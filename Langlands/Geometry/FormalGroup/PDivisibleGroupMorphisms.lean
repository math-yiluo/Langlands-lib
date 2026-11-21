import Langlands.Geometry.FormalGroup.PDivisibleGroupSchemeTower
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # Morphisms of actual p-divisible groups -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.PDivisibleGroup

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]

/-- The inclusion at any pair of levels is injective on every affine test. -/
theorem inclusion_affine_injective (G : PDivisibleGroup R p) {m n : ℕ} (i : m ⟶ n)
    (A : CommAlgCat.{u} R) :
    Function.Injective (fun x : CommGroupScheme.affineTest A ⟶ (G.inclusions.obj m).X =>
      x ≫ (G.inclusions.map i).toMul.hom.hom) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (leOfHom i)
  have he : i = homOfLE (Nat.le_add_left m k) := Subsingleton.elim _ _
  rw [he]
  exact (G.shortExact k m).1 A

/-- A map of inclusion diagrams commutes with the transfers. Scalar
factorization gives equality after the target inclusion, which is injective
on affine points. The finite source level is affine. -/
theorem naturalTransformation_transferCompatible {G H : PDivisibleGroup R p}
    (f : G.inclusions ⟶ H.inclusions) {m n : ℕ} (i : m ⟶ n) :
    G.transfer i ≫ f.app m = f.app n ≫ H.transfer i := by
  let a := G.transfer i ≫ f.app m
  let b := f.app n ≫ H.transfer i
  let j := H.inclusions.map i
  have hab : a ≫ j = b ≫ j := by
    calc
      a ≫ j = (G.transfer i ≫ G.inclusions.map i) ≫ f.app n := by
        change (G.transfer i ≫ f.app m) ≫ j = _
        rw [Category.assoc, ← f.naturality i, ← Category.assoc]
      _ = p ^ (n - m) • f.app n := by rw [G.multiplication]; simp
      _ = b ≫ j := by
        change _ = (f.app n ≫ H.transfer i) ≫ H.inclusions.map i
        rw [Category.assoc, H.multiplication]
        simp
  have : IsFinite (G.inclusions.obj n).X.hom := (G.finiteLocallyFree n).1
  have : IsAffine (G.inclusions.obj n).X.left :=
    GroupScheme.Cartier.FiniteDual.isAffine_of_isFinite (G.inclusions.obj n).toGrp
  obtain ⟨C, _, _, ⟨e⟩⟩ := GroupScheme.Cartier.FiniteDual.exists_iso_algSpec (G.inclusions.obj n).X
  change Additive.ofMul a.toMul = Additive.ofMul b.toMul
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  apply (cancel_epi e.inv).mp
  apply H.inclusion_affine_injective i (CommAlgCat.of R C)
  have he := congrArg (fun c : G.inclusions.obj n ⟶ H.inclusions.obj n =>
    e.inv ≫ c.toMul.hom.hom) hab
  change e.inv ≫ a.toMul.hom.hom ≫ j.toMul.hom.hom =
    e.inv ≫ b.toMul.hom.hom ≫ j.toMul.hom.hom at he
  simpa only [Category.assoc] using he

/-- The subgroup of natural transformations of the inclusion diagrams compatible
with all transfers. -/
def transferCompatible (G H : PDivisibleGroup R p) : AddSubgroup (G.inclusions ⟶ H.inclusions) where
  carrier := { f | ∀ {m n : ℕ} (i : m ⟶ n),
    G.transfer i ≫ f.app m = f.app n ≫ H.transfer i }
  zero_mem' := by
    intro m n i
    simp
  add_mem' := by
    intro f g hf hg m n i
    change G.transfer i ≫ (f.app m + g.app m) = (f.app n + g.app n) ≫ H.transfer i
    rw [Preadditive.comp_add, Preadditive.add_comp, hf i, hg i]
  neg_mem' := by
    intro f hf m n i
    change G.transfer i ≫ (-f.app m) = (-f.app n) ≫ H.transfer i
    rw [Preadditive.comp_neg, Preadditive.neg_comp, hf i]

/-- A morphism acts by a homomorphism of the actual group schemes at each level,
compatible with the two tower arrows. -/
abbrev Hom (G H : PDivisibleGroup R p) := ↥(transferCompatible G H)

namespace Hom

variable {G H J : PDivisibleGroup R p}

/-- The actual group scheme morphism at the specified finite level. -/
def app (f : Hom G H) (n : ℕ) : G.inclusions.obj n ⟶ H.inclusions.obj n := f.val.app n

@[reassoc]
theorem naturality (f : Hom G H) {m n : ℕ} (i : m ⟶ n) :
    G.inclusions.map i ≫ f.app n = f.app m ≫ H.inclusions.map i := f.val.naturality i

@[reassoc]
theorem transfer_naturality (f : Hom G H) {m n : ℕ} (i : m ⟶ n) :
    G.transfer i ≫ f.app m = f.app n ≫ H.transfer i := f.property i

/-- Build a tower morphism from actual level maps and their two naturality laws. -/
def ofComponents (f : ∀ n : ℕ, G.inclusions.obj n ⟶ H.inclusions.obj n)
    (hf : ∀ {m n : ℕ} (i : m ⟶ n), G.inclusions.map i ≫ f n = f m ≫ H.inclusions.map i)
    (hf' : ∀ {m n : ℕ} (i : m ⟶ n), G.transfer i ≫ f m = f n ≫ H.transfer i) : Hom G H :=
  ⟨{ app := f, naturality _ _ i := hf i }, hf'⟩

/-- A natural transformation of the actual inclusion diagrams gives a tower morphism. -/
def ofNaturalTransformation (f : G.inclusions ⟶ H.inclusions) : Hom G H :=
  ⟨f, fun i => naturalTransformation_transferCompatible f i⟩

@[simp] theorem ofComponents_app {f hf hf'} (n : ℕ) :
    (ofComponents (G := G) (H := H) f hf hf').app n = f n := rfl

@[ext] theorem ext {f g : Hom G H} (h : ∀ n, f.app n = g.app n) : f = g :=
  Subtype.ext (NatTrans.ext (funext h))

private def id (G : PDivisibleGroup R p) : Hom G G :=
  ⟨𝟙 G.inclusions, fun _ => (Category.comp_id _).trans (Category.id_comp _).symm⟩

private def comp (f : Hom G H) (g : Hom H J) : Hom G J :=
  ⟨f.val ≫ g.val, fun {m n} i => by
    change G.transfer i ≫ (f.app m ≫ g.app m) = (f.app n ≫ g.app n) ≫ J.transfer i
    rw [← Category.assoc, f.transfer_naturality i, Category.assoc, g.transfer_naturality i, Category.assoc]⟩

@[simp] theorem zero_app (n : ℕ) : (0 : Hom G H).app n = 0 := rfl

@[simp] theorem add_app (f g : Hom G H) (n : ℕ) : (f + g).app n = f.app n + g.app n := rfl

@[simp] theorem neg_app (f : Hom G H) (n : ℕ) : (-f).app n = -f.app n := rfl

end Hom

/-- Composition and the identity are the ordinary compositions and identities at every level. -/
instance : Category (PDivisibleGroup R p) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

/-- Addition of tower morphisms is addition of the actual homomorphisms on each level. -/
instance : Preadditive (PDivisibleGroup R p) where
  homGroup G H := inferInstanceAs (AddCommGroup (Hom G H))
  add_comp _ _ _ f g h := Subtype.ext (Preadditive.add_comp _ _ _ f.val g.val h.val)
  comp_add _ _ _ f g h := Subtype.ext (Preadditive.comp_add _ _ _ f.val g.val h.val)

@[simp] theorem Hom.id_app (G : PDivisibleGroup R p) (n : ℕ) : (𝟙 G : G ⟶ G).app n = 𝟙 _ := rfl

@[simp] theorem Hom.comp_app {G H J : PDivisibleGroup R p} (f : G ⟶ H) (g : H ⟶ J) (n : ℕ) :
    (f ≫ g).app n = f.app n ≫ g.app n := rfl

/-- The actual inclusion diagram and its morphism on every level. -/
def inclusionDiagramFunctor (R : CommRingCat.{u}) (p : ℕ) [Fact p.Prime] :
    PDivisibleGroup R p ⥤ (ℕ ⥤ CommGroupScheme (Spec R)) where
  obj G := G.inclusions
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

instance (R : CommRingCat.{u}) (p : ℕ) [Fact p.Prime] : (inclusionDiagramFunctor R p).Faithful where
  map_injective := Subtype.ext

instance (R : CommRingCat.{u}) (p : ℕ) [Fact p.Prime] : (inclusionDiagramFunctor R p).Full where
  map_surjective f := ⟨Hom.ofNaturalTransformation f, rfl⟩

instance (R : CommRingCat.{u}) (p : ℕ) [Fact p.Prime] : (inclusionDiagramFunctor R p).Additive where
  map_add := rfl

end Langlands.PDivisibleGroup
