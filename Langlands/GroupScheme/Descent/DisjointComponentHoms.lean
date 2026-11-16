import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Pi.Monoidal

/-! # Homomorphisms over arbitrary disjoint scheme decompositions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.Descent.DisjointComponents

variable {I : Type u} {S : Scheme.{u}} {Z : I → Scheme.{u}}
variable (p : ∀ i, Z i ⟶ S) [IsIso (Sigma.desc p)]

/-- The actual restrictions to all components. -/
abbrev restriction : Over S ⥤ ∀ i, Over (Z i) :=
  Functor.pi' (fun i => Over.pullback (p i))

/-- The component pullbacks cover each scheme over the decomposed base. -/
def projection (X : Over S) :
    (∐ fun i => pullback X.hom (p i)) ⟶ X.left :=
  Sigma.desc (fun i => pullback.fst X.hom (p i))

instance component_openImmersion (i : I) : IsOpenImmersion (p i) := by
  rw [← Sigma.ι_comp_desc p i]
  infer_instance

/-- The component images cover the base of the decomposition. -/
theorem component_covers (x : S) : ∃ i, ∃ y : Z i, p i y = x := by
  obtain ⟨⟨i, y⟩, hy⟩ := (AlgebraicGeometry.sigmaMk Z).surjective (inv (Sigma.desc p) x)
  refine ⟨i, y, ?_⟩
  have h := congrArg (fun z => Sigma.desc p z) hy
  simpa [← Scheme.Hom.comp_apply] using h

/-- Distinct components have disjoint images. -/
theorem component_disjoint {i j : I} (hij : i ≠ j) :
    Disjoint (Set.range (p i)) (Set.range (p j)) := by
  refine Set.disjoint_iff_forall_ne.mpr ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
  have he : Sigma.ι Z i x = Sigma.ι Z j y := by
    apply (Sigma.desc p).isOpenEmbedding.injective
    simpa only [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc] using h
  exact hij (congrArg Sigma.fst ((AlgebraicGeometry.sigmaι_eq_iff Z i j x y).mp he))

/-- Base change preserves an arbitrary small scheme coproduct decomposition. -/
instance projection_isIso (X : Over S) : IsIso (projection p X) := by
  have hcol : Nonempty (IsColimit (Cofan.mk X.left
      (fun i => pullback.fst X.hom (p i)))) := by
    apply AlgebraicGeometry.nonempty_isColimit_cofanMk_of
    · apply top_unique
      intro x _
      obtain ⟨i, y, hy⟩ := component_covers p (X.hom x)
      have hx : x ∈ (pullback.fst X.hom (p i)).opensRange := by
        rw [Scheme.Hom.opensRange_pullbackFst]
        exact ⟨y, hy⟩
      exact (le_iSup (fun i => (pullback.fst X.hom (p i)).opensRange) i) hx
    · intro i j hij
      change Disjoint _ _
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro x hx
      have hi : X.hom x ∈ Set.range (p i) := by
        simpa [Scheme.Hom.opensRange_pullbackFst] using hx.1
      have hj : X.hom x ∈ Set.range (p j) := by
        simpa [Scheme.Hom.opensRange_pullbackFst] using hx.2
      exact Set.disjoint_left.mp (component_disjoint p hij) hi hj
  exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp hcol

/-- Assemble actual underlying maps along the coproduct decomposition. -/
def schemeHom {X Y : Over S}
    (a : ∀ i, (Over.pullback (p i)).obj X ⟶ (Over.pullback (p i)).obj Y) :
    X.left ⟶ Y.left :=
  inv (projection p X) ≫
    Sigma.desc (fun i => (a i).left ≫ pullback.fst Y.hom (p i))

@[reassoc]
theorem schemeHom_fac {X Y : Over S}
    (a : ∀ i, (Over.pullback (p i)).obj X ⟶ (Over.pullback (p i)).obj Y) (i : I) :
    pullback.fst X.hom (p i) ≫ schemeHom p a =
      (a i).left ≫ pullback.fst Y.hom (p i) := by
  calc
    _ = Sigma.ι (fun j => pullback X.hom (p j)) i ≫ projection p X ≫
        schemeHom p a := by rw [projection, Sigma.ι_comp_desc_assoc]
    _ = _ := by simp [schemeHom]

/-- The assembled map retains its given base. -/
def overHom {X Y : Over S}
    (a : ∀ i, (Over.pullback (p i)).obj X ⟶ (Over.pullback (p i)).obj Y) : X ⟶ Y :=
  Over.homMk (schemeHom p a) (by
    apply (cancel_epi (projection p X)).mp
    apply Sigma.hom_ext
    intro i
    simp only [projection, Sigma.ι_comp_desc_assoc]
    rw [schemeHom_fac_assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (fun f => f ≫ p i) (Over.w (a i))).trans
      (pullback.condition (f := X.hom) (g := p i)).symm)

@[simp]
theorem map_overHom {X Y : Over S}
    (a : ∀ i, (Over.pullback (p i)).obj X ⟶ (Over.pullback (p i)).obj Y) (i : I) :
    (Over.pullback (p i)).map (overHom p a) = a i := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Over.pullback_map_left, pullback.lift_fst, overHom, Over.homMk_left]
      using schemeHom_fac p a i
  · simpa only [Over.pullback_map_left, pullback.lift_snd, Over.pullback_obj_hom]
      using (Over.w (a i)).symm

/-- Component restrictions detect equality of actual maps over the base. -/
theorem overHom_ext {X Y : Over S} {a b : X ⟶ Y}
    (h : ∀ i, (Over.pullback (p i)).map a = (Over.pullback (p i)).map b) : a = b := by
  apply Over.OverMorphism.ext
  apply (cancel_epi (projection p X)).mp
  apply Sigma.hom_ext
  intro i
  have hi := congrArg (fun f => f.left ≫ pullback.fst Y.hom (p i)) (h i)
  simpa [projection, Over.pullback_map_left, pullback.lift_fst] using hi

/-- Restricting schemes to the components is fully faithful. -/
def restrictionFullyFaithful : (restriction p).FullyFaithful where
  preimage a := overHom p a
  map_preimage a := funext (map_overHom p a)
  preimage_map _a := overHom_ext p (fun i => map_overHom p _ i)

open MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

/-- The pointwise tensor on the component categories is their categorical product. -/
local instance pointwiseCartesianMonoidalCategory : CartesianMonoidalCategory (∀ i, Over (Z i)) where
  toMonoidalCategory := Pi.monoidalCategory
  isTerminalTensorUnit := .ofUniqueHom (fun X i => toUnit (X i)) (by
    intro X m
    funext i
    exact toUnit_unique _ _)
  fst X Y i := fst (X i) (Y i)
  snd X Y i := snd (X i) (Y i)
  fst_def X Y := by
    funext i
    exact fst_def (X i) (Y i)
  snd_def X Y := by
    funext i
    exact snd_def (X i) (Y i)
  tensorProductIsBinaryProduct X Y :=
    BinaryFan.IsLimit.mk _
      (fun f g i => lift (f i) (g i))
      (fun f g => funext (fun i => lift_fst (f i) (g i)))
      (fun f g => funext (fun i => lift_snd (f i) (g i)))
      (fun f g m hf hg => funext (fun i =>
        hom_ext _ _ (by simpa using congrFun hf i) (by simpa using congrFun hg i)))

set_option backward.isDefEq.respectTransparency false in
/-- A component family of group homomorphisms is a homomorphism of pointwise group objects. -/
def componentGroupHom {G H : GroupScheme S}
    (a : ∀ i, (baseChange (p i)).obj G ⟶ (baseChange (p i)).obj H) :
    (restriction p).mapGrp.obj G ⟶ (restriction p).mapGrp.obj H :=
  Grp.homMk'' (fun i => (a i).hom.hom)
    (by funext i; exact IsMonHom.one_hom (a i).hom.hom)
    (by funext i; exact IsMonHom.mul_hom (a i).hom.hom)

/-- Assemble actual group-scheme homomorphisms from their component restrictions. -/
def groupHom {G H : GroupScheme S}
    (a : ∀ i, (baseChange (p i)).obj G ⟶ (baseChange (p i)).obj H) : G ⟶ H :=
  (restrictionFullyFaithful p).mapGrp.preimage (componentGroupHom p a)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem map_groupHom {G H : GroupScheme S}
    (a : ∀ i, (baseChange (p i)).obj G ⟶ (baseChange (p i)).obj H) (i : I) :
    (baseChange (p i)).map (groupHom p a) = a i := by
  apply Grp.hom_ext
  exact congrArg (fun f => f.hom.hom i)
    ((restrictionFullyFaithful p).mapGrp.map_preimage (componentGroupHom p a))

/-- Component restrictions detect equality of actual group-scheme homomorphisms. -/
theorem groupHom_ext {G H : GroupScheme S} {a b : G ⟶ H}
    (h : ∀ i, (baseChange (p i)).map a = (baseChange (p i)).map b) : a = b := by
  apply Grp.hom_ext
  exact overHom_ext p (fun i => congrArg (fun f => f.hom.hom) (h i))

/-- Actual group-scheme restriction to the components. -/
abbrev groupRestriction : GroupScheme S ⥤ ∀ i, GroupScheme (Z i) :=
  Functor.pi' (fun i => baseChange (p i))

/-- Group-scheme homomorphisms are exactly families of component homomorphisms. -/
def groupRestrictionFullyFaithful : (groupRestriction p).FullyFaithful where
  preimage a := groupHom p a
  map_preimage a := funext (map_groupHom p a)
  preimage_map _a := groupHom_ext p (fun i => map_groupHom p _ i)

/-- Assemble actual group-scheme isomorphisms from component isomorphisms. -/
def groupIso {G H : GroupScheme S}
    (a : ∀ i, (baseChange (p i)).obj G ≅ (baseChange (p i)).obj H) : G ≅ H where
  hom := groupHom p (fun i => (a i).hom)
  inv := groupHom p (fun i => (a i).inv)
  hom_inv_id := groupHom_ext p (fun i => by simp)
  inv_hom_id := groupHom_ext p (fun i => by simp)

@[simp]
theorem map_groupIso {G H : GroupScheme S}
    (a : ∀ i, (baseChange (p i)).obj G ≅ (baseChange (p i)).obj H) (i : I) :
    (baseChange (p i)).mapIso (groupIso p a) = a i := by
  apply Iso.ext
  exact map_groupHom p (fun j => (a j).hom) i

end Langlands.GroupScheme.Descent.DisjointComponents
