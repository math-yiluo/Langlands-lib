import Langlands.GroupScheme.Torus.DiagonalizableIsoLift

/-! # Comparison isomorphisms between diagonalizable charts and their free lifts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

open Descent FreeCharacterCover

/-! ### Pulling back conjugates by iterated base-change comparisons -/

section Bridge

variable {B S V W : Scheme.{u}}

@[reassoc] private theorem baseChange_map_fst' {T S : Scheme.{u}} (p : T ⟶ S)
    {G H : GroupScheme S} (i : H ⟶ G) :
    ((GroupScheme.baseChange p).map i).hom.hom.left ≫ pullback.fst G.X.hom p =
      pullback.fst H.X.hom p ≫ i.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- Canonical direct-pullback comparisons agree around a three-step tower. -/
theorem pullbackComparison_tower' {T U : Scheme.{u}} {G : GroupScheme S}
    (p : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S) (h : q ≫ p = r)
    (c : V ⟶ U) (b : V ⟶ T) (a : V ⟶ S)
    (hcb : c ≫ q = b) (hba : b ≫ p = a) (hca : c ≫ r = a) :
    (GroupScheme.baseChange c).map (pullbackComparison p q r h G).hom ≫
        (pullbackComparison r c a hca G).hom =
      (pullbackComparison q c b hcb ((GroupScheme.baseChange p).obj G)).hom ≫
        (pullbackComparison p b a hba G).hom := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      pullbackComparison_hom_fst, baseChange_map_fst'_assoc,
      pullbackComparison_hom_fst_assoc]
  · exact (Over.w _).trans (Over.w _).symm

/-- The inverse form of `pullbackComparison_tower'`. -/
theorem pullbackComparison_tower_inv {T U : Scheme.{u}} {G : GroupScheme S}
    (p : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S) (h : q ≫ p = r)
    (c : V ⟶ U) (b : V ⟶ T) (a : V ⟶ S)
    (hcb : c ≫ q = b) (hba : b ≫ p = a) (hca : c ≫ r = a) :
    (pullbackComparison r c a hca G).inv ≫
        (GroupScheme.baseChange c).map (pullbackComparison p q r h G).inv =
      (pullbackComparison p b a hba G).inv ≫
        (pullbackComparison q c b hcb ((GroupScheme.baseChange p).obj G)).inv := by
  have h' := congrArg Iso.inv (Iso.ext (pullbackComparison_tower' p q r h c b a hcb hba hca) :
    (GroupScheme.baseChange c).mapIso (pullbackComparison p q r h G) ≪≫
        pullbackComparison r c a hca G =
      pullbackComparison q c b hcb ((GroupScheme.baseChange p).obj G) ≪≫
        pullbackComparison p b a hba G)
  simpa only [Iso.trans_inv, Functor.mapIso_inv] using h'

/-- Pulling back a morphism conjugated by iterated base-change comparisons. -/
theorem pullHom_conj_pullbackComparison (t : S ⟶ B) {a b : V ⟶ S} {ta tb : V ⟶ B}
    (ha : a ≫ t = ta) (hb : b ≫ t = tb) (q : W ⟶ V) {a' b' : W ⟶ S}
    (hqa : q ≫ a = a') (hqb : q ≫ b = b') {ta' tb' : W ⟶ B}
    (hta : q ≫ ta = ta') (htb : q ≫ tb = tb') {K K' : GroupScheme B}
    (φ : (GroupScheme.baseChange a).obj ((GroupScheme.baseChange t).obj K) ⟶
      (GroupScheme.baseChange b).obj ((GroupScheme.baseChange t).obj K')) :
    pullHom q hta htb ((pullbackComparison t a ta ha K).inv ≫ φ ≫
        (pullbackComparison t b tb hb K').hom) =
      (pullbackComparison t a' ta' (by rw [← hqa, ← hta, ← ha, Category.assoc]) K).inv ≫
        pullHom q hqa hqb φ ≫
          (pullbackComparison t b' tb' (by rw [← hqb, ← htb, ← hb, Category.assoc]) K').hom := by
  have h1 := pullbackComparison_tower_inv t a ta ha q a' ta' hqa
    (by rw [← hqa, ← hta, ← ha, Category.assoc]) hta (G := K)
  have h2 := pullbackComparison_tower' t b tb hb q b' tb' hqb
    (by rw [← hqb, ← htb, ← hb, Category.assoc]) htb (G := K')
  unfold pullHom
  simp only [Functor.map_comp, Category.assoc]
  rw [h2, reassoc_of% h1]

/-- The conjugation by `diagonalizableBaseChangeIso` turns pullbacks over `S` into pullbacks of
homomorphisms of diagonalizable groups. -/
theorem dpull_conj {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ'] {a b : V ⟶ S}
    (q : W ⟶ V) {a' b' : W ⟶ S} (hqa : q ≫ a = a') (hqb : q ≫ b = b')
    (φ : (GroupScheme.baseChange a).obj (diagonalizable S Λ) ⟶
      (GroupScheme.baseChange b).obj (diagonalizable S Λ')) :
    dpull q ((diagonalizableBaseChangeIso a Λ).inv ≫ φ ≫
        (diagonalizableBaseChangeIso b Λ').hom) =
      (diagonalizableBaseChangeIso a' Λ).inv ≫ pullHom q hqa hqb φ ≫
        (diagonalizableBaseChangeIso b' Λ').hom :=
  pullHom_conj_pullbackComparison (Gm.toSpecZ S) (toSpecZ_comp a) (toSpecZ_comp b) q hqa hqb
    (toSpecZ_comp q) (toSpecZ_comp q) φ

/-- Pulling back the inverse of an isomorphism. -/
theorem pullHom_inv {T S : Scheme.{u}} (q : W ⟶ T) {f g : T ⟶ S} {r s : W ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s) {G H : GroupScheme S}
    (e : (GroupScheme.baseChange f).obj G ≅ (GroupScheme.baseChange g).obj H) :
    pullHom q hg hf e.inv = (pullIso q hf hg e).inv :=
  rfl

end Bridge

/-! ### Diagonalizable atlases -/

/-- A family of maps `f i : Z i ⟶ S` together with isomorphisms
`(f i)^* H ≅ D_{Z i}(Λ i)` for finitely generated abelian groups `Λ i`. -/
structure DiagonalizableAtlas {S : Scheme.{u}} (H : GroupScheme S) where
  /-- The index type of the charts. -/
  I : Type u
  /-- The chart schemes. -/
  Z : I → Scheme.{u}
  /-- The chart maps. -/
  f : ∀ i, Z i ⟶ S
  /-- The character groups. -/
  Λ : I → Type u
  [addCommGroup : ∀ i, AddCommGroup (Λ i)]
  [fg : ∀ i, AddGroup.FG (Λ i)]
  /-- The trivializations of `H` over the charts. -/
  e : ∀ i, (GroupScheme.baseChange (f i)).obj H ≅ diagonalizable (Z i) (Λ i)

attribute [instance] DiagonalizableAtlas.addCommGroup DiagonalizableAtlas.fg

namespace DiagonalizableAtlas

variable {S V W : Scheme.{u}} {H : GroupScheme S} (A : DiagonalizableAtlas H)

/-- The trivialization over the chart, written as an isomorphism of base changes of groups
over `S`. -/
def triv (i : A.I) :
    (GroupScheme.baseChange (A.f i)).obj H ≅
      (GroupScheme.baseChange (A.f i)).obj (diagonalizable S (A.Λ i)) :=
  A.e i ≪≫ (diagonalizableBaseChangeIso (A.f i) (A.Λ i)).symm

/-- The trivialization of `l^* H` given by a chart coordinate `x` of `l`. -/
def chartTriv (i : A.I) (x : V ⟶ A.Z i) (l : V ⟶ S) (hx : x ≫ A.f i = l) :
    (GroupScheme.baseChange l).obj H ≅ diagonalizable V (A.Λ i) :=
  pullIso x hx hx (A.triv i) ≪≫ diagonalizableBaseChangeIso l (A.Λ i)

/-- The comparison `D_V(Λ i) ≅ D_V(Λ j)` between two chart coordinates over the same point of
`S`. -/
def comparison (i j : A.I) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) (l : V ⟶ S)
    (hx : x ≫ A.f i = l) (hy : y ≫ A.f j = l) :
    diagonalizable V (A.Λ i) ≅ diagonalizable V (A.Λ j) :=
  (A.chartTriv i x l hx).symm ≪≫ A.chartTriv j y l hy

@[simp] theorem comparison_self (i : A.I) (x : V ⟶ A.Z i) (l : V ⟶ S) (hx : x ≫ A.f i = l) :
    A.comparison i i x x l hx hx = Iso.refl _ := by
  simp [comparison]

theorem comparison_trans (i j k : A.I) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) (z : V ⟶ A.Z k)
    (l : V ⟶ S) (hx : x ≫ A.f i = l) (hy : y ≫ A.f j = l) (hz : z ≫ A.f k = l) :
    A.comparison i j x y l hx hy ≪≫ A.comparison j k y z l hy hz =
      A.comparison i k x z l hx hz := by
  simp [comparison]

theorem comparison_hom_eq (i j : A.I) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) (l : V ⟶ S)
    (hx : x ≫ A.f i = l) (hy : y ≫ A.f j = l) :
    (A.comparison i j x y l hx hy).hom =
      (diagonalizableBaseChangeIso l (A.Λ i)).inv ≫
        ((pullIso x hx hx (A.triv i)).inv ≫ (pullIso y hy hy (A.triv j)).hom) ≫
          (diagonalizableBaseChangeIso l (A.Λ j)).hom := by
  simp [comparison, chartTriv]

/-- Comparisons commute with pullback. -/
theorem dpullIso_comparison (i j : A.I) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) (l : V ⟶ S)
    (hx : x ≫ A.f i = l) (hy : y ≫ A.f j = l) (q : W ⟶ V) :
    dpullIso q (A.comparison i j x y l hx hy) =
      A.comparison i j (q ≫ x) (q ≫ y) (q ≫ l) (by rw [Category.assoc, hx])
        (by rw [Category.assoc, hy]) := by
  apply Iso.ext
  rw [dpullIso_hom, comparison_hom_eq, comparison_hom_eq, dpull_conj q rfl rfl,
    pullHom_comp q rfl rfl rfl, pullHom_inv, ← pullIso_hom, pullIso_pullIso, pullIso_pullIso]

/-- The lift of a comparison to the free character covers. -/
def lift (i j : A.I) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) (l : V ⟶ S)
    (hx : x ≫ A.f i = l) (hy : y ≫ A.f j = l) :
    diagonalizable V (Cover (A.Λ i)) ≅ diagonalizable V (Cover (A.Λ j)) :=
  liftIso (A.comparison i j x y l hx hy)

@[simp] theorem lift_self (i : A.I) (x : V ⟶ A.Z i) (l : V ⟶ S) (hx : x ≫ A.f i = l) :
    A.lift i i x x l hx hx = Iso.refl _ := by
  rw [lift, comparison_self, liftIso_refl]

theorem lift_trans (i j k : A.I) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) (z : V ⟶ A.Z k)
    (l : V ⟶ S) (hx : x ≫ A.f i = l) (hy : y ≫ A.f j = l) (hz : z ≫ A.f k = l) :
    A.lift i j x y l hx hy ≪≫ A.lift j k y z l hy hz = A.lift i k x z l hx hz := by
  rw [lift, lift, lift, ← liftIso_trans, comparison_trans]

theorem dpullIso_lift (i j : A.I) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) (l : V ⟶ S)
    (hx : x ≫ A.f i = l) (hy : y ≫ A.f j = l) (q : W ⟶ V) :
    dpullIso q (A.lift i j x y l hx hy) =
      A.lift i j (q ≫ x) (q ≫ y) (q ≫ l) (by rw [Category.assoc, hx])
        (by rw [Category.assoc, hy]) := by
  rw [lift, lift, ← liftIso_dpullIso, dpullIso_comparison]

theorem lift_comm (i j : A.I) (x : V ⟶ A.Z i) (y : V ⟶ A.Z j) (l : V ⟶ S)
    (hx : x ≫ A.f i = l) (hy : y ≫ A.f j = l) :
    (A.comparison i j x y l hx hy).hom ≫ diagonalizableMap V (proj (A.Λ j)) =
      diagonalizableMap V (proj (A.Λ i)) ≫ (A.lift i j x y l hx hy).hom :=
  liftIso_comm _

end DiagonalizableAtlas

end Langlands.GroupScheme.RelativeMultiplicativeType
