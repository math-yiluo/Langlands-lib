import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionFiniteProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartFiniteProducts
import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionPointComparison

/-!
# Finite-product Weil restriction on field-valued points

The full-test finite-product comparison is a limiting fan whenever its
members are algebraic spaces. The etale-chart product theorem and the local
Weil point theorem then give the canonical product homeomorphism.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

namespace WeilRestrictionFiniteProduct

variable (A : Type u) [CommRing A]
  {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
  [∀ i, Algebra A (B i)]
  (X : AlgebraicSpace (Spec (CommRingCat.of (∀ i, B i))))

/-- The original projection from the dependent product presheaf. -/
def productProjection (i : ι) :
    productPresheaf A B X ⟶
      ((ringWeilRestriction A (B i)).obj (factorSpace B X i).toSheaf).obj where
  app _ := ↾fun x => x i
  naturality _ _ _ := rfl

/-- The explicitly defined dependent product presheaf has its ordinary
full-presheaf product universal property. -/
def productFanIsLimit :
    IsLimit (Fan.mk (productPresheaf A B X) (productProjection A B X)) where
  lift s :=
    { app T := ↾fun x i => (s.π.app ⟨i⟩).app T x
      naturality _ _ a := by
        ext x
        funext i
        exact ConcreteCategory.congr_hom ((s.π.app ⟨i⟩).naturality a) x }
  fac s j := by
    obtain ⟨i⟩ := j
    ext T x
    rfl
  uniq s m hm := by
    ext T x
    funext i
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (hm ⟨i⟩) T) x

variable
  (h : IsAlgebraicSpace _ ((ringWeilRestriction A (∀ i, B i)).obj X.toSheaf))
  (hf : ∀ i, IsAlgebraicSpace _
    ((ringWeilRestriction A (B i)).obj (factorSpace B X i).toSheaf))

/-- The represented factor restriction, with its supplied algebraicity
witness. -/
abbrev factorWeilSpace (i : ι) : AlgebraicSpace (Spec (CommRingCat.of A)) :=
  ringWeilRestrictionSpace A (B i) (factorSpace B X i) (hf i)

/-- The actual projection morphism from the restriction along the product
algebra to the factor restriction. -/
def spaceProjection (i : ι) :
    ringWeilRestrictionSpace A (∀ i, B i) X h ⟶ factorWeilSpace A B X hf i :=
  homMk ((ringWeilRestrictionFiniteProductPresheafIso A B X).hom ≫
    productProjection A B X i)

/-- The represented Weil restrictions form a full-presheaf product cone;
this is derived from the finite-product comparison, not an additional
universal-property assumption. -/
def spaceFanIsLimit :
    IsLimit (Fan.mk (ringWeilRestrictionSpace A (∀ i, B i) X h).presheaf
      (fun i => hom (spaceProjection A B X h hf i))) :=
  IsLimit.ofIsoLimit (productFanIsLimit A B X)
    (Fan.ext (ringWeilRestrictionFiniteProductPresheafIso A B X)
      (by intro i; rfl)).symm

end WeilRestrictionFiniteProduct

open WeilRestrictionFiniteProduct

variable (K : Type u) [NontriviallyNormedField K]
  {ι : Type u} [Finite ι] (L : ι → Type u)
  [∀ i, NontriviallyNormedField (L i)] [∀ i, Algebra K (L i)] [∀ i, ContinuousSMul K (L i)]
  [∀ i, FiniteDimensional K (L i)] [∀ i, IsModuleTopology K (L i)]
  (X : AlgebraicSpace (Spec (CommRingCat.of (∀ i, L i))))
  (h : IsAlgebraicSpace _ ((ringWeilRestriction K (∀ i, L i)).obj X.toSheaf))
  (hf : ∀ i, IsAlgebraicSpace _
    ((ringWeilRestriction K (L i)).obj (factorSpace L X i).toSheaf))

/-- The canonical finite-product local Weil comparison for actual
algebraic spaces, with representability and geometry explicit. -/
def finiteProductWeilRestrictionPointHomeomorph
    (hK : IsHenselianValuedField K) (hL : ∀ i, IsHenselianValuedField (L i))
    (hX : ∀ i, IsQuasiSeparatedLocallyFiniteType (L i) (factorSpace L X i))
    (hW : IsQuasiSeparatedLocallyFiniteType K
      (ringWeilRestrictionSpace K (∀ i, L i) X h))
    (hWf : ∀ i, IsQuasiSeparatedLocallyFiniteType K (factorWeilSpace K L X hf i)) :
    letI : TopologicalSpace
        (RingPoints K (ringWeilRestrictionSpace K (∀ i, L i) X h) K) :=
      etaleChartTopology K (ringWeilRestrictionSpace K (∀ i, L i) X h)
    letI : ∀ i, TopologicalSpace (RingPoints (L i) (factorSpace L X i) (L i)) :=
      fun i => etaleChartTopology (L i) (factorSpace L X i)
    RingPoints K (ringWeilRestrictionSpace K (∀ i, L i) X h) K ≃ₜ
      (∀ i, RingPoints (L i) (factorSpace L X i) (L i)) := by
  let : TopologicalSpace
      (RingPoints K (ringWeilRestrictionSpace K (∀ i, L i) X h) K) :=
    etaleChartTopology K (ringWeilRestrictionSpace K (∀ i, L i) X h)
  let (i : ι) : TopologicalSpace (RingPoints K (factorWeilSpace K L X hf i) K) :=
    etaleChartTopology K (factorWeilSpace K L X hf i)
  let (i : ι) : TopologicalSpace (RingPoints (L i) (factorSpace L X i) (L i)) :=
    etaleChartTopology (L i) (factorSpace L X i)
  exact (finiteProductSpacePointHomeomorph (factorWeilSpace K L X hf)
    (spaceProjection K L X h hf) (spaceFanIsLimit K L X h hf) hK hW hWf).trans
      (Homeomorph.piCongrRight fun i =>
        ringWeilRestrictionPointHomeomorph K (L i) (factorSpace L X i)
          hK (hL i) (hX i) (hf i) (hWf i))

/-- Each component is the original factor restriction projection followed
by the canonical local Weil rational-point equivalence. -/
@[simp]
theorem finiteProductWeilRestrictionPointHomeomorph_apply
    (hK : IsHenselianValuedField K) (hL : ∀ i, IsHenselianValuedField (L i))
    (hX : ∀ i, IsQuasiSeparatedLocallyFiniteType (L i) (factorSpace L X i))
    (hW : IsQuasiSeparatedLocallyFiniteType K
      (ringWeilRestrictionSpace K (∀ i, L i) X h))
    (hWf : ∀ i, IsQuasiSeparatedLocallyFiniteType K (factorWeilSpace K L X hf i))
    (x : RingPoints K (ringWeilRestrictionSpace K (∀ i, L i) X h) K) (i : ι) :
    finiteProductWeilRestrictionPointHomeomorph K L X h hf hK hL hX hW hWf x i =
      ringWeilRestrictionBasePointsEquiv K (L i) (factorSpace L X i) (hf i)
        (RingPoints.map (spaceProjection K L X h hf i) x) := by
  change ringWeilRestrictionBasePointsEquiv K (L i) (factorSpace L X i) (hf i)
      (finiteProductSpacePointHomeomorph (factorWeilSpace K L X hf)
        (spaceProjection K L X h hf) (spaceFanIsLimit K L X h hf) hK hW hWf x i) = _
  rw [finiteProductSpacePointHomeomorph_apply]

end Langlands.AlgebraicGeometry.AlgebraicSpace
