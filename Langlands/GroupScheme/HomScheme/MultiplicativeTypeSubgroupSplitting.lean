import Langlands.GroupScheme.HomScheme.DiagonalizableHopfPoint
import Langlands.GroupScheme.HomScheme.TorusSubgroupSplitting
import Langlands.GroupScheme.Torus.MultiplicativeTypeAffineSplitting

/-! # Finite affine fppf splitting of actual multiplicative-type subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme.DiagonalizableSplitting

open FiniteSource
open TorusSplitting (ChartRing chartHom)

variable {R : Type u} [CommRing R] {T : Over (Spec (CommRingCat.of R))}
variable (G : GroupScheme (Spec (CommRingCat.of R))) {L : GroupScheme T.left}
  (i : L ⟶ (GroupScheme.baseChange T.hom).obj G)

/-- An actual split inclusion expressed with the fixed diagonalizable model over `Spec R`. -/
def chartRelHom (A : CommRingCat.{u}) (g : Spec A ⟶ T.left) (Λ : Type u) [AddCommGroup Λ]
    (e : (GroupScheme.baseChange g).obj L ≅ RelativeMultiplicativeType.diagonalizable (Spec A) Λ) :
    RelativeHom (RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of R)) Λ) G
      (specOver R (ChartRing A g)) :=
  (RelativeMultiplicativeType.diagonalizableBaseChangeIso
      (specOver R (ChartRing A g)).hom Λ ≪≫ e.symm).hom ≫
    TorusSubgroupModuli.familyHom i (chartHom A g)

/-- The diagonalizable expression retains the actual closed inclusion. -/
theorem isClosedSubgroup_chartRelHom (hi : IsClosedSubgroup i) (A : CommRingCat.{u})
    (g : Spec A ⟶ T.left) (Λ : Type u) [AddCommGroup Λ]
    (e : (GroupScheme.baseChange g).obj L ≅ RelativeMultiplicativeType.diagonalizable (Spec A) Λ) :
    IsClosedSubgroup (chartRelHom G i A g Λ e) :=
  IsClosedSubgroup.iso_comp _ (TorusSubgroupModuli.isClosedSubgroup_familyHom i hi _)

/-- Reexpressing a split subgroup does not change its all-test range. -/
theorem evaluate_chartHom (A : CommRingCat.{u}) (g : Spec A ⟶ T.left)
    (Λ : Type u) [AddCommGroup Λ]
    (e : (GroupScheme.baseChange g).obj L ≅ RelativeMultiplicativeType.diagonalizable (Spec A) Λ) :
    TorusSubgroupModuli.evaluate i (chartHom A g) =
      SubgroupFunctor.range (chartRelHom G i A g Λ e) :=
  (SubgroupFunctor.range_iso_comp _ _).symm

end Langlands.GroupScheme.HomScheme.DiagonalizableSplitting

namespace Langlands.GroupScheme.HomScheme

open Langlands.FiniteBialgebraHom FiniteSource DiagonalizablePoint
open TorusSplitting (ChartRing chartHom)

/-- Actual closed multiplicative-type subgroups over an affine test scheme split
on finitely many affine fppf charts, with surjective Hopf coordinates and exact ranges. -/
theorem exists_fppf_diagPoints {R : Type u} [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] {L : GroupScheme T.left}
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G) (hi : IsClosedSubgroup i)
    (hL : RelativeMultiplicativeType.IsMultiplicativeType L) :
    ∃ (n : ℕ) (C : Fin n → Type u) (_ : ∀ k, CommRing (C k)) (_ : ∀ k, Algebra R (C k))
      (b : ∀ k, specOver R (C k) ⟶ T) (Λ : Fin n → Type u)
      (_ : ∀ k, AddCommGroup (Λ k)) (_ : ∀ k, AddGroup.FG (Λ k))
      (f : ∀ k, {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C k ⊗[R] AddMonoidAlgebra R (Λ k) //
        IsHopfPoint R f}),
      (∀ k, Flat (b k).left) ∧ (∀ k, LocallyOfFinitePresentation (b k).left) ∧
      (∀ t : T.left, ∃ k, t ∈ Set.range (b k).left.base) ∧
      (∀ k, Function.Surjective (AlgHom.liftEquiv R (C k) _ _ (f k).1)) ∧
      ∀ k, TorusSubgroupModuli.evaluate i (b k) =
        SubgroupFunctor.range ((diagPointEquiv G (C k)).symm (f k)) := by
  classical
  let d := RelativeMultiplicativeType.affineSplittingCover L hL
  choose Λ hΛ hFG e using d.diagonalizable
  let : ∀ k, AddCommGroup (Λ k) := hΛ
  let : ∀ k, AddGroup.FG (Λ k) := hFG
  refine ⟨d.count, fun k => ChartRing (d.ring k) (d.map k), fun k => inferInstance,
    fun k => inferInstance, fun k => chartHom (d.ring k) (d.map k), Λ,
    fun k => inferInstance, fun k => inferInstance,
    fun k => diagPointEquiv G _
      (DiagonalizableSplitting.chartRelHom G i (d.ring k) (d.map k) (Λ k) (e k).some),
    fun k => ?_, fun k => ?_, ?_, fun k => ?_, fun k => ?_⟩
  · exact d.flat k
  · exact d.locallyOfFinitePresentation k
  · exact d.covers
  · rw [← isClosedSubgroup_diagPointEquiv_symm_iff, Equiv.symm_apply_apply]
    exact DiagonalizableSplitting.isClosedSubgroup_chartRelHom G i hi _ _ _ _
  · rw [Equiv.symm_apply_apply]
    exact DiagonalizableSplitting.evaluate_chartHom G i _ _ _ _

end Langlands.GroupScheme.HomScheme
