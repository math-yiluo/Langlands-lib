import Langlands.GroupScheme.UnipotentAffineOrbitClosedStatement
import Langlands.GroupScheme.KostantRosenlicht.Geometry
import Langlands.GroupScheme.KostantRosenlicht.Surjective
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Proof of the Kostant–Rosenlicht closed-orbit theorem -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme

open AffineLinearEmbedding KostantRosenlicht

/-- The coordinate algebra of an affine scheme locally of finite type over `R` is of finite
type. -/
theorem KostantRosenlicht.finiteType_of_iso {R : CommRingCat.{u}} {Y : Over (Spec R)}
    [LocallyOfFiniteType Y.hom] {A : CommAlgCat.{u} R} (jY : (algSpec R).obj (op A) ≅ Y) :
    Algebra.FiniteType R A := by
  have h : LocallyOfFiniteType ((algSpec R).obj (op A)).hom := by
    have : IsIso jY.hom.left := inferInstanceAs (IsIso ((Over.forget _).map jY.hom))
    rw [← Over.w jY.hom]
    exact MorphismProperty.comp_mem _ _ _ inferInstance ‹_›
  exact RingHom.finiteType_algebraMap.mp
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType).mp h)

/-- Milne, *Algebraic Groups* (2017), Theorem 17.64, over an algebraically closed field:
the orbit of a rational point under an action of a smooth affine unipotent group on an
affine scheme of finite type is closed. -/
theorem unipotentAffineOrbitClosed : UnipotentAffineOrbitClosedStatement.{u} := by
  intro k _ _ U _ _ hU X _ _ a x
  obtain ⟨⟨B⟩, ⟨j⟩⟩ := (essImage_algSpec (G := U.X)).mpr (isAffine_of_isAffineHom U.X.hom)
  obtain ⟨⟨A⟩, ⟨jX⟩⟩ := (essImage_algSpec (G := X)).mpr ‹IsAffine X.left›
  have : Algebra.FiniteType (CommRingCat.of k) B := finiteType_of_iso j
  have : Algebra.FiniteType (CommRingCat.of k) A := finiteType_of_iso jX
  have : _root_.IsReduced B := by
    have := Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k
      U.X.left U.X.hom
    have : IsIso j.hom.left := inferInstanceAs (IsIso ((Over.forget _).map j.hom))
    have := isReduced_of_isOpenImmersion j.hom.left
    exact (affine_isReduced_iff (CommRingCat.of B)).mp this
  have : IsIso (modelIso U j).inv.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (modelIso U j).inv.hom.hom))
  have hmodel : IsUnipotent (model U j) := hU.of_epi (modelIso U j).inv
  apply isClosed_range_orbit j a jX x
  rw [range_comap_eq_zeroLocus (corepresentableBy U j) hmodel (coordMap j a jX x).hom
    fun v b => ⟨(leftTranslate a jX (basePoint j v)).hom b, by
      have := congrArg (fun f => CommAlgCat.Hom.hom f b) (coordMap_comp_rightTranslate j a jX x v)
      exact this⟩]
  exact PrimeSpectrum.isClosed_zeroLocus _

end Langlands.GroupScheme
