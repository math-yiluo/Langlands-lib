import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeFinitePresentationStatement
import Langlands.AlgebraicGeometry.Picard.DualSchemeQuotientFactorization
import Langlands.AlgebraicGeometry.Picard.DualSchemeBaseChange
import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBaseChangeProof

/-! # Proof: local finite presentation of the chosen dual parameter scheme

Local finite presentation is local on the target. Over each member `Spec R` of an affine open
cover of the base, the base change of the chosen dual is isomorphic over `Spec R` to the chosen
dual of the base-changed abelian scheme, which is locally of finite presentation by
`dualScheme_locallyOfFinitePresentation_affine`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The chosen dual parameter scheme of an abelian scheme is locally of finite presentation over
the base. -/
theorem relativeDualSchemeFinitePresentation :
    RelativeDualSchemeFinitePresentationStatement.{u} := by
  intro S _ A hA
  let 𝒰 := S.affineOpenCover
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  refine IsZariskiLocalAtTarget.of_openCover 𝒰.openCover (fun i ↦ ?_)
  let b : Spec (𝒰.X i) ⟶ S := 𝒰.f i
  let hA₁ := hasDualScheme_baseChange picardZeroUniversalBaseChange b A hA
  have h₁ : LocallyOfFinitePresentation (dualScheme ((baseChange b).obj A) hA₁).hom :=
    dualScheme_locallyOfFinitePresentation_affine (R := 𝒰.X i) _ hA₁
  let e := dualSchemeBaseChangeIso picardZeroUniversalBaseChange b A hA hA₁
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso e).hom)
  have h₂ : e.hom.left ≫ (dualScheme ((baseChange b).obj A) hA₁).hom =
      pullback.snd (dualScheme A hA).hom b := Over.w e.hom
  change LocallyOfFinitePresentation (pullback.snd (dualScheme A hA).hom b)
  rw [← h₂]
  infer_instance

end Langlands.AbelianScheme
