import Langlands.Representation.Classification.FineRelativeHomLowerBoundStatement
import Langlands.Representation.Classification.FineOppositeJacquetHomFinitenessProof
import Langlands.Representation.Classification.RelativeCosocleAdmissibilityProof
import Langlands.Representation.Parabolic.FineAmbientHomMapInjectivityProof
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Parabolic.FlattenedOppositeJacquetComparisonProof

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity RelativeHomComparison

universe uG uH uA uB uC uF uV uW uZ

section Algebra

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  {A : Type uA} {B : Type uB} {C : Type uC}
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]

-- These transport constructions follow the published detection proof of
-- Workers 845, 526 and 435, whose original assembly transport is Worker 435's.
private def homPostcompEquiv (ρ : Representation ℂ G A)
    {σ : Representation ℂ G B} {τ : Representation ℂ G C} (e : σ.Equiv τ) :
    (ρ.IntertwiningMap σ) ≃ₗ[ℂ] (ρ.IntertwiningMap τ) where
  toFun f := e.toIntertwiningMap.comp f
  invFun f := e.symm.toIntertwiningMap.comp f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv f := by ext x; exact e.symm_apply_apply (f x)
  right_inv f := by ext x; exact e.apply_symm_apply (f x)

private def homChangeGroup (e : G ≃* H) (ρ : Representation ℂ G A)
    (σ : Representation ℂ H B) :
    (ρ.IntertwiningMap (σ.comp e.toMonoidHom)) ≃ₗ[ℂ]
      Representation.IntertwiningMap (ρ.comp e.symm.toMonoidHom) σ where
  toFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' h := by
        simpa using f.isIntertwining' (e.symm h) }
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' g := by
        simpa using f.isIntertwining' (e g) }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

end Algebra

/-- The actual relative Hom spaces are finite dimensional, and the inner
dimension is bounded by the outer dimension. -/
theorem fineRelativeHomLowerBound :
    FineRelativeHomLowerBoundStatement.{uF, uV, uW, uZ} := by
  intro p _ F T
  let := T.topology
  intro n hn B S ω hωirr hωcusp v₀ π hπirr hπadm t J hJnontriv hJquot
  obtain ⟨q, hq⟩ := hJquot
  have hJadm : IsAdmissible J.ρ :=
    ((relativeCosocleAdmissibility p F T n B π).2.2 hπadm t).2.2 J q hq
  have hfiniteOut :=
    (fineOppositeJacquetHomFinite.{uF, uV, uW, uZ}
      p F T n B S ω hωirr hωcusp v₀ t).2 J hJadm
  have hfiniteIn :=
    (fineOppositeJacquetHomFinite.{uF, uV, uW, uZ}
      p F T n B S ω hωirr hωcusp v₀ 0).1 π hπadm
  have hreg0 := fineTwistIrreducibleAdmissible p F T n B S ω hωirr hωcusp v₀ 0
  have hregt := fineTwistIrreducibleAdmissible p F T n B S ω hωirr hωcusp v₀ t
  obtain ⟨Ein, -⟩ :=
    (Parabolic.normalizedSecondAdjointness.{uF, uV, uW}).2 p F T n hn B S
  obtain ⟨Eout, -⟩ :=
    (Parabolic.normalizedSecondAdjointness.{uF, uV, uZ}).1 p F T n hn (B.flatten S)
  obtain ⟨φ, -⟩ :=
    Parabolic.flattenedOppositeJacquetComparison.{uF, uF, uZ}.2 p F T n B S J
  let α := Rep.of (T.leviRealPowerTwist (B.flatten S)
    (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ)
  let e := flattenedLeviEquiv F.Carrier B S
  let Etransport := (homPostcompEquiv α.ρ φ.symm).trans
    (homChangeGroup e α.ρ (T.normalizedComposedOppositeJacquet B S J.ρ))
  let Eambient := (Eout α J hregt.2.2.1 hJadm).trans Etransport
  let Einner := Ein (fineTwist T B S ω v₀ 0) π hreg0.2.1 hπadm
  let C := fineAmbientHomMap T B S ω v₀ t hωcusp.1.1 π J q
  have hC : Function.Injective C :=
    fineAmbientHomMapInjective p F T n B S ω v₀ t hωcusp.1.1
      π hπirr J hJnontriv q hq
  let L := Eambient.toLinearMap.comp (C.comp Einner.symm.toLinearMap)
  have hL : Function.Injective L :=
    Eambient.injective.comp (hC.comp Einner.symm.injective)
  let := hfiniteOut
  let := hfiniteIn
  exact ⟨hfiniteOut, hfiniteIn, LinearMap.finrank_le_finrank_of_injective hL⟩

end Langlands
