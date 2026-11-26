import Langlands.Global.AdelicEisensteinAmbientShiftStatement
import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.Global.AdelicEisensteinContinuationReduction
import Langlands.Global.AdelicEisensteinRegularParameterStatement

/-! # The ambient character shift of Eisenstein series

* `eisensteinSeriesAmbientShift`: the defining sum satisfies
  `E(φ, λ + p*ν)(g) = g^ν E(φ, λ)(g)` (`EisensteinSeriesAmbientShiftStatement`);
* `eisensteinContinuationAmbientShift_of_regularParameter`: if every regular-parameter region is
  nonempty (`EisensteinRegularParameterStatement`), a supplied meromorphic continuation satisfies
  the same identity on its holomorphy domain for ambient shifts of real part zero
  (`EisensteinContinuationAmbientShiftStatement`);
* `eisensteinAmbientShift_of_regularParameter`: the conjunction `EisensteinAmbientShiftStatement`
  under the same hypothesis. -/

noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj TensorProduct Manifold

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Langlands.Analysis.Meromorphic

section Sum

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

private theorem log_eq_dualMap_height (g : AdelicGroupPoints F G) :
    characterLog F G g = realCharacterDualMap F P G p (hK.height g) := by
  obtain ⟨q, k, hk, hq⟩ := hK.exists_eq g
  rw [hK.height_eq hk hq, ← hq, characterLog_mul, characterLog_map,
    characterLog_eq_zero_on_compactSubgroup F G K hK.isCompact hk, add_zero]

private theorem heightPower_add_ambient (lam : ComplexCharacterParameter F P)
    (ν : ComplexCharacterParameter F G) (g : AdelicGroupPoints F G) :
    hK.heightPower (lam + parameterRestrict p ν) g =
      hK.heightPower lam g * parameterPower F G ν g := by
  simp only [IsIwasawaCompact.heightPower, map_add, LinearMap.add_apply,
    complexParameterPairing_parameterRestrict, ← log_eq_dualMap_height hK, Complex.exp_add, parameterPower]

omit [IsAffine G.X.left] in
private theorem parameterPower_principal_mul (ν : ComplexCharacterParameter F G)
    (rpoint : rationalSubgroup F G) (g : AdelicGroupPoints F G) :
    parameterPower F G ν ((rpoint : AdelicGroupPoints F G) * g) = parameterPower F G ν g := by
  obtain ⟨x, hx⟩ := rpoint.property
  simp only [parameterPower, characterLog_mul, ← hx, characterLog_rational, zero_add]

/-- Shifting the defining sum by an ambient parameter multiplies the sum by the ambient
adelic character, in the stated normalization. -/
theorem eisensteinSeriesAmbientShift : EisensteinSeriesAmbientShiftStatement.{u} := by
  intro F _ _ G P _ _ p _ K hK phi lam ν g
  have hterm (c : ParabolicRationalCosets F p) :
      hK.eisensteinTerm phi (lam + parameterRestrict p ν) g c =
        parameterPower F G ν g * hK.eisensteinTerm phi lam g c := by
    unfold IsIwasawaCompact.eisensteinTerm IsIwasawaCompact.parameterTwist
    rw [heightPower_add_ambient hK, parameterPower_principal_mul]
    ac_rfl
  unfold IsIwasawaCompact.eisensteinSeries
  rw [tsum_congr hterm, tsum_mul_left]

end Sum

section Analytic

/-- The weak manifold formulation yields precisely the flat scalar local denominators. -/
private theorem scalar_localDenominators {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {D : Set (Fin n → ℂ)} (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D) :
    HasLocalDenominators f D univ := by
  intro s _
  obtain ⟨W, hWo, hWc, hs, a, b, ha, ha0, hb, heq⟩ := hf.2.2.2 s
  exact ⟨W, hWo, hWc.isPreconnected, hs, a, b, mdifferentiableOn_iff_differentiableOn.mp ha,
    ha0, differentiableOn_of_isHolomorphicOn hb, fun x hx => by simpa only [smul_eq_mul] using heq x hx⟩

private theorem eq_translate_of_eqOn_open {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {D O : Set (Fin n → ℂ)} (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D)
    (d : Fin n → ℂ) (c : ℂ) (hO : IsOpen O) (hOne : O.Nonempty)
    (heq : ∀ s ∈ O, s ∈ D → s + d ∈ D → f (s + d) = c * f s) :
    ∀ s ∈ D, s + d ∈ D → f (s + d) = c * f s := by
  let T : (Fin n → ℂ) ≃ₜ (Fin n → ℂ) := Homeomorph.addRight d
  have hdT : Differentiable ℂ T := (differentiable_id : Differentiable ℂ (id : (Fin n → ℂ) → _)).add_const d
  have hfD := (differentiableOn_of_isHolomorphicOn hf.2.2.1).continuousOn
  have h1 : HasLocalDenominators (f ∘ T) (T ⁻¹' D) univ := by
    intro s _
    obtain ⟨W, hWo, hWc, hs, a, b, ha, ⟨x, hx, hx0⟩, hb, hab⟩ :=
      scalar_localDenominators hf (T s) (mem_univ _)
    refine ⟨T ⁻¹' W, hWo.preimage T.continuous, ?_, hs, a ∘ T, b ∘ T,
      ha.comp hdT.differentiableOn (mapsTo_preimage _ _), ⟨T.symm x, by simpa, by simpa⟩,
      hb.comp hdT.differentiableOn (mapsTo_preimage _ _), fun y hy => hab (T y) hy⟩
    have hset : T.symm '' W = T ⁻¹' W := T.toEquiv.image_symm_eq_preimage W
    rw [← hset]
    exact hWc.image _ T.symm.continuous.continuousOn
  have h2 : HasLocalDenominators (fun s => c * f s) D univ := by
    intro s _
    obtain ⟨W, hWo, hWc, hs, a, b, ha, ha0, hb, hab⟩ := scalar_localDenominators hf s (mem_univ _)
    exact ⟨W, hWo, hWc, hs, a, fun x => c * b x, ha, ha0, hb.const_mul c, fun x hx => by
      rw [mul_left_comm, hab x hx]⟩
  obtain ⟨s₀, hs₀⟩ := hOne
  have aux := eq_of_hasLocalDenominators (Ω := (univ : Set (Fin n → ℂ)))
    isOpen_univ isPreconnected_univ (hf.1.preimage T.continuous) hf.1
    (fun s _ => (hf.2.1.preimage T.isOpenMap) s) (fun s _ => hf.2.1 s)
    (hfD.comp T.continuous.continuousOn (mapsTo_preimage _ _)) (hfD.const_mul c)
    h1 h2 (mem_univ s₀) (Filter.eventually_of_mem (hO.mem_nhds hs₀)
      fun s hs ht hD => heq s hs hD ht)
  exact fun s hs hsd => aux s (mem_univ _) hsd hs

end Analytic

/-- Uniqueness carries the defining-sum identity to the supplied continuation on the common
holomorphy domain, once every regular-parameter region is nonempty. -/
theorem eisensteinContinuationAmbientShift_of_regularParameter
    (hR : EisensteinRegularParameterStatement.{u}) :
    EisensteinContinuationAmbientShiftStatement.{u} := by
  intro F _ _ G P M A _ _ _ p _ l a r _ _ _ hA hT hG K hK phi g E D hE hagree ν hν lam hlam hshift
  obtain ⟨R, hagree⟩ := hagree
  let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := hE.1
  let e := (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  let d := e.symm (parameterRestrict p ν)
  have hcoord (s : Fin (Module.finrank ℂ (ComplexCharacterParameter F P)) → ℂ) :
      e (s + d) = e s + parameterRestrict p ν := by
    rw [map_add, show e d = parameterRestrict p ν from e.apply_symm_apply _]
  let O := {s | r.IsRegularParameter hA hT R (e s)}
  have hO : IsOpen O := isOpen_setOf_isRegularParameter r hA hT hG R e
  obtain ⟨v, hv⟩ := hR F G P M A p l a r hA hT hG R
  have hOne : O.Nonempty := ⟨e.symm v, by simpa [O] using hv⟩
  have hreg (x : ComplexCharacterParameter F P) (hx : r.IsRegularParameter hA hT R x) :
      r.IsRegularParameter hA hT R (x + parameterRestrict p ν) := by
    intro α hα
    rw [map_add, parameterRealPart_pullback, hν, map_zero, add_zero]
    exact hx α hα
  have key := eq_translate_of_eqOn_open (hE.2 _ e) d (parameterPower F G ν g) hO hOne
    (fun s (hs : r.IsRegularParameter hA hT R (e s)) (hD : e s ∈ D) (hDs : e (s + d) ∈ D) => by
      rw [hcoord] at hDs
      simp only [Function.comp_apply, hcoord]
      rw [hagree _ hDs (hreg _ hs), hagree _ hD hs]
      exact eisensteinSeriesAmbientShift F G P p K hK phi (e s) ν g)
  have hs : e (e.symm lam) ∈ D := by simpa using hlam
  have hsd : e (e.symm lam + d) ∈ D := by simpa only [hcoord, LinearEquiv.apply_symm_apply] using hshift
  simpa only [Function.comp_apply, hcoord, LinearEquiv.apply_symm_apply] using key (e.symm lam) hs hsd

/-- Both the defining and common-domain meromorphic identities, once every regular-parameter
region is nonempty. -/
theorem eisensteinAmbientShift_of_regularParameter
    (hR : EisensteinRegularParameterStatement.{u}) : EisensteinAmbientShiftStatement.{u} :=
  ⟨eisensteinSeriesAmbientShift, eisensteinContinuationAmbientShift_of_regularParameter hR⟩

end Langlands.Global
