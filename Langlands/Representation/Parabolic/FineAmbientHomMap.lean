import Langlands.Representation.Parabolic.RefinedLeviRealTwistProof
import Langlands.Representation.Parabolic.OrderedRefinementInduction
import Langlands.Representation.Parabolic.ComposedFlattenedInductionProof
import Langlands.Representation.Classification.RelativeRecoveryStatement

/-! # The fine-to-ambient Hom map attached to a specified outer intertwiner

For a specified intertwiner `q` out of the outer induction of the coarse twist
`T.leviRealPowerTwist B t π.ρ`, this module defines the actual `ℂ`-linear map
from inner intertwiners at fine parameter `v₀` and coarse parameter `0` to
intertwiners out of the fine ambient induction. It is defined on all
intertwiners; no surjectivity, injectivity or dimension claim is made.
-/

noncomputable section

namespace Langlands.RelativeHomComparison

open GeneralLinear Geometric RelativeJacquetMultiplicity Parabolic

universe uF uV uW uZ uA uB

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n)

section Induced

variable {V : Type uA} {W : Type uB} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- Normalized parabolic induction of actual Levi intertwiners, as a
`ℂ`-linear map on spaces of intertwiners. -/
def inducedMapLinear (σ : Representation ℂ (B.Levi F.Carrier) V)
    (τ : Representation ℂ (B.Levi F.Carrier) W) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    σ.IntertwiningMap τ →ₗ[ℂ]
      (T.normalizedParabolicInduced B σ).IntertwiningMap
        (T.normalizedParabolicInduced B τ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  { toFun := fun f => T.normalizedParabolicInducedMap B f
    map_add' := fun f g => by
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      apply Subtype.ext
      funext x
      rfl
    map_smul' := fun c f => by
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      apply Subtype.ext
      funext x
      rfl }

@[simp]
theorem inducedMapLinear_apply (σ : Representation ℂ (B.Levi F.Carrier) V)
    (τ : Representation ℂ (B.Levi F.Carrier) W) (f : σ.IntertwiningMap τ) :
    inducedMapLinear T B σ τ f = T.normalizedParabolicInducedMap B f := rfl

end Induced

variable (S : BlockRefinement B)

/-- The coarse real determinant character `m ↦ ∏ᵢ |det mᵢ|^{tᵢ}` of the coarse
Levi, as a smooth character. -/
def coarseCharacter (t : Fin B.length → ℝ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (B.Levi F.Carrier) :=
  letI := T.topology
  ⟨T.leviRealPowerCharacter B t, T.isOpen_ker_leviRealPowerCharacter B t⟩

variable (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
  (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ)

/-- Twisting the refined inducing data of the coarse parameter `0` by the
restricted coarse character gives the refined inducing data of parameter `t`. -/
theorem inducingData_twist :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    twist ((coarseCharacter T B t).toMonoidHom.comp
        (refinedParabolic F.Carrier B S).subtype)
      (twist (T.refinedParabolicHalfModulus B S)
        ((fineTwist T B S ω v₀ 0).ρ.comp (refinedLeviProjection F.Carrier B S))) =
    twist (T.refinedParabolicHalfModulus B S)
      ((fineTwist T B S ω v₀ t).ρ.comp (refinedLeviProjection F.Carrier B S)) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  ext q x
  let m := (flattenedLeviEquiv F.Carrier B S).symm
    (refinedLeviProjection F.Carrier B S q)
  have hc :
      T.leviRealPowerCharacter (B.flatten S)
          (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) m =
        T.leviRealPowerCharacter B t q.val *
          T.leviRealPowerCharacter (B.flatten S) (fun k => -v₀ k) m := by
    rw [(refinedLeviRealTwist.{uF, uV, 0} p F T n B S ω v₀ t).1 q]
    rw [← MonoidHom.mul_apply, ← T.leviRealPowerCharacter_add]
    congr 2
    funext k
    exact add_comm _ _
  change (T.leviRealPowerCharacter B t q.val : ℂ) •
      ((T.refinedParabolicHalfModulus B S q : ℂ) •
        ((T.leviRealPowerCharacter (B.flatten S)
          (fun k => -v₀ k + (0 : Fin B.length → ℝ)
            ((B.flattenBlockEquiv S).symm k).1) m : ℂ) • ω.ρ m x)) =
    (T.refinedParabolicHalfModulus B S q : ℂ) •
      ((T.leviRealPowerCharacter (B.flatten S)
        (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) m : ℂ) • ω.ρ m x)
  simp only [Pi.zero_apply, add_zero, hc, Units.val_mul, mul_smul]
  exact smul_comm _ _ _

/-- The fixed equivalence `E₀` from the coarse twist of the inner induction at
coarse parameter `0` to the inner induction at coarse parameter `t`: multiply
each induced function by the coarse character, then identify the twisted
inducing data with those at `t`. It depends only on the inducing data. -/
def coarseTwistEquiv :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    (T.leviRealPowerTwist B t (innerInduced T B S (fineTwist T B S ω v₀ 0)).ρ).Equiv
      (innerInduced T B S (fineTwist T B S ω v₀ t)).ρ :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  (Induction.smoothInductionTwistEquiv (refinedParabolic F.Carrier B S)
      (coarseCharacter T B t) _).trans
    (Induction.smoothInducedEquiv (refinedParabolic F.Carrier B S)
      (equivOfRepresentationEq (inducingData_twist T B S ω v₀ t)))

/-- `E₀` multiplies the value at `m` by the coarse character. -/
theorem coarseTwistEquiv_eval :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ f (m : B.Levi F.Carrier),
      Induction.eval _ _ (coarseTwistEquiv T B S ω v₀ t f) m =
        (T.leviRealPowerCharacter B t m : ℂ) • Induction.eval _ _ f m :=
  fun _ _ => rfl

/-- The inverse of `E₀` multiplies the value at `m` by the inverse character. -/
theorem coarseTwistEquiv_symm_eval :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ f (m : B.Levi F.Carrier),
      Induction.eval _ _ ((coarseTwistEquiv T B S ω v₀ t).symm f) m =
        ((T.leviRealPowerCharacter B t m)⁻¹ : ℂˣ) • Induction.eval _ _ f m :=
  fun _ _ => rfl

/-- The linear map `f ↦ fₜ`: twist an arbitrary inner intertwiner by the common
coarse character and precompose with `E₀⁻¹`. -/
def coarseTwistHom (π : Rep.{uW} ℂ (B.Levi F.Carrier)) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    (innerInduced T B S (fineTwist T B S ω v₀ 0)).ρ.IntertwiningMap π.ρ →ₗ[ℂ]
      (innerInduced T B S (fineTwist T B S ω v₀ t)).ρ.IntertwiningMap
        (T.leviRealPowerTwist B t π.ρ) :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  { toFun := fun f => (twistIntertwining (T.leviRealPowerCharacter B t) f).comp
      (coarseTwistEquiv T B S ω v₀ t).symm.toIntertwiningMap
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem coarseTwistHom_apply (π : Rep.{uW} ℂ (B.Levi F.Carrier)) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ f, coarseTwistHom T B S ω v₀ t π f =
      (twistIntertwining (T.leviRealPowerCharacter B t) f).comp
        (coarseTwistEquiv T B S ω v₀ t).symm.toIntertwiningMap :=
  fun _ => rfl

set_option maxHeartbeats 800000 in
/-- The fixed equivalence `E_flat` from the outer induction of the inner
induction at `t` to the fine ambient induction: the ordered stages equivalence
at the canonical flattened coordinates, with its Levi coordinate map rewritten
to the published flattened Levi equivalence. -/
def flatStagesEquiv
    (hω : letI := T.topology; IsSmooth ω.ρ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (CuspidalJacquetMultiplicity.induced T B
        (innerInduced T B S (fineTwist T B S ω v₀ t))).ρ.Equiv
      (RelativeRecovery.fineAmbientInduced T B S ω v₀ t).ρ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup B
  have E := orderedRefinementInductionEquiv F T (B.flatten S) B S (B.flattenBlockEquiv S)
    (fun a => (B.flatten_size_flattenBlockEquiv S a).symm)
    (fun i k x => B.index_index_eq_flatten S ⟨i, k⟩ x)
    (T.leviRealPowerTwist (B.flatten S)
      (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ)
    ((T.isSmooth_leviRealPowerTwist_iff (B.flatten S) _ ω.ρ).mpr hω)
  dsimp only [orderedRefinementIteratedInduced] at E
  rw [B.leviRefinementEquiv_flatten F.Carrier S] at E
  exact E

/-- The actual `ℂ`-linear fine-to-ambient Hom map attached to a specified outer
intertwiner `q`: `f ↦ q ∘ i_P(fₜ) ∘ E_flat⁻¹`, defined for every inner
intertwiner `f`. -/
def fineAmbientHomMap
    (hω : letI := T.topology; IsSmooth ω.ρ)
    (π : Rep.{uW} ℂ (B.Levi F.Carrier)) (J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier))
    (q : (CuspidalJacquetMultiplicity.induced T B
      (Rep.of (T.leviRealPowerTwist B t π.ρ))).ρ.IntertwiningMap J.ρ) :
    (innerInduced T B S (fineTwist T B S ω v₀ 0)).ρ.IntertwiningMap π.ρ →ₗ[ℂ]
      (RelativeRecovery.fineAmbientInduced T B S ω v₀ t).ρ.IntertwiningMap J.ρ :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup B
  Representation.IntertwiningMap.llcomp _ _ _ q ∘ₗ
    (Representation.IntertwiningMap.llcomp _ _ _).flip
      (flatStagesEquiv T B S ω v₀ t hω).symm.toIntertwiningMap ∘ₗ
    inducedMapLinear T B _ _ ∘ₗ coarseTwistHom T B S ω v₀ t π

/-- The implemented formula `C_q(f) = q ∘ i_P(fₜ) ∘ E_flat⁻¹`. -/
theorem fineAmbientHomMap_apply
    (hω : letI := T.topology; IsSmooth ω.ρ)
    (π : Rep.{uW} ℂ (B.Levi F.Carrier)) (J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier))
    (q : (CuspidalJacquetMultiplicity.induced T B
      (Rep.of (T.leviRealPowerTwist B t π.ρ))).ρ.IntertwiningMap J.ρ)
    (f : (innerInduced T B S (fineTwist T B S ω v₀ 0)).ρ.IntertwiningMap π.ρ) :
    fineAmbientHomMap T B S ω v₀ t hω π J q f =
      q.comp ((T.normalizedParabolicInducedMap B (coarseTwistHom T B S ω v₀ t π f)).comp
        (flatStagesEquiv T B S ω v₀ t hω).symm.toIntertwiningMap) :=
  rfl

end Langlands.RelativeHomComparison
