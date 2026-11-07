import Langlands.Representation.Plancherel.ContinuedIntertwiningScalarBaseChange
import Langlands.Representation.Plancherel.UnramifiedScalarOrbit

/-! # Orbit scalars from original self-base-change squares -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open UnramifiedOperatorFamily

universe u uG uI uV uW

namespace UnramifiedOperatorFamily

variable {H : Type uG} [Group H] [TopologicalSpace H]
  {I : Type uI} {ν : I → (H →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Original comparison squares for one translated parameter chart and the
same two operator families. The two nonempty open regions are independent. -/
structure SelfBaseChangeData
    (Ω Λ : Set (unramifiedCharacters ν))
    (A : Ω → V →ₗ[ℂ] W) (B : Λ → W →ₗ[ℂ] V)
    (τ : unramifiedCharacters ν) where
  source : V ≃ₗ[ℂ] V
  target : W ≃ₗ[ℂ] W
  forwardRegion : Set (unramifiedCharacters ν)
  reverseRegion : Set (unramifiedCharacters ν)
  forward_isOpen : IsOpen forwardRegion
  forward_nonempty : forwardRegion.Nonempty
  forward_in_translation : forwardRegion ⊆ (unramifiedParameterTranslation ν τ) ⁻¹' Ω
  forward_in_original : forwardRegion ⊆ Ω
  reverse_isOpen : IsOpen reverseRegion
  reverse_nonempty : reverseRegion.Nonempty
  reverse_in_translation : reverseRegion ⊆ (unramifiedParameterTranslation ν τ) ⁻¹' Λ
  reverse_in_original : reverseRegion ⊆ Λ
  forward_natural : ∀ χ (hχ : χ ∈ forwardRegion),
    (A ⟨χ, forward_in_original hχ⟩).comp source.toLinearMap =
      target.toLinearMap.comp (A ⟨τ * χ, forward_in_translation hχ⟩)
  reverse_natural : ∀ χ (hχ : χ ∈ reverseRegion),
    (B ⟨χ, reverse_in_original hχ⟩).comp target.toLinearMap =
      source.toLinearMap.comp (B ⟨τ * χ, reverse_in_translation hχ⟩)

end UnramifiedOperatorFamily

section ActualScalar

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω Λ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}
  (p : RationalOperatorContinuationData Ω A)
  (q : RationalOperatorContinuationData Λ B)
  (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty)

/-- Generic scalarity and original self-comparison squares imply fixedness
of the extracted fraction under the indicated character translation. -/
theorem continuedCompositeRationalScalar_fixed_of_selfBaseChange
    (τ : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))
    (d : SelfBaseChangeData Ω Λ A B τ)
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hU : IsOpen U) (hneU : U.Nonempty)
    (hscalar : ∀ χ : ↥(p.regularRegion ∩ q.regularRegion), χ.val ∈ U →
      ∃ c : ℂ, p.continuedComposite q χ = c • LinearMap.id)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    rationalUnramifiedFunctionFieldTranslation L hp hL τ
        (continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ) =
      continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ := by
  exact (continuedCompositeRationalScalar_base_independent L hp hL
    p q τ p q d.source d.target
    d.forward_isOpen d.forward_nonempty d.forward_in_translation d.forward_in_original
    d.reverse_isOpen d.reverse_nonempty d.reverse_in_translation d.reverse_in_original
    d.forward_natural d.reverse_natural hU hneU hscalar v ℓ hℓ v ℓ hℓ).symm

/-- Self-comparison witnesses for every subgroup element prove subgroup
fixedness; the scalar fixedness is a conclusion, not an input. -/
theorem continuedCompositeRationalScalar_subgroup_fixed
    (S : Subgroup (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul)))
    (hd : ∀ τ : S, Nonempty (SelfBaseChangeData Ω Λ A B τ.val))
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hU : IsOpen U) (hneU : U.Nonempty)
    (hscalar : ∀ χ : ↥(p.regularRegion ∩ q.regularRegion), χ.val ∈ U →
      ∃ c : ℂ, p.continuedComposite q χ = c • LinearMap.id)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    ∀ τ : S, rationalUnramifiedFunctionFieldTranslation L hp hL τ.val
      (continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ) =
        continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ := by
  intro τ
  obtain ⟨d⟩ := hd τ
  exact continuedCompositeRationalScalar_fixed_of_selfBaseChange L hp hL
    p q hΩ hΛ τ.val d hU hneU hscalar v ℓ hℓ

/-- Construct an invariant presentation of the extracted composite scalar
for the actual twist orbit, from original self-comparison witnesses. -/
def continuedCompositeOrbitScalarPresentation
    [NonarchimedeanGroup (GroupScheme.rationalPoints L)]
    (π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints L))
    [Finite (smoothRepUnramifiedTwistStabilizer
      (fun ψ => (rationalNormCharacters L ψ).toMul) π)]
    (hd : ∀ τ : smoothRepUnramifiedTwistStabilizer
      (fun ψ => (rationalNormCharacters L ψ).toMul) π,
      Nonempty (SelfBaseChangeData Ω Λ A B τ.val))
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hU : IsOpen U) (hneU : U.Nonempty)
    (hscalar : ∀ χ : ↥(p.regularRegion ∩ q.regularRegion), χ.val ∈ U →
      ∃ c : ℂ, p.continuedComposite q χ = c • LinearMap.id)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer
        (fun ψ => (rationalNormCharacters L ψ).toMul) π)
      (continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ) :=
  Classical.choice (unramifiedTwistOrbitScalarPresentation_exists L hp hL π _
    (continuedCompositeRationalScalar_subgroup_fixed L hp hL p q hΩ hΛ _ hd
      hU hneU hscalar v ℓ hℓ))

end ActualScalar

section ValueComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  [NonarchimedeanGroup (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  (π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints L))

namespace UnramifiedInvariantScalarPresentation

/-- A presentation of the same fraction on an original character region
agrees with the orbit value at every common regular character. -/
theorem orbitValue_eq_scalarPresentation
    {f : rationalUnramifiedFunctionField L hp hL}
    (r : UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer
        (fun ψ => (rationalNormCharacters L ψ).toMul) π) f)
    {Ω : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    {g : Ω → ℂ} (s : ScalarPresentation Ω g) (hΩ : Ω.Nonempty)
    (hs : s.toFunctionField L hp hL hΩ = f) (χ : Ω)
    (hχ : r.denominator.val χ.val ≠ 0) :
    r.orbitValue π ⟨unramifiedTwistOrbitMap
      (fun ψ => (rationalNormCharacters L ψ).toMul) π χ.val,
        (r.orbitRegularRegion_map π χ.val).mpr hχ⟩ = g χ := by
  let R := unramifiedRegularFunctions (fun ψ => (rationalNormCharacters L ψ).toMul)
  let K := rationalUnramifiedFunctionField L hp hL
  have hi := rationalUnramifiedFunctionField_algebraMap_injective L hp hL
  have hr0 : algebraMap R K r.denominator ≠ 0 := by
    intro h
    exact r.denominator_ne_zero (hi (by simpa only [map_zero] using h))
  have hs0 : algebraMap R K s.denominator ≠ 0 := by
    intro h
    exact s.denominator_ne_zero hΩ (hi (by simpa only [map_zero] using h))
  have he : algebraMap R K r.numerator / algebraMap R K r.denominator =
      algebraMap R K s.numerator / algebraMap R K s.denominator :=
    r.represents.trans (hs.symm.trans (s.toFunctionField_eq_div L hp hL hΩ))
  have hc : r.numerator * s.denominator = s.numerator * r.denominator := by
    apply hi
    simpa only [map_mul] using (div_eq_div_iff hr0 hs0).mp he
  rw [r.orbitValue_map π χ.val hχ, s.value_eq_div χ]
  exact (div_eq_div_iff hχ (s.denominator_nonzero χ)).mpr
    (congrArg (fun b : R => b.val χ.val) hc)

end UnramifiedInvariantScalarPresentation

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω Λ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}
  (p : RationalOperatorContinuationData Ω A)
  (q : RationalOperatorContinuationData Λ B)
  (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty)
  (v : V) (ℓ : V →ₗ[ℂ] ℂ)
  (r : UnramifiedInvariantScalarPresentation L hp hL
    (smoothRepUnramifiedTwistStabilizer
      (fun ψ => (rationalNormCharacters L ψ).toMul) π)
    (continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ))

/-- Every invariant presentation of this extracted fraction recovers its
original coefficient wherever both the continued composite and it are regular. -/
theorem continuedCompositeOrbitScalar_value
    (χ : ↥(p.regularRegion ∩ q.regularRegion))
    (hχ : r.denominator.val χ.val ≠ 0) :
    r.orbitValue π ⟨unramifiedTwistOrbitMap
      (fun ψ => (rationalNormCharacters L ψ).toMul) π χ.val,
        (r.orbitRegularRegion_map π χ.val).mpr hχ⟩ =
      endomorphismScalarCoefficient v ℓ (p.continuedComposite q χ) :=
  r.orbitValue_eq_scalarPresentation L hp hL π
    (scalarCoefficientPresentation (p.continuedComposite q)
      (p.continuedComposite_rational q) v ℓ)
    (continuedCompositeRegion_nonempty L hp hL p q hΩ hΛ) rfl χ hχ

/-- Generic scalarity determines the full continued composite from the
orbit scalar wherever both the operators and the presentation are regular.
No irreducibility at the parameter under consideration is assumed. -/
theorem continuedComposite_eq_orbitScalar
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hU : IsOpen U) (hneU : U.Nonempty)
    (hscalar : ∀ χ : ↥(p.regularRegion ∩ q.regularRegion), χ.val ∈ U →
      ∃ c : ℂ, p.continuedComposite q χ = c • LinearMap.id)
    (hℓ : ℓ v = 1)
    (χ : ↥(p.regularRegion ∩ q.regularRegion))
    (hχ : r.denominator.val χ.val ≠ 0) :
    p.continuedComposite q χ =
      r.orbitValue π ⟨unramifiedTwistOrbitMap
        (fun ψ => (rationalNormCharacters L ψ).toMul) π χ.val,
          (r.orbitRegularRegion_map π χ.val).mpr hχ⟩ • LinearMap.id := by
  rw [continuedCompositeOrbitScalar_value L hp hL π p q hΩ hΛ v ℓ r χ hχ]
  have hopen := hU.inter (p.regularRegion_isOpen.inter q.regularRegion_isOpen)
  have hnonempty := (continuedCompositeRegion_dense L hp hL p q hΩ hΛ).inter_open_nonempty
    U hU hneU
  exact rationalUnramifiedScalarContinuation L hp hL hopen hnonempty
    Set.inter_subset_right (p.continuedComposite q) (p.continuedComposite_rational q)
    v ℓ hℓ (fun ψ hψ => hscalar ⟨ψ, hψ.2⟩ hψ.1) χ

end ValueComparison

end Langlands.Plancherel
