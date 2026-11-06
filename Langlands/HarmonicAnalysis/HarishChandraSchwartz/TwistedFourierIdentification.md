# The Fourier transform at a twist `ω ⊗ χ` (Waldspurger VII.1.3, case `M = G`)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TwistedFourierIdentification`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.TwistedFourierFamily`: `Space.twist`
(`f ↦ f χ_z`) and `schwartzActionTensor_twist_mem_finiteSmoothFamilies`. Through its imports it
also supplies `schwartzActionTensor`, `schwartzActionTensor_eq_of_coefficientTensorToEnd_eq`,
`coefficientTensorToEnd`, `coefficientFourierTransform` with
`coefficientFourierTransform_apply`, `schwartzAction_eval`, `ext_smoothDual`, `Space.check`,
`finiteSmoothFamilies`, `torusCharacter`, the twist `SmoothRep.twist` and
`smoothContragredientTwistEquiv` (the identification of the smooth dual of `A ⊗ χ` with that of
`A`, keeping the underlying functional).

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`).

- Proof of Proposition VII.1.3, printed p. 316 (PDF p. 82): for `M = G`,
  `C_{v⊗v̌, f}(χ) = d(ω ⊗ χ) ⟨(ω ⊗ χ)(f̌) v, v̌⟩`, and the first assertion is
  `C_{v⊗v̌, f} ∈ C^∞(Im X(G))`. "Notons que `d(ω ⊗ χ) = d(ω)` pour tout `χ ∈ Im X(G)`."
- VII.1, printed p. 313 (PDF p. 79): `f̂(ω, G) = d(ω) ω(f̌)` in `E ⊗ Ě` by VII.1 (1).

The smoothness of `χ ↦ f̂(ω ⊗ χ, G)` (all coefficients at once) is source content. The
identification `(ω ⊗ χ)(f) = ω(f χ)` (`twistTensorEquiv_schwartzActionTensor`) is derived; the
source uses it implicitly. The torus coordinates are derived as in `TwistedFourierFamily`.

### Correspondence with the source

- `ω ⊗ χ` is the Library's twist `A.twist χ hχ` of a smooth representation `A` by a character
  `χ : G →* ℂˣ` with open kernel. Its carrier is that of `A`; its smooth dual is identified with
  that of `A` by `smoothContragredientTwistEquiv`, which keeps the underlying functional.
  `twistTensorEquiv A χ hχ : (A ⊗ χ) ⊗ (A ⊗ χ)~ ≃ A ⊗ Ã` is the identity on the first factor
  and this identification on the second.
- `f̂(ω ⊗ χ, G)` for a given constant `d` is
  `coefficientFourierTransform (A.twist χ hχ) hw hA' hT' hΞ hσ d f = d (A ⊗ χ)(f̌)`. For
  `d = d(ω)`, the source's `d(ω ⊗ χ) = d(ω)` is the Library's
  `representationFormalDegree_unitaryTwist` (Worker 200), which is not used here: the family
  theorem takes one fixed `d`.
- `Im X(G)` is replaced by a torus `J → Circle` with characters `χ z` satisfying
  `χ z g = ∏ⱼ zⱼ^{n(g)ⱼ}` (hypothesis `hχn`) for a lattice map `n` as in `TwistedFourierFamily`.

## Scope and hypotheses

### Identification section

`G` is a topological group with `MeasurableSpace`, `OpensMeasurableSpace`, `MeasurableMul` and
`Nonempty (CompactOpenSubgroup G)`; `μ` a left and right invariant measure; `Ξ σ : G → ℝ` with
`hw : L2Weights μ Ξ σ`; `A : SmoothRep ℂ G` with `hA : IsAdmissible A.representation` and
`hT : HasTemperedCoefficients Ξ σ A.representation`; `χ : G →* ℂˣ` with
`hχ : IsOpen χ.ker`; `hA'` and `hT'`: admissibility and tempered coefficients of `A ⊗ χ`.

- `twistTensorEquiv` and `coefficientTensorToEnd_twistTensorEquiv` use only `A`, `χ`, `hχ` and
  the topological group structure.
- `twistTensorEquiv_schwartzActionTensor` uses all of the above, plus a finite type `J`,
  `n : G → (J → ℤ)` with `hn : ∀ g h, n (g h) = n g + n h`, a compact open subgroup `K₀` with
  `hK₀ : ∀ k ∈ K₀, n k = 0`, `z : J → Circle`, `hχn : ∀ g, χ g = torusCharacter (n g) z`, and
  `φ ∈ C(G)`.

### Family section

The data of the identification section with `χ` replaced by a family
`χ : (J → Circle) → G →* ℂˣ` with `hχ : ∀ z, IsOpen (χ z).ker`,
`hχn : ∀ z g, χ z g = torusCharacter (n g) z`, `hA' : ∀ z` (admissibility of `A ⊗ χ z`) and
`hT' : ∀ z` (tempered coefficients of `A ⊗ χ z`); `hn`, `K₀`, `hK₀`, `hnm : Measurable n`,
`hnσ : ∀ g, ‖n g‖ ≤ C (1 + σ g)`; `hΞ`, `hσ` (inversion symmetry of `Ξ`, `σ`); `d : ℝ` and
`f ∈ C(G)`.

## Definitions

- `twistTensorEquiv A χ hχ : CoefficientTensor (A.twist χ hχ) ≃ₗ[ℂ] CoefficientTensor A`.

## Results

- `coefficientTensorToEnd_twistTensorEquiv`: the endomorphism of `A` attached to a tensor is
  unchanged when the twist is removed.
- `twistTensorEquiv_schwartzActionTensor`: for `χ = χ_z`, removing the twist from the tensor of
  `(A ⊗ χ_z)(φ)` gives the tensor of `A(φ χ_z)`.
- `twistTensorEquiv_coefficientFourierTransform_mem_finiteSmoothFamilies`: the family
  `z ↦ twistTensorEquiv (d (A ⊗ χ_z)(f̌))` is a finite smooth family on `J → Circle` with values
  in `A ⊗ Ã`.

## Proof notes

1. `coefficientTensorToEnd_twistTensorEquiv`: on `v ⊗ ℓ` both sides are `w ↦ ℓ(w) v`.
2. `twistTensorEquiv_schwartzActionTensor`: by uniqueness of the tensor of `A(φ χ_z)`, compare
   endomorphisms. By step 1 the left side has endomorphism `(A ⊗ χ_z)(φ)`. For `ℓ` a smooth
   functional of `A`, `ℓ((A ⊗ χ_z)(φ) w) = ∫_G φ(g) ℓ(χ_z(g) A(g) w) dμ(g)
   = ∫_G (φ χ_z)(g) ℓ(A(g) w) dμ(g)`, the value of `ℓ` at `A(φ χ_z) w`.
3. Family: `d (A ⊗ χ_z)(f̌)` untwisted is `d` times the tensor of `A(f̌ χ_z)` by step 2, and
   `TwistedFourierFamily` shows that `z ↦` the tensor of `A(f̌ χ_z)` is a finite smooth family.

## Relation to the Library

- `TwistedFourierFamily` proves the smoothness for `A(f χ_z)`. This module identifies those
  operators with the Fourier transforms of the Library's twisted representations.
- Worker 200's `productCompactTwistTensorEquiv ν χ A`, for an unramified character `χ`, has the
  same definition as `twistTensorEquiv A χ.val.toMonoidHom …`; this module does not use it.

## Open obligations

- The lattice map `n` and the coordinate identity `hχn` for the actual `Im X(G)` are not
  supplied here.
- The reduction from general `M` to `M = G` (through Lemma VII.1.2) and the passage to the
  sections `C^∞(O, P)` are not done here.
