# `Θ^H` for one parabolic subgroup and the support of `ψ_f` (Waldspurger, Remark VIII.1.3)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedFixedOrbits`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitFourierPairing` (Library,
  this author's Unit 23). It provides `rationalFourierOrbitSection` (`ψ_f[O, P]`) and
  `rationalFourierOrbitSection_apply`. Through its imports come this author's
  `rationalInducedFourierTransform` (Unit 22, `f̂(ω, P)`), the actual-point facts of Unit 19
  (`exists_standardParabolicPoints_rootSet_mul`, `isClosed_standardParabolicPoints_rootSet`,
  `locallyCompactSpace_standardParabolicPoints_rootSet`,
  `compactSpace_leftQuotient_standardParabolicPoints_rootSet`) and the Library's
  `inducedFourierTransform`, `coefficientFourierTransform`,
  `coefficientFourierTransform_translate`, `coefficientTensorToEnd_action`,
  `coefficientTensorToEnd_injective`, `Space.translate`, `Space.exists_rightInvariant`,
  `UnitaryOrbitRepresentative`, `unitaryUnramifiedInclusion`,
  `unitaryOrbitRepresentative_isDiscreteSeries`, `isClosed_standardLeviPoints`,
  `RationalPointFamily.continuous_leviRationalNormCharacters` and `continuous_projection_standard`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteSeriesOrbitFiniteness` (Library):
  `discreteSeriesFixedOrbits` (`Θ^H_G` for an abstract group) and, through its imports,
  `DiscreteSeriesClass`, `discreteSeriesClass`, `DiscreteSeriesOrbitClass` and the action of the
  unitary unramified characters (`Langlands.Plancherel.DiscreteSeriesOrbits`).
- `Langlands.Representation.Aubert.General.InductionCompactVisibility` (Library):
  `finiteInductionFixedVectorVisibility`.
- `Langlands.Representation.Plancherel.NormalizedCompactPicture` (Library):
  `normalizedInductionCompactEquiv` and `unramifiedNormalizedInductionCompactEquiv`.
- `Langlands.Representation.Category.ClassInvariants` (Library):
  `fixedVectors_ne_bot_iff_of_equiv` and `SmoothDualClass.HasFixedVector`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on the
rendered PDF page 87.

- VIII.1, printed p. 321: "Soit `H` un sous-groupe ouvert compact de `G`. Pour `(O, P) ∈ Θ` et
  `(ω, E) ∈ O`, la propriété '`I_P^G E` possède des éléments non nuls invariants par `H`' ne
  dépend pas du choix de `(ω, E) ∈ O`. On note `Θ^H` l'ensemble des `(O, P)` tels que cette
  propriété soit vérifiée pour un (ou pour tout) `(ω, E) ∈ O`. On pose `Θ^H_G = Θ_G ∩ Θ^H`."
- Remarque VIII.1.3, printed p. 321: "Supposons le Théorème VIII.1.2 vrai pour tout sous-groupe
  de Lévi d'un sous-groupe parabolique semi-standard, resp. et propre, de `G`. Alors
  (i) `Θ^H`, resp. `Θ^H − Θ^H_G`, est fini pour tout sous-groupe ouvert compact `H` de `G`;
  (ii) pour tout `f ∈ C(G)`, l'ensemble des `(O, P) ∈ Θ`, resp. `Θ − Θ_G`, tels que
  `ψ_f[O, P] ≠ 0` est fini. En effet, pour (i), on peut supposer que `H` est un sous-groupe
  distingué de `K`. Pour `(O, P = MU) ∈ Θ`, on a alors `(O, P) ∈ Θ^H` si et seulement si
  `O ∈ Θ^{M∩H}_M`. D'autre part si `f ∈ C(G)` et si `H` est un sous-groupe ouvert compact de `G`
  tel que `f` soit bi-invariante par `H`, il est clair que, pour `(O, P) ∈ Θ`, `ψ_f[O, P] ≠ 0`
  seulement si `(O, P) ∈ Θ^H`."
- Théorème VIII.1.2, printed p. 321: "Pour tout sous-groupe ouvert compact `H` de `G`, `Θ^H_G`
  est fini." Its actual statement is `RationalDiscreteSeriesOrbitFinitenessStatement`
  (published, not proved).

`f̂(ω, P) = d(ω) π(f̌)` with `π = I_P^G ω` is VII.1 (printed p. 313), and `ψ_f[O, P]` is the
section `ω ↦ f̂(ω, P)` over `O` (VII.1, printed p. 316); both are quoted in the Markdown of
`RationalInducedFourierTransform` and `RationalInducedOrbitFourierPairing`.

The source states "il est clair" for the vanishing and gives the reduction for (i) in two
sentences. The proofs here are this author's (provenance: derived). The route for (i) differs
from the source: instead of reducing to `H` normal in `K` and the subgroup `M ∩ H`, it uses the
Library's `finiteInductionFixedVectorVisibility`, which gives finitely many compact open subgroups
`L_x` of `M`, independent of the inducing representation, such that `I_P^G E` has a nonzero
`H`-fixed vector only if `E` has a nonzero `L_x`-fixed vector for some `x`.

## Contents

### Vanishing (abstract)

Section `Vanishing`: `G` a topological group with the measure-theoretic assumptions of the
Library's `FourierTransform` (left and right invariant `mu`, `L2Weights mu Ξ σ`), `A` an
admissible smooth representation with tempered coefficients (`hT`), `Ξ` and `σ` invariant under
inversion.

- **`coefficientFourierTransform_eq_zero_of_fixedVectors_eq_bot A hw hA hT hΞ hσ ht d hH f hf`**:
  for `ht : TranslationWeights Ξ σ`, `d : ℝ`, a subgroup `H` with
  `hH : fixedVectors A.representation H = ⊥`, and `f ∈ Space Ξ σ` right invariant under `H`
  (`hf : ∀ k ∈ H, ∀ g, f (g * k) = f g`): `coefficientFourierTransform A … d f = 0`, that is
  `d π(f̌) = 0` in `A ⊗ Ã`.

Section `Induced`: the hypotheses of the Library's `inducedFourierTransform` (a closed
semidirect decomposition `P = M ⋉ U`, `G = P K` with `K` compact open, `G` unimodular, the modulus
of `P`, `A` irreducible and square integrable modulo `C`, `L2Weights`, tempered coefficients of
`I_P^G A`).

- **`inducedFourierTransform_eq_zero_of_fixedVectors_eq_bot … ht hH f hf`**: if
  `hH : fixedVectors (I_P^G A) H = ⊥` and `f` is right invariant under `H`, then
  `f̂(A, P) = inducedFourierTransform … f = 0`.

### Classes and twists

Section `Classes`: `G` a locally compact nonarchimedean group, `h : IsSemidirectDecomposition P M
U`, `hU : IsClosed U`.

- **`HasInducedFixedVector h hU H`** (definition): the predicate on
  `SmoothDualClass` of `M` (classes of irreducible admissible representations) lifting
  `A ↦ fixedVectors (I_P^G A) H ≠ ⊥` through the quotient. It is well defined because
  normalized induction (`normalizedInductionFunctor h hU`) carries an isomorphism to an
  equivalence (`SmoothRep.equivOfIso`, `fixedVectors_ne_bot_iff_of_equiv`).
- `hasInducedFixedVector_mk`: on the class of `A`, it is `fixedVectors (I_P^G A) H ≠ ⊥`
  (`Iff.rfl`).

Section `Restriction`: `G` a group, `V`, `W` complex vector spaces.

- `fixedVectors_eq_comap_subtype ρ hHK`: for `H ≤ K`, the `H`-fixed vectors of `ρ` are the
  `H ∩ K`-fixed vectors (`H.comap K.subtype`) of the restriction `ρ.comp K.subtype`.
- `fixedVectors_ne_bot_iff_of_equiv_restrict e hHK`: for an equivalence
  `e : Representation.Equiv (ρ.comp K.subtype) (τ.comp K.subtype)` and `H ≤ K`,
  `fixedVectors ρ H ≠ ⊥ ↔ fixedVectors τ H ≠ ⊥`.

Section `Twist`: moreover `K` an open subgroup, `hP : IsClosed P`, `hK : IsCompact K`,
`hPK : ∀ g, ∃ p : P, ∃ k : K, g = p * k`, `ν : I → (M →* ℝ≥0ˣ)` with continuous members (`hν`),
and `hr : Continuous h.projection`.

- **`fixedVectors_normalizedInduction_twist_ne_bot_iff … χ A hHK`**: for an unramified character
  `χ : unramifiedCharacters ν` and `H ≤ K`, `I_P^G(A ⊗ χ)` has a nonzero `H`-fixed vector iff
  `I_P^G A` does. This is the independence of `(ω, E) ∈ O` in VIII.1.
- `hasInducedFixedVector_twist_iff … χ hHK ω`: the same on classes, with
  `SmoothDualClass.twist`.

### `Θ^H` for one parabolic

Section `Orbits`: moreover `C` a normal subgroup of `M` contained in its center, a Haar measure
`μM` on `M ⧸ C` (Waldspurger's `C = A_M`), and `ν`.

- **`inducedDiscreteSeriesFixedOrbits h hU C hC μM ν H`** (definition, the recorded declaration):
  the image in `DiscreteSeriesOrbitClass C hC μM ν` (orbits of the unitary unramified characters
  `Im X(M)` in `E₂(M)`) of the discrete-series classes `ω` with `HasInducedFixedVector h hU H ω`.
  It is the set of `O` with `(O, P) ∈ Θ^H`, defined, as in the source, by "for one `(ω, E) ∈ O`".
  It parallels the Library's `discreteSeriesFixedOrbits` (`Θ^H_G`).
- `mk_mem_inducedDiscreteSeriesFixedOrbits_of_representative h hU C hC μM ν π hπ A hA`: if
  `π` is square integrable modulo `C` (`hπ`) and some `A : UnitaryOrbitRepresentative ν π` has
  `fixedVectors (I_P^G A) H ≠ ⊥`, then the orbit of the class of `π` lies in the set.
- **`mk_mem_inducedDiscreteSeriesFixedOrbits_iff … hHK ω`** (with the hypotheses of `Twist`,
  `H ≤ K`): the orbit of `ω` lies in the set iff `HasInducedFixedVector h hU H ω`. So "for one"
  and "for every" member agree, as stated in VIII.1.
- `fixedVectors_unitaryOrbitRepresentative_eq_bot … hHK π hπ A`: for `H ≤ K`, if
  `fixedVectors (I_P^G π) H = ⊥`, the same holds for every `A : UnitaryOrbitRepresentative ν π`.

Section `Finiteness`: moreover `hM : IsClosed M` and `[CompactSpace (Induction.LeftQuotient P)]`.

- `exists_inducedDiscreteSeriesFixedOrbits_subset h hU hM C hC μM ν H`: for an open subgroup `H`
  of `G`, there are a finite set `t` and compact open subgroups `L x` of `M`, `x ∈ t`, with
  `inducedDiscreteSeriesFixedOrbits … H ⊆ ⋃ x, discreteSeriesFixedOrbits C hC μM ν (L x)`.
- **`finite_inducedDiscreteSeriesFixedOrbits h hU hM C hC μM ν H hfin`**: if `hfin` holds
  (`discreteSeriesFixedOrbits C hC μM ν L` is finite for every compact open subgroup `L` of `M`:
  Theorem VIII.1.2 for `M`), then `inducedDiscreteSeriesFixedOrbits … H` is finite. This is
  Remark VIII.1.3 (i) for one `P`.

### Actual rational points

Section `Rational`: the setting of Units 19–28. `F` is a nonarchimedean local field, `G` a group
scheme over `F` with `hG : IsConnectedReductive G`, `i` a maximal split torus (`hi`), `ν` a
generic cocharacter (`hν`), `I` a finite set of simple roots, `P = P_I(F) = M_I(F) ⋉ U_I(F)` with
`M_I(F)` the subtype `𝐌` of `G(F)`, `K` an open subgroup with `hKc : IsCompact K` and
`hPK : IsIwasawaPair P₀(F) K`. The decomposition is `isSemidirectDecomposition_standard` and the
closedness of `U_I(F)` is `isClosed_standardUnipotentPoints` (local notations `𝐡`, `𝐡U`). The
unramified characters of `M_I(F)` are `RationalPointFamily.leviRationalNormCharacters i ν I`.

- `exists_standardParabolicPoints_rootSet_subtype_mul hG hi hν I hPK g`: `G(F) = P_I(F) K` with
  subgroup elements.
- `fixedVectors_rationalInduction_unitaryOrbitRepresentative_eq_bot hG hi hν I hKc hPK hHK π hπ
  A`: the abstract result above for `P_I(F)`, `H ≤ K`.
- **`finite_rationalInducedDiscreteSeriesFixedOrbits hG hi hν I hKc hPK C hC μM H hfin`**: for an
  open subgroup `H` of `G(F)`, if `hfin` holds for `M_I(F)` (Theorem VIII.1.2 for `M_I(F)` modulo
  `C`, for all compact open `L`), then the set of orbits `O` with `(O, P_I(F)) ∈ Θ^H` is finite.
  `P_I(F) \ G(F)` is compact by `compactSpace_leftQuotient_standardParabolicPoints_rootSet` and
  `M_I(F)` is closed by `isClosed_standardLeviPoints`.

Section `Representative` (the hypotheses of `rationalInducedFourierTransform`: `ρ`, `hρ`, `hKρ`,
`hM`, `A`, `C`, `μM`, `hsq`, `hirr`, `hTA`, `mu`, `hsw`):

- **`rationalInducedFourierTransform_eq_zero_of_fixedVectors_eq_bot … hH f hf`**: if
  `I_{P_I}^G A` has no nonzero `H`-fixed vector (`hH`) and `f ∈ C(G)` is right invariant under
  `H`, then `f̂(A, P_I) = 0`.

Section `Orbit` (the hypotheses of `rationalFourierOrbitSection`: `π`, `hsq` for `π`, `hTA` for
every representative of the orbit):

- **`rationalFourierOrbitSection_eq_zero_of_fixedVectors_eq_bot … hHK hπ f hf`**: for `H ≤ K`, if
  `I_{P_I}^G π` has no nonzero `H`-fixed vector and `f` is right invariant under `H`, then
  `ψ_f[O, P_I] = 0`.
- **`mk_mem_inducedDiscreteSeriesFixedOrbits_of_rationalFourierOrbitSection_ne_zero … f hf hne`**:
  for every subgroup `H` under which `f` is right invariant, `ψ_f[O, P_I] ≠ 0` implies that the
  orbit of the class of `π` lies in `inducedDiscreteSeriesFixedOrbits 𝐡 𝐡U C hC μM
  (leviRationalNormCharacters i ν I) H` (`(O, P_I) ∈ Θ^H`). No condition `H ≤ K` is needed here.

Section `Support` (the same hypotheses without `π`):

- **`exists_finite_rationalFourierOrbitSection_ne_zero … hfin f`**: given `hfin` for `M_I(F)`,
  for every `f ∈ C(G)` there is a finite set `T` of orbit classes such that every `π`
  (square integrable modulo `C`, with `hTA` for its orbit) with `ψ_f[O, P_I] ≠ 0` has its orbit
  in `T`. This is Remark VIII.1.3 (ii) for one standard `P`.

## Proofs

- `coefficientFourierTransform_eq_zero_of_fixedVectors_eq_bot`: let `T` be the endomorphism of
  `t = d π(f̌)` (`coefficientTensorToEnd`). For `k ∈ H`, `ρ(k) f = f` (`Space.translate ht k 1 f
  = f` by `hf`), so Lemma VII.1.1 (i) (`coefficientFourierTransform_translate`) gives
  `t = (π(k) ⊗ 1) t`, and `coefficientTensorToEnd_action` gives `T = π(k) T`. Hence every `T w`
  is `H`-fixed, so `T w = 0` by `hH`, `T = 0`, and `t = 0` by `coefficientTensorToEnd_injective`.
- `inducedFourierTransform_eq_zero_of_fixedVectors_eq_bot`: `inducedFourierTransform` is the
  inverse of `coefficientTensorEquiv` applied to `coefficientFourierTransform` for `I_P^G A` and
  `d = d(A)`; the latter vanishes.
- `HasInducedFixedVector`: `Quotient.lift` with `fixedVectors_ne_bot_iff_of_equiv` applied to the
  image of an isomorphism under `normalizedInductionFunctor`.
- `fixedVectors_eq_comap_subtype`: both sides are `{v | ρ(h) v = v for h ∈ H}`.
  `fixedVectors_ne_bot_iff_of_equiv_restrict` rewrites both sides with it and applies
  `fixedVectors_ne_bot_iff_of_equiv` to `e`.
- `fixedVectors_normalizedInduction_twist_ne_bot_iff`: `unramifiedNormalizedInductionCompactEquiv`
  restricts `I_P^G(A ⊗ χ)` to `K` as the compact picture of `A`; composing with the inverse of
  `normalizedInductionCompactEquiv` gives an equivalence of the restrictions to `K` of
  `I_P^G(A ⊗ χ)` and `I_P^G A`; apply `fixedVectors_ne_bot_iff_of_equiv_restrict`.
- `mk_mem_inducedDiscreteSeriesFixedOrbits_of_representative`: the class of `A` is a discrete
  series (`unitaryOrbitRepresentative_isDiscreteSeries`) with the property, and the orbit
  membership of `A` gives `χ` with `χ · [π] = [A]`, so the two orbits coincide
  (`Quotient.sound`).
- `mk_mem_inducedDiscreteSeriesFixedOrbits_iff`: if `[ω]` is the orbit of some `w` with the
  property, `Quotient.exact` gives `w = χ · ω` and `hasInducedFixedVector_twist_iff` (with
  `unitaryUnramifiedInclusion ν χ`) transfers the property to `ω`. The converse is the
  definition.
- `fixedVectors_unitaryOrbitRepresentative_eq_bot`: the orbit membership of `A` and
  `hasInducedFixedVector_twist_iff` at the class of `π`.
- `exists_inducedDiscreteSeriesFixedOrbits_subset`: `finiteInductionFixedVectorVisibility` gives
  `t` and `L`. For an orbit `[ω]` with the property, choose a representative `A` of `ω`
  (`Quotient.exists_rep`); `I_P^G A` has a nonzero `H`-fixed vector, hence `A` has a nonzero
  `L x`-fixed vector for some `x`, so `[ω] ∈ discreteSeriesFixedOrbits … (L x)`.
- `finite_inducedDiscreteSeriesFixedOrbits`: a finite union of finite sets (`Set.finite_iUnion`).
- The actual statements instantiate the abstract ones with `G(F)`, `M_I(F)`, `P_I(F)`; the
  Fourier vanishing unfolds `rationalInducedFourierTransform` and closes with
  `with_reducible_and_instances exact`, as in Units 19–27. The orbit statements apply the
  per-representative vanishing at every `A` (`rationalFourierOrbitSection_apply`). The support
  theorem takes `H = L` with `L` the compact open subgroup of `Space.exists_rightInvariant f` and
  `T = Θ^L` for `P_I(F)`.

## Scope and hypotheses

- Only one standard parabolic `P_I ⊇ P₀` at a time. The source's `Θ` consists of pairs `(O, P)`
  with `P` semi-standard; this module treats the standard ones, and the finiteness over all `I`
  (finitely many) is not stated as one theorem.
- Theorem VIII.1.2 for `M_I(F)` is the hypothesis `hfin`, as in the source, whose Remark VIII.1.3
  assumes it for the Levi subgroups. It is stated for the subtype `M_I(F)` of `G(F)`, modulo the
  given central subgroup `C` with the Haar measure `μM`, for every compact open `L`. The published
  `RationalDiscreteSeriesOrbitFinitenessStatement` concerns a group scheme with a split
  component; its transport to the subtype `M_I(F)` (through the Levi scheme
  `Standard.leviScheme`) is not done here.
- The vanishing results require only right invariance of `f` under `H` (the source assumes
  bi-invariance). They use the hypotheses of `rationalInducedFourierTransform` (`hsw`, the
  conclusion of Lemma II.1.5; `hTA`, temperedness of the representatives) unchanged.
- The twist independence and `mk_mem_inducedDiscreteSeriesFixedOrbits_iff` need `H ≤ K` with
  `G = P K`; the source reduces to this case ("on peut supposer que `H` est un sous-groupe
  distingué de `K`"). The membership for `ψ_f[O, P] ≠ 0` and the finiteness hold for every `H`.
