# The section `ψ_f[O, P]` (Waldspurger VII.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierCoherence`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierTransform`:
  `inducedFourierTransform` (`f ↦ f̂(ω, P)`), Lemma VII.1.1 (ii) in the form
  `integral_conj_coefficientMap_mul_eq_inner`, and the uniqueness statement
  `inducedFourierTransform_eq_of_forall_integral`;
- `Langlands.Representation.Plancherel.CompactProductFormTransport` (Worker 200): the transport
  `productInducedCoefficientTransport h hU e : L(A, P) ≃ L(B, P)` along an equivalence
  `e : A ≃ B` of inducing representations (through its import `ProductInducedTransport`),
  `CompactInduction.coefficientMap_transport` (`E_P^G` is unchanged by transport) and
  `CompactInduction.formalDegreeProductForm_ofEquiv` (the transport is an isometry for the product
  of V.2);
- `Langlands.Representation.Plancherel.ProductInducedOrbitSections` (Worker 200):
  `UnitaryOrbitRepresentative ν π`, `ProductInducedOrbitSections ν π h hU` and
  `coherentProductInducedOrbitSections ν π h hU`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`).

- VII.1, printed p. 316 (PDF p. 82): "Soit `O` une orbite dans `E_2(M)` pour l'action de
  `Im X(M)`. Pour `f ∈ C(G)`, on définit une fonction `ψ_f[O, P]` sur `O` par:
  `ψ_f[O, P]_ω = f̂(ω, P)` pour tout `ω ∈ O`."
- VI.1, printed pp. 295–296 (PDF pp. 61–62): the spaces `L(ω, P)` for the points `ω` of `O`
  are identified along equivalences of representatives, and `C^∞(O, P)` consists of sections
  compatible with these identifications.
- VII.1, printed p. 313 (PDF p. 79): `f̂(ω, P) = d(ω) π(f̌)` with `π = I_P^G ω`.

The definition `fourierOrbitSection` is source content (`ψ_f[O, P]`). That `f̂(ω, P)` is
compatible with the identifications of VI.1 is implicit in the source, which treats
`ψ_f[O, P]` as a function on `O`. Here it is proved as
`productInducedCoefficientTransport_inducedFourierTransform`. That theorem, the coherence and
the linear map are derived.

### Correspondence with the source

- `O` is the orbit of the class of `π : IrreducibleAdmissibleRep ℂ M` under the unitary
  unramified characters `unitaryUnramifiedCharacters ν` of Worker 200, for a family
  `ν : I → (M →* ℝ≥0ˣ)` of positive characters. Waldspurger's `Im X(M)` is the group of unitary
  unramified characters. A point `ω ∈ O` is represented by every actual
  `A : UnitaryOrbitRepresentative ν π`, an irreducible admissible representation whose class is
  in the orbit.
- A section over `O` assigns to every representative `A` an element of `L(A, P)`
  (`ProductInducedOrbitSections ν π h hU`). It is coherent if its values correspond under the
  transport along every equivalence of representatives
  (`coherentProductInducedOrbitSections ν π h hU`).
- `f̂(ω, P)` is `inducedFourierTransform … A … f` with `d(ω)` the formal degree of `A` for the
  Haar measure `μM` on `M/C`, as in `InducedFourierTransform`.

## Scope and hypotheses

### Transport section

The hypotheses of the transform section of `InducedFourierTransform` for two inducing
representations `A` and `B` with the same data: instances on `G` (`Group`, `TopologicalSpace`,
`LocallyCompactSpace`, `NonarchimedeanGroup`, `SecondCountableTopology`, `T2Space`,
`MeasurableSpace`, `BorelSpace`, `Nonempty (CompactOpenSubgroup G)`); subgroups `P`, `M`, `U`
with `[LocallyCompactSpace P]`; `h`, `hU`, `hP`, `hm`, `K`, `hK`, `hPK`, `hG`, `hδ`; `A`, `B` in
the same carrier universe; `hcof`; `C`, `hC`, the measurable structure on `M/C` and an
inversion-invariant Haar measure `μM`; square integrability and irreducibility of both,
`hsqA`, `hiA`, `hsqB`, `hiB`; a left and right invariant measure `μ` on `G` with
`hw : L2Weights μ Ξ σ`; tempered coefficients of both induced representations, `hTA`, `hTB`;
and `hΞ`, `hσ`. The theorem also takes `[MeasurableInv G]`, `[μ.IsInvInvariant]`, an
equivalence `e : A ≃ B` and `f ∈ C(G)`.

### Orbit section

The same data for `G`, `P`, `M`, `U`, `K`, `C`, `μM`, `μ`, `Ξ`, `σ`, with a family
`ν : I → (M →* ℝ≥0ˣ)`, `π : IrreducibleAdmissibleRep ℂ M`, and:

- `hsq : ∀ A : UnitaryOrbitRepresentative ν π`, `A` is square integrable modulo `C` for `μM`;
- `hT : ∀ A`, `I_P^G A` has tempered coefficients for `Ξ`, `σ`.

Irreducibility of each representative is part of `UnitaryOrbitRepresentative`. Square
integrability and tempered coefficients are required at every representative; this module does
not derive them from those of `π`. `fourierOrbitSection_mem_coherent` and
`fourierOrbitSectionLinear` also take `[MeasurableInv G]` and `[μ.IsInvInvariant]`.

## Definitions

- `fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f :
  ProductInducedOrbitSections ν π h hU` is `A ↦ f̂(A, P)`, i.e. `ψ_f[O, P]`.
- `fourierOrbitSectionLinear … : Space Ξ σ →ₗ[ℂ] coherentProductInducedOrbitSections ν π h hU`
  is `f ↦ ψ_f[O, P]`.

## Results

- `productInducedCoefficientTransport_inducedFourierTransform`: for `e : A ≃ B`,
  `productInducedCoefficientTransport h hU e (f̂(A, P)) = f̂(B, P)`.
- `fourierOrbitSection_apply` (definitional): the value at `A` is `f̂(A, P)`.
- `fourierOrbitSection_mem_coherent`: `ψ_f[O, P]` is a coherent section.

## Proof notes

1. Transport: by `inducedFourierTransform_eq_of_forall_integral` for `B`, it suffices to show
   `(E_P^G ψ, f)_G = (ψ, T f̂(A, P))_B` for every `ψ ∈ L(B, P)`, where `T` is the transport.
   Write `ψ = T (T⁻¹ ψ)`. Then `E_P^G ψ = E_P^G (T⁻¹ ψ)` (`coefficientMap_transport`), so the
   left side is `(T⁻¹ ψ, f̂(A, P))_A` by Lemma VII.1.1 (ii) for `A`. By
   `formalDegreeProductForm_ofEquiv` this is `(T T⁻¹ ψ, T f̂(A, P))_B = (ψ, T f̂(A, P))_B`.
2. Coherence: apply step 1 to each equivalence between representatives.
3. Linearity: `inducedFourierTransform` is linear at each representative.

## Relation to the Library

- Worker 200's `productInducedSmoothOrbitSections` are the coherent sections whose restriction
  to a fixed compact picture is a finite smooth family on the torus coordinates. Proposition
  VII.1.3 asserts that `ψ_f[O, P]` lies there and depends continuously on `f`; this module
  proves the coherence part only.

## Open obligations

- The smoothness of `ψ_f[O, P]` (Proposition VII.1.3) and continuity in `f` are not proved.
- Square integrability and tempered coefficients of the unitary twists of `π` are hypotheses.
