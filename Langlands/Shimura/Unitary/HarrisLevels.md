# CM-compatible signature charts and the unitary adelic level tower

Author: Worker 57. This module joins the actual global unitary algebra input
to the topological level spaces of `Langlands.Shimura.Levels`, with real
charts that are complex linear for a prescribed CM type.

## Why the charts must respect a CM type

At a real embedding `τ` of the totally real field `E`, the algebra
`ℝ ⊗_{E,τ} A` is isomorphic to complex `n × n` matrices, but such a real
algebra isomorphism is complex linear for one of the two complex embeddings
of the CM field `K` above `τ` and complex antilinear for the other. Composing
a chart with entrywise conjugation exchanges these. Entrywise conjugation
turns the coordinate homomorphism `z ↦ h(z)` of `Unitary.Domain` into
`z ↦ h(conj z)`. Thus the distinction between the corrected homomorphism of
Harris (1998, Erratum) and the original one of Harris (1997) has meaning only
relative to charts that are complex linear for a fixed CM type. This module
makes that CM type explicit and constructs charts compatible with it.

## Declarations

- `matrixConj n` is entrywise complex conjugation as a real algebra
  automorphism of complex matrices. It fixes every diagonal signature matrix,
  commutes with the conjugate transpose, and therefore commutes with every
  `signatureAdjoint n r` (`matrixConj_signatureAdjoint`). It sends the scalar
  matrix of `z` to the scalar matrix of the conjugate of `z`.
- `tmul_center_commute` and `chart_center_mem_range`: the image
  `1 ⊗ k` of an element `k` of the CM center commutes with the whole scalar
  extension, so every chart sends it to a scalar matrix. This uses Mathlib's
  identification of the center of a matrix algebra over a commutative ring
  with the scalar matrices.
- `chartCenter e` is the resulting ring homomorphism from `K` to the complex
  numbers, read off from the `(0,0)` entry (with `n ≠ 0`); `chart_center_eq_scalar`
  states that the chart sends `1 ⊗ k` to the scalar matrix of `chartCenter e k`,
  and `chartCenter_comp` proves that `chartCenter e` restricts to the given real
  embedding `τ` on `E`.
- `IsCMSection E K Φ` says that `Φ` chooses, for every real embedding `τ` of
  `E`, a complex embedding of `K` restricting to `τ`. For a CM extension this
  is the same as a CM type: one embedding from each complex-conjugate pair.
- `eq_or_eq_conjugate_of_comp_eq`: two complex embeddings of `K` that agree
  on `E` are equal or complex conjugate. The proof counts `E`-algebra maps
  into the complex numbers (`AlgHom.card`, with `[K:E] = 2`) and uses that
  `K` is totally complex, so an embedding differs from its conjugate.
- `HasSignature.exists_centerCompatible`: if `HasSignature σ τ n r` holds and
  `φ` is a complex embedding of `K` above `τ`, then there is a signature
  chart that intertwines the involutions and sends `1 ⊗ k` to the scalar
  matrix of `φ k`. The chart given by the predicate is kept if its center
  embedding is `φ`; otherwise it is composed with `matrixConj`.
- `HarrisSignatureCharts σ n Φ` records the distinguished real embedding,
  `n > 1`, the actual chart at every real embedding, its intertwining
  certificate for signature `(n-1,1)` at the distinguished embedding and
  `(n,0)` elsewhere, and its compatibility (`center`) with the section `Φ`.
  `ofSignature` constructs such charts by choice from `HasHarrisSignature`
  and a CM-type section; existence of a global algebra with prescribed
  finite invariants is not assumed.
- `component`, `component_involution`, `component_center`, `evaluation` and
  `evaluation_center` evaluate the original algebra in all charts; the CM
  center acts by the scalars `Φ τ k`.
- `rationalMap` transports genuine rational similitudes along the evaluation.
  The real multiplier is the image of the rational multiplier at every real
  embedding simultaneously (`rationalMap_multiplier`).
- `Domain` is the homogeneous quotient of the corrected product homomorphism
  from `Unitary.Domain`, with the rational action obtained through
  `rationalMap`. `tower` is the functor
  `U ↦ G(Q) \ (X × G(A_f)) / U` on actual compact open levels of the finite
  adelic points, with the continuous right translations and functor laws of
  `Levels`; its transition maps are surjective (`tower_map_surjective`).
- `unitaryLevelTower D h Φ hΦ` specializes to `CentralSimpleUnitaryData`,
  deriving rational finite dimensionality from the number-field tower.
- Harris's CM type. For an imaginary quadratic field `F` with
  `ι : F →+* K` and a complex embedding `τ₀` of `F`, `harrisCMSection E ι τ₀`
  sends a real embedding `τ` of `E` to `embeddingAbove` of the CM type
  `inducedFromImaginaryQuadratic ι τ₀` of `Langlands.Global.CMType`. The CM
  field instance is `IsCMField.ofCMExtension E K`; it is a proposition, so no
  data is chosen. `isCMSection_harrisCMSection` proves `IsCMSection`,
  `harrisCMSection_comp` that every selected embedding induces `τ₀`,
  `harrisCMSection_mem` that it belongs to the induced CM type, and
  `eq_harrisCMSection` that it is the only complex embedding above `τ`
  inducing `τ₀`. Hence this section is determined by `ι` and `τ₀`.
- `harrisUnitaryLevelTower D h ι τ₀` is `unitaryLevelTower` for this
  section, the tower of Harris (1999), Section 4.

## Scope

The construction chooses charts. Charts compatible with the same CM type
differ by complex-linear automorphisms compatible with the involution; this
module does not prove the resulting independence, the decomposition of the
real points of the global algebra, the complex-ball identification, local
compactness, existence of a compact open level, neatness, or any algebraic
scheme model. No output scheme is stored.

Harris also assumes that `p` splits in the imaginary quadratic field and
fixes local data at `p` (p.308). Those hypotheses concern the local
uniformization of Section 4 and are not imposed here.

## Sources

- Harris (1999), Section 1, printed p.301 (PDF p.3): the CM field, the
  central simple algebra with involution of the second kind, the rational
  similitude group `GG = GU(B,*)`, and signature `U(n-1,1)` at one real place
  and `U(n)` elsewhere, equation (1.1). Section 4, printed pp.308-309
  (PDF pp.10-11): the CM field "is assumed to contain an imaginary quadratic
  field", and the CM type consists of all complex embeddings inducing a
  chosen complex embedding of it; then the Shimura datum and its adelic
  level subgroups (4.1)-(4.3).
- Harris (1997), Section 2, printed pp.88-90: the archimedean conjugacy
  domain and the level and right-action mechanism, with the homomorphism
  corrected by Harris (1998), Erratum, printed pp.180-182.
- Kottwitz (1992), printed pp.654-655: the real conjugacy class, its
  centralizer description, compact open levels, and the separation of these
  data from the canonical model and reflex field.

These original passages were read. The chart adjustment, the explicit
CM-type section and the quotient packaging are derived implementations.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-1997-drinfeld-cohomology`:
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
- `harris-1998-local-langlands`:
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- `kottwitz-1992-lambda-adic-simple-shimura`:
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.

Formal dependencies: `Langlands.Shimura.Unitary.Adelic`, `Unitary.Domain`
(with `CMData` and `Signature`), `Langlands.Shimura.Levels`,
`Langlands.Global.CMType` (`inducedFromImaginaryQuadratic`, `embeddingAbove`
and its restriction, membership and uniqueness theorems), and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in particular
`Matrix.center_eq_range`, `AlgEquiv.mapMatrix`, `AlgHom.card` and
`IsCMField.ofCMExtension`.
