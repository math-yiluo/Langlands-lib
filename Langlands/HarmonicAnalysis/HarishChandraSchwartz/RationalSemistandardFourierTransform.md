# Actual Fourier tensors for every semistandard parabolic

This is the first construction step of the full Fourier product family
(`RationalSemistandardFourierFamily` is the second). It specializes the published
actual operator construction to the literal subgroups of every intrinsic
`SemistandardSpectralIndex i`. It does not assert smooth orbit dependence,
inter-parabolic covariance, or Fourier support finiteness.

## Source and scope

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), registered as
`waldspurger-2003-plancherel`, VII.1, printed pp. 313–314 (PDF pp. 79–80):
the embedding (1), the definition immediately following it, and VII.1.1(i)–(iii).
The coefficient product is that of V.2, supplied by the imported actual compact
induction development. The comparison bookkeeping below is an internal derived
construction, not an additional assertion attributed to Waldspurger.

The field universe `u` and complex representation carrier universe `uV` are
independent. The field is any nonarchimedean local field in the Library's sense
(including finite residue field), and the ambient group is affine and locally
of finite type. Connected reductivity, a maximal split torus, and a generic
cocharacter are explicit arguments for the rational Schwartz weights. No split,
quasisplit, characteristic-zero or positive-rank restriction is imposed.
No irreducibility of parabolic induction is assumed.

## Exact construction and hypotheses

For an intrinsic index `p`, the imported `parabolic p`, `levi p`, and `radical p`
are the point subgroups of its actual all-test subgroup functors. Their
`decomposition p` is the actual semidirect decomposition. A supplied
`CompactData p` records a compact open subgroup, continuous Levi projection,
and Iwasawa factorization. Its existence and projection continuity remain
separate published structural targets in `RationalSemistandardOrbitSections`.

`RationalSemistandard.ModularNormalization p` says that the parabolic modular
character equals the Haar modulus of its radical. The named Prop target
`RationalSemistandardModularNormalizationStatement` concludes that equality at
every semistandard index under connected reductivity and maximal splitness.
It is unproved here. Its standard specialization is proved by the existing
`modularCharacter_standardParabolicPoints`.

`rationalSemistandardInducedFourierTransform` takes an actual complex smooth
Levi representation `A`, a central normal subgroup `C`, a Borel quotient with
Haar measure `muM` invariant under inversion, square integrability modulo `C`,
and irreducibility of `A`. In the source case, take `C` to be exactly
`m.splitCenter a`, with `a` an actual split-component morphism for a representing
Levi model `m`; its centrality is the published `m.splitCenter_le_center`.
The more general central subgroup argument does not substitute an unrelated
formal degree for the split-component formal degree.

The ambient measure `mu` is left and right invariant. The Schwartz weight input
`hsw` is the precise `SquareIntegrableWeight mu (rationalXi ...) (rationalHeight ...)`.
The input `hT` is tempered coefficient growth of the actual normalized induced
representation. Both are preceding analytic obligations, not claimed external
structural facts. All displayed formulas retain these inputs where needed.
The pairing and inducing-equivalence transport identities additionally require
inversion invariance of `mu`.

The transform is the published `inducedFourierTransform`, hence the inverse of
`CompactInduction.coefficientTensorEquiv` applied to the actual
`coefficientFourierTransform`. The operator identity is

`coefficientTensorToEnd (E (fhat)) = d(A) • schwartzAction (check f)`.

Here `E` is the actual coefficient-tensor equivalence, `d(A)` is exactly
`representationFormalDegree C hC muM ...`, and `check f(g) = f(g⁻¹)`.
The result belongs to the dependency's `productInducedCoefficientObject`,
not to a newly introduced tensor carrier. The actual induced representation
is admissible by discrete-series admissibility and compact induction. Its
finite-rank tensor image is proved explicitly.

## Declaration dependencies and implemented proofs

Exported names in the following table are in `Langlands.HarishChandraSchwartz`,
with the indicated `RationalSemistandard` prefix where present.

| New declaration | Meaning and immediate dependency |
| --- | --- |
| `isClosed_fourierLevi` (private helper) | Closedness through the actual representing closed immersion. |
| `RationalSemistandard.compactOpenCofinal` | Cofinality from the compact open Levi intersection and `CompactOpenSubgroup.cofinal`. |
| `RationalSemistandard.CompactData.factorization_mem` | Converts the subtype factorization to the generic API. |
| `rationalSemistandardInducedFourierTransform` and `_eq_inducedFourierTransform` | Literal specialization of `inducedFourierTransform`; equality is reflexive. |
| `rationalSemistandardFourierTensorEquiv`, `...CoefficientMap`, `...ProductForm`, `...Admissible` | The existing tensor equivalence, actual compact probability coefficient map, V.2 formal-degree product, and induced admissibility. |
| `rationalSemistandardFourierTensorEquiv_transform` | Specializes `coefficientTensorEquiv_inducedFourierTransform`. |
| `rationalSemistandardFourier_operator` | The preceding tensor identity and `coefficientTensorToEnd_coefficientFourierTransform`. |
| `rationalSemistandardFourier_operator_finiteRank` | `coefficientTensorToEnd_mem_finiteRankEnd`. |
| `rationalSemistandardFourier_translate` | VII.1.1(i), by `inducedFourierTransform_translate`. |
| `rationalSemistandardFourier_pairing_integrable` | Absolute convergence by `integrable_conj_coefficientTensorMap_mul`. |
| `rationalSemistandardFourier_pairing` | VII.1.1(ii), by `integral_conj_coefficientMap_mul_eq_inner`. |
| `rationalSemistandardFourier_trace` | VII.1.1(iii), by `coefficientMap_inducedFourierTransform`; the character unfolds to the trace of `finiteRankSchwartzAction`. |
| `rationalSemistandardFourier_eq_of_pairings` | Uniqueness by the imported pairing characterization. |
| `rationalSemistandardFourier_transport` | Every inducing equivalence, including every self-twist, by `productInducedCoefficientTransport_inducedFourierTransform`. |
| `rationalSemistandardFourier_add`, `..._smul` | Complex linearity of the constructed linear map. |
| `rationalSemistandardFourierCompactTransport`, `..._compactTransport` | Prescribed change of compact picture `E_d.trans E_e.symm`; cancellation of the two inverse tensor maps proves compatibility. |
| `rationalSemistandardFourier_normalization` | Equality for two actual central quotient data when their actual formal degrees agree; unfold the construction and rewrite that equality. |
| `rationalSemistandardModularNormalization_standard` | Specializes the published actual standard modular theorem. |
| `rationalSemistandardFourier_standard` | Exact equality with `rationalInducedFourierTransform` at `standardIndex`, `standardCompactData`, and the published induced-temperedness proof; definitional equality and proof irrelevance. |

The translation convention throughout is
`Space.translate ... g1 g2 f(x) = f(g2⁻¹ * x * g1)`.
In particular the source's left translation is `lambda(g) = translate 1 g`,
and VII.1.1(iii) uses `lambda(g) check f(x) = check f(g⁻¹ * x)`.
Its right side is the trace of the actual finite-rank induced operator, not a
freely supplied character functional.

## Model and normalization boundaries

The transform is defined on the literal Levi subgroup and does not depend on a
representing scheme model. The imported model comparison fixes every actual
Levi element, unitary character value, and inducing representation; it merely
reindexes orbit sections. That reindexing is used in the product family
(`RationalSemistandardFourierFamily`).
Changing compact pictures uses the specified tensor equivalences above.

Changing split-component presentations uses the imported
`SplitCenterChoiceIndependenceStatement` and the actual quotient measures.
The normalization lemma deliberately displays equality of the actual formal
degrees: arbitrary independently scaled quotient Haar measures do not imply
that equality. Standard comparison for the same central quotient is fully
proved here; comparison of a whole product with independently supplied split
components and measures retains the precise normalization condition in
`RationalSemistandardFourierFamily`. The standard theorem also retains closedness of the chosen matrix
representation, its height compatibility with `K`, the Levi Iwasawa pair, and
`IsRationalLeviTempered`, exactly as the existing standard transform does.
