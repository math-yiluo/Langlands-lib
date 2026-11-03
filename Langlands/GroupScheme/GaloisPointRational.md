# Rational-point comparisons and multiplicative-group norm normalization

Worker 1294. Derived algebraic implementation using the Library's actual
`GroupScheme`, `CommGroupScheme`, `affinePoints`, `affinePointMap`,
`rationalPoints`, and scheme-pullback `baseChange` constructions. The imported
`GaloisPointDescent` and `GaloisPointNorm` construct effective coordinate descent
and the finite conjugate-product norm. Neither descent nor a norm is an extra
input to this module.

## Existing rational-point carriers

Let `k,L : Type u` be fields in the same arbitrary universe with `Algebra k L`,
and let G be an actual group scheme over `Spec k`.

`GaloisPointComparison.rationalCoeffEquiv` is a multiplicative equivalence from
`rationalPoints G` to the existing k-coefficient points. Its carrier map is
exactly the published `rationalPointEquiv` (`rationalCoeffEquiv_eq`), obtained by
changing the identity test scheme through `ringTestSelfIso`.

`baseMap k L` is the actual spectrum of `algebraMap k L`.
`baseChanged k L G` is the existing `GroupScheme.baseChange` along it.
`baseChangeCoeffEquiv` identifies `rationalPoints (baseChanged k L G)`
multiplicatively with the actual L-coefficient points. It reuses
`baseChangeBasePointsEquiv`, and `baseChangeCoeffEquiv_left` identifies its
underlying morphism as projection from the actual scheme pullback. These
comparisons need no affineness, finite-dimensionality or Galois hypotheses.

`rationalExtend` and `rationalConjugate` transport coefficient extension and
the actual coefficient-automorphism action to these existing rational-point
carriers. `rationalConjugate` uses the existing multiplicative automorphism
`affinePointAut`; its coefficient map is definitionally the canonical
`GaloisPoint.conjugate`. The explicit comparison equations are
`baseChangeCoeffEquiv_rationalExtend` and
`baseChangeCoeffEquiv_rationalConjugate`. `rationalExtend_fst` identifies
extension as pulling back the original section along `baseMap`. Identity and
composition laws for `rationalConjugate` follow through the injective comparison.
No replacement point carrier or group law is introduced.

For `T : CommGroupScheme (Spec k)` with `IsAffine T.X.left`, and with
`FiniteDimensional k L` and `IsGalois k L`, `rationalNorm` has domain
`rationalPoints` of the **actual** `CommGroupScheme.baseChange` of T and codomain
`rationalPoints T.toGrp`. `rationalCoeffEquiv_rationalNorm` identifies it with
the imported constructed `GaloisPoint.norm` under the explicit multiplicative
comparisons. `rationalNorm_extend` and `rationalExtend_norm` give, respectively,
the degree-power formula and the full Galois-product formula on these existing
rational-point carriers. They follow from the coefficient norm's intrinsic
laws and multiplicativity/injectivity of the comparisons.

## Multiplicative group normalization

The normalization lemmas are in namespace `Langlands.GroupScheme.GaloisPoint`.
`gm_units_extend` and `gm_units_conjugate` apply the existing
`Gm.affineUnitsEquiv_naturality` to identify extension and conjugation with the
usual maps on field units.

`gm_units_rationalCoeffEquiv` identifies the base-field rational/coefficient
comparison with the existing `Gm.affinePointsEquiv`. Similarly,
`gm_units_baseChangeCoeffEquiv` identifies the base-change comparison with the
existing `Gm.baseChangeUnitsEquiv`, followed by the actual global-section ring
isomorphism `Γ(Spec L) ≅ L`. Their proofs compare the units' regular-function
values, using the underlying scheme-projection equations above. These helper
comparisons require no finite-dimensionality, Galois or affineness assumptions.

For a finite-dimensional Galois extension, `gm_units_norm` identifies the
constructed coefficient-point norm for the actual multiplicative group with
`Units.map (Algebra.norm k) : Lˣ →* kˣ` under the existing
`Gm.affineUnitsEquiv` on both fields. The proof applies the injective field
inclusion to the unit values. The extended norm is the product over the full
Galois group, and this is `Algebra.norm_eq_prod_automorphisms` from pinned
Mathlib `RingTheory.Norm.Transitivity`. The private affineness instance unfolds
Gm as the actual pullback of the integral Laurent spectrum over `Spec ℤ` to
`Spec k`; affineness follows from that pullback. It is proved rather than
assumed as an extra hypothesis for Gm.

`gm_rational_units_norm` combines these identifications and gives the same field
unit norm on the existing rational-point carriers of Gm and its actual base
change. Its source units use the published `Gm.baseChangeUnitsEquiv` and
`Γ(Spec L) ≅ L`, and its target uses the published `Gm.affinePointsEquiv`.

## Provenance and arithmetic boundary

All comparisons and normalization proofs are derived implementation content.
The intended torus consumer is Kaletha and Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Lemma 2.5.12 and Definition 2.5.13, printed pp.89–90 / PDF
pp.120–121; registered source `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Read with the authors' corrections, version 1 November 2024, PDF pp.24–25;
registered source `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
The correction to Remark 2.5.11 changes its Serre reference to §6, and the
example in Remark 2.5.15 is replaced. Neither arithmetic assertion is used.
KP motivates the later norm-image consumer; it does not supply effective
descent as an assumption.

No splitness, torus, finite type, smoothness, characteristic, valuation, topology,
completeness, local compactness or residue-field hypothesis is imposed. This
module does not assert tower transitivity, splitting-field independence,
openness, unit-norm surjectivity, an Iwahori subgroup, a maximal unramified
characterization or a construction of `G(k)^0`. The existing WeilGm finite-free
determinant norm is unchanged. Those later arithmetic constructions and
compatibilities remain successor obligations.
