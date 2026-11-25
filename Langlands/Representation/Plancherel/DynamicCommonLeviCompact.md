# Actual common-Levi compact standard families

This is a derived adapter from the published actual common-Levi
standard integrals to the published compact-picture interface.

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, registered `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
IV.1, printed pp.276–278 / PDF pp.42–44, defines fixed compact pictures,
compact conjugation, representative naturality and the original weak standard
integral. The implementation specializes existing constructions; it does not
assert an additional source theorem or prove IV.1.1.

## Actual data and conventions

The field `F : Type u` is any nonarchimedean local field, with no
characteristic restriction. `G/F` is affine and locally of finite type. The
compact constructions assume `hG : IsConnectedReductive G`, with no splitness
or quasi-splitness restriction. A base cocharacter `χ` fixes the literal Levi
`levi χ`. Cocharacters `ψ, ψ'` come with equalities of their centralizer
subgroup functors to `Dynamic.centralizer χ`. Both decompositions are
precisely `DynamicCommonLeviComposition.commonDecomposition`, so both use
this literal common Levi and its inherited canonical rational-point topology.

There is one compact open subgroup `K`, a proof `hK` of its compactness,
and the two separate factorizations `hψK`, `hψ'K` of every actual ambient
point as a point of the corresponding parabolic times a point of `K`.
Closedness of the parabolics and radicals and unimodularity of the radicals
are the published proved results of `DynamicOppositeCanonicalScalar` and
`DynamicOppositeStandardIntertwining`. They are supplied to the general
compact construction, not imposed as new assumptions. The lemma
`commonProjection_continuous` transports the published projection-continuity
proof from `levi ψ` to the literal `levi χ` using the centralizer equality;
proof irrelevance identifies semidirect-decomposition proofs.

The inducing representation is canonical `SmoothRep.{0,u,uV} ℂ (levi χ)`.
The field universe `u`, original carrier universe `uV`, and equivalent
representative carrier universe `uW` are independent. No finite length,
admissibility, irreducibility, or finite-dimensionality is assumed for these
elementary constructions.

The parameter family is exactly `normCharacters χ`, indexed by **all**
`rationalCharacters (parameterScheme χ)`. Its transport to the literal
Levi is the existing `parameterTransport χ`; the norm family there is
`leviNormCharacters χ`. The published norm-character continuity is composed
with the inverse `parameterHomeomorph χ` only to pass to this literal Levi.
No lattice subset or alternative character algebra is introduced.

## Restriction, conjugation and the integral

`compactEquiv` is precisely `unramifiedLeviInductionCompactEquiv` with
these actual inputs. Its source is the varying positive Levi-normalized
induction of the actual twist; its target is the single fixed
`CompactInductionPicture (commonDecomposition χ ψ hψ) K A`.
`compactEquiv_eval` says that it is literal restriction to `K`.

`compactFamily` applies the existing `compactIntertwiningOperator` to the
published `pairFamily`. Thus it is exactly

```
res_target ∘ pairFamily(z) ∘ res_source⁻¹.
```

Its source and target are the fixed compact pictures of the two specified
common decompositions. The squared-modulus proof `hδ` remains an explicit
premise, as for `pairFamily`. Its parameter lies in precisely
`pairFullDomainRegion χ K hK ψ hψ ψ' A`; no openness or nonemptiness of
this full convergence domain is asserted.

`compactFamily_eval` identifies compact-point evaluation with evaluation of
the original pair integral on the actually extended source vector.
`compactFamily_spec` extends the compact output by `compactEquiv.symm` and
proves `StandardIntertwining.HasIntegral` for the original source. By the
imported definition this retains every ambient argument and every smooth
dual functional: the scalar integral is absolutely convergent and is
represented by a vector of the original inducing carrier. The measure is
literally `pairQuotientMeasure K hK ψ ψ'`, with the original radical and
intersection Haar measures normalized at this same `K`.
The proof cancels the target compact equivalence and uses `pairFamily_spec`.
There is no completion of the carrier and no rescaling of the integral.

## Equivalent representatives and opposite specialization

`pairFullDomainRegion_equiv` proves equality of the entire actual full
domains for any equivariant linear equivalence of inducing representations,
with the same quotient measure. It uses the published
`standardIntertwiningFullDomainRegion_equiv`, which preserves both absolute
scalar convergence and original-carrier representability. Neither full
domain for the second representative nor a commuting square is assumed.

`pairFamily_natural` proves the ambient integral square with the induced
map of `twistEquiv`; the second membership proof comes from this proved
full-domain equality. `compactFamily_natural` conjugates this square by
the actual compact equivalences. The vertical compact maps are exactly the
fixed pointwise `compactInductionPictureEquiv` maps. Both proofs specialize
published representative-naturality results and allow independent `uV,uW`.

`compactFamily_inverse_eq_conditionalForwardCompactFamily` specializes
`ψ = χ`, `ψ' = inverseCocharacter χ` and the published
`conditionalSquaredModulus χ hRefl hCST hG`, where
`hRefl : RelativeRootReflectionExistenceStatement` and
`hCST : CentralSplitTorusCharacterStatement`. It proves literal equality
with the published `conditionalForwardCompactFamily`. The decompositions,
closedness proofs and projection proofs have the same propositions; proof
irrelevance makes the equality definitional. No new squared-modulus proof
is claimed. This specialization retains the two original opposite compact
factorizations and the same quotient-measure normalization.

## Scope

This module supplies actual families and their elementary transport laws.
It proves neither squared-modulus compatibility for a general common-Levi
pair nor nonempty convergence regions, rationality, continuation existence,
unitary regularity, invertibility, composition, or scalar identities.
Those are separate obligations. The proofs use the ordinary
Lean axioms only; no axiom or proof hole is introduced.
