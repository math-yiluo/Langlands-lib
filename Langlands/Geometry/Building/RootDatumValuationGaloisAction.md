# Coefficient actions on actual root-datum valuations

This internal construction proves that the existing coefficient action preserves
and reflects `IsRootDatumValuation`, including its two normalization conditions
and every axiom V0–V5. It restricts that action to the subtype of all families
satisfying this predicate for the same descended group-scheme map. It does not
assume that this subtype is inhabited.

## Objects and hypotheses

Let `k` and `K` be fields in the same arbitrary universe, with a supplied
`Algebra k K`. Let `T` be a commutative group scheme over `k`, `G` a group scheme
over `k`, and `i : T.toGrp ⟶ G`. The actual base changes along
`algebraBaseMap k K` are denoted by `T_K`, `G_K`, and `i_K` below. The valuation
results assume that the underlying scheme map of `i_K` is a monomorphism and
that `G` is affine over `k`; affineness of `G_K` follows by base change.
There is no finite-dimensional, separable, Galois-extension, valuation on the
fields, splitness, or reductivity hypothesis.

For `σ : K ≃ₐ[k] K`, write `A_σ` for the existing ordinary character
representation and `Q_σ` for the existing multiplicative automorphism
`rationalConjugate k K G σ` of `rationalPoints G_K`. The underlying family
action remains exactly

`(σ φ)_a(g) = φ_(A_(σ⁻¹) a)(Q_(σ⁻¹) g)`.

The real values are unchanged. `image_rootGroupPoints_galois` proves
`Q_σ '' U_a(K) = U_(A_σ a)(K)` for the existing `rootGroupPoints` of the
actual relative-root subgroup functors. This image identity itself needs
neither the monomorphism nor affineness hypotheses.

## Normalizers and reflection realizers

The first two lemmas work over arbitrary schemes and prove that explicit
cocharacter transport commutes with postcomposition by the explicitly
descended automorphism. Their proofs use functoriality, cancellation of the
canonical descent isomorphism, and equality on test-scheme points.

`normalizerAction_galoisCocharacterAction` applies this to the actual
normalizing torus automorphism. Uniqueness of that automorphism identifies its
coefficient transport; tensor induction gives covariance of the existing
normalizer action on real cocharacters. Together with the published full
character covariance and evaluation pairing, this proves
`RealizesReflection.galoisTransport`: the actual conjugate normalizer point
sends the conjugate character to its negative and fixes its real kernel
pointwise. These two results use the monomorphism of `i_K` and need no
affineness hypothesis.

## Preservation of the valuation axioms

`IsRootDatumValuation.galoisTransport` transports a supplied proof of the
existing predicate, with the following implemented arguments.

- Normalization follows from the exact root permutation and root-group
  membership equivalence. For V0, the image of a root group under the
  transported function is the image of the original root group under the
  original function, so its cardinality bound is unchanged.
- V1 uses exact filtration transport, multiplicativity of `Q_σ`, and its
  preservation and reflection of equality with the identity. It proves all
  three subgroup closure conditions and the prescribed infinity fibre.
- V2 pulls a reflection realizer back by `σ⁻¹` using the proved reflection
  transport and reuses the same real constant from the original family.
- V3 first transports the negative-ray exclusion by the real scalar extension
  of `characterLattice.galoisEquiv`. This linear equivalence preserves the
  real tensor expressions and negatives, and its inverse character formulas
  recover the original exclusion. The proof then maps the entire original
  commutator-subgroup inclusion through `Q_σ.toMonoidHom`.
  `Subgroup.map_commutator` and `MonoidHom.map_closure`, together with exact
  filtration images, identify its left side with the required commutator
  subgroup. Every generator on the right maps to the generator with the same
  positive natural indices `p,q` and the same depth `p*r+q*s`; character
  linearity and the actual root permutation prove its root condition.
  Subgroup closure then gives the full required inclusion.
- V4 uses character linearity at `2a` and actual root-group covariance. V5
  pulls back the three factors and their normalizer membership by the same
  multiplicative coefficient map. The original equalities apply verbatim to
  the unchanged real values.

Thus V3 is proved for the generated subgroups appearing in the existing
predicate, rather than replaced by a condition only on individual
commutators. All normalization and axiom fields are proved without additional
premises.

## Restricted action and scope

`isRootDatumValuation_galoisAction_iff` also reflects the predicate by applying
the transport theorem to `σ⁻¹`. The definition
`IsRootDatumValuation.galoisAction` is a group homomorphism from `K ≃ₐ[k] K` to
permutations of exactly

`{φ : RootFunctionFamily T_K G_K // IsRootDatumValuation i_K φ}`.

Its inverse uses `σ⁻¹`. Subtype extensionality reduces the inverse, identity,
and composition laws to those of `RootFunctionFamily.galoisAction`.
`galoisAction_val` identifies the underlying family with that original action.

The provenance is internal: these are consequences of the published actual
coefficient, subgroup, normalizer, lattice, and family constructions and the
fields of the existing valuation predicate. No new original-literature
assertion is introduced. The mathematical content of V0–V5 is inherited from
that predicate, whose source comparison is documented in
`RootDatumValuation.md`.

This construction does not establish existence of a valuation, preservation of
V6 or full centralizer compatibility, equipollence with a coefficient
conjugate, or stability of any selected full valuation class. Those remain
separate obligations for a canonical apartment. It constructs no metric,
special vertex, supplied-model stabilizer comparison, or descent, and does not
prove `BuildingComparisonStatement`.
