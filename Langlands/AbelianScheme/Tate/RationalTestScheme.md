# Rational and adelic test-scheme restriction

Fix a scheme `S`, a commutative group object `G` over `S`, and a morphism
`a : T' ⟶ T` of test schemes over `S`. This module extends actual
integral test-scheme restriction to the published rational Tate modules.
The main declarations are in `Langlands.GroupScheme.Tate`; the final
namespace `Langlands.AbelianScheme.Tate` supplies the actual abelian-scheme
specialization and its rational-homomorphism naturality.

## Internal provenance

`TestScheme` constructs restriction by precomposition on the actual
torsion sections and their coherent-family limit. `Rational` constructs
`ℚ ⊗[ℤ] Integral G T P`, with the rational factor first, and the maps
induced by group-scheme and rational abelian-scheme homomorphisms.
`RationalScalars` and `AwayRationalScalars` construct the rational residue
and conditional adelic actions. The present module applies scalar
extension to the existing restriction map. Its new assertions follow from
these constructions; no additional original-literature claim is used.

## Rational restriction

For any predicate `P : ℕ → Prop`, `rationalTestRestrict G P a` is the
rational base change of the integer-linear map underlying
`testRestrict G P a`. It is a `ℚ`-linear map from `Rational G T P` to
`Rational G T' P`. Its pure-tensor formula sends `q ⊗ x` to
`q ⊗ testRestrict G P a x`. The `toRational` compatibility is the case
`q = 1`, and does not assert injectivity of `toRational`.

`rationalTestRestrict_id` and `rationalTestRestrict_comp` give identity
and contravariant composition. For `b : T'' ⟶ T'`, the latter says that
restriction along `b ≫ a` first restricts along `a` and then along `b`.
The proofs use linear-map extensionality on pure tensors and the integral
identity and composition laws.

`rationalTestRestrict_restrictAway` shows that restriction commutes with
restricting the order indices to those coprime to any natural modulus `m`.
`rationalTestRestrict_map` shows that it commutes with the rational Tate
map of a homomorphism `G ⟶ H`. Tensor induction reduces both equalities
to their integral counterparts and additivity.

## Scalar actions

`rationalTestRestrict_scalarAction` preserves the existing action of
`ℚ ⊗[ℤ] Global.ProfiniteIntegerRing` on any selected rational Tate
module. It is an application of `TateScalarExtension.map_action` to the
published continuous linear map `fullTestRestrict`, after forgetting
continuity. `rationalTestRestrict_awayScalarAction` uses
`awayTestRestrict` to prove the corresponding law for
`ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m` on the away module.

Assume explicitly `h : Global.RationalProfiniteIntegerAdeleComparison`.
`rationalTestRestrict_finiteAdeleAction` evaluates the full scalar law
at the inverse image under the comparison chosen from `h`.
`finiteAdeleTestRestrict` bundles this as a linear map over the existing
ring `Global.FiniteAdeles ℚ`, installing the existing local module
structures with the same `h` on both ends.

For `hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`,
`rationalTestRestrict_primeToFiniteAdeleAction` and
`primeToFiniteAdeleTestRestrict` give the analogous law and linear map
over `Global.PrimeToFiniteAdeles m`. The away witness remains coupled
to the same full witness `h`. Apply lemmas identify these bundles with
the original rational restriction function. The comparison propositions
are assumptions, not proved here.

## Actual abelian schemes

The abelian-scheme abbreviation `rationalTestRestrict A P a` specializes
the group-object map to `A.toGrp`. Its `rationalTestRestrict_map` theorem
commutes with the map of an actual abelian-scheme homomorphism.
`rationalTestRestrict_homMap` extends this to every
`f : Rationalization.Hom A B`: tensor induction on `f` uses the published
pure-tensor formula for `rationalHomMap`, rational linearity of restriction,
and additivity. `rationalTestRestrict_iso` specializes this law to the
forward map of an isomorphism in the rationalized category.

## Scope

All rational and adelic constructions here are algebraic. No rational
topology, continuity or restricted-product comparison is claimed. The
base `S` is fixed: these maps restrict test sections, rather than
constructing base change of the group scheme or geometric path transport.
No finiteness, rank, pairing or PEL completion claim is made.
