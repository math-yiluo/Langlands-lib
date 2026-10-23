# Tensor-algebra-linear restriction and test-scheme isomorphisms

## Scope and provenance

This is derived algebraic infrastructure for the actual Tate modules in
Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 (PDF p.26), and their tensor-algebra frame structures in
Section III.1, printed pp.91–92 (PDF pp.99–100). The source defines the full
Tate module using all positive torsion orders, its rationalization, and the away
version using orders coprime to the excluded primes before rationalization.
The moduli problem uses frames linear for the endomorphism algebra tensored
with the full or away finite adeles. The restriction and transport maps below
are derived from the Library's actual test-scheme restriction; these particular
implementation formulas are not asserted to be statements from the source.

The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

## Parameters and constructed actions

Fix an abelian scheme `A` over a scheme `S`, test schemes `T`, `T'`, and `T''`
over `S`, a ring `D` with rational algebra structure, and an algebra map
`i : D →ₐ[ℚ] Rationalization.End A`. The latter codomain is the rationalization
of actual abelian-scheme endomorphisms. Injectivity of `i` is not required for
these constructions.

The full construction works with any torsion-order predicate `P`. Its carrier
`Rational A T P` is the rationalization of the coherent inverse limit of actual
torsion points at the positive orders satisfying `P`. The usual full carrier is
the specialization `P = fun _ => True`. The coefficient ring is
`D ⊗[ℚ] Global.FiniteAdeles ℚ`, acting through
`finiteAdeleAlgebraModule A T P h i`. One explicit witness
`h : Global.RationalProfiniteIntegerAdeleComparison` is used at every test scheme.

The away construction uses `RationalAway A T m`, selecting orders coprime to the
natural modulus `m`, and the coefficient ring
`D ⊗[ℚ] Global.PrimeToFiniteAdeles m`. Its action is the existing
`primeToFiniteAdeleAlgebraModule A T hAway i`, with one common witness
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m` coupled to
`h`. Taking `m` prime gives the prime-to-p specialization. No independence of
these comparison witnesses is claimed.

## Restriction maps

For an actual test-scheme morphism `a : T' ⟶ T`,
`rationalTestRestrict_endAction` proves that rational restriction commutes with
each actual rational endomorphism of `A`. It is the previously proved
rational-Hom naturality equation specialized to endomorphisms.

`rationalTestRestrict_finiteAdeleAlgebraAction` and
`rationalTestRestrict_primeToFiniteAdeleAlgebraAction` prove compatibility with
the respective tensor-algebra actions. The proof uses tensor induction: a pure
tensor acts by the two commuting endomorphism and scalar actions, and each
commutes with restriction by its existing naturality theorem; the additive
case follows from additivity.

`finiteAdeleAlgebraTestRestrict A P i h a` bundles the rational restriction as a
linear map over the full tensor algebra, from the carrier at `T` to the carrier
at `T'`. `primeToFiniteAdeleAlgebraTestRestrict A i hAway a` does the same for the
away carrier and coefficient ring. Both `_apply` lemmas identify the underlying
map with `rationalTestRestrict`. Their `_id` and `_comp` lemmas prove, pointwise,

- restriction along an identity is the identity;
- for `b : T'' ⟶ T'`, restriction along `b ≫ a` first restricts along `a`, then
  along `b`.

These follow directly from the existing rational restriction laws, so the maps
are contravariant in the test scheme.

## Transport by test-scheme isomorphisms

For `e : T ≅ T'`, `finiteAdeleAlgebraTestIso A P i h e` is the full tensor-linear
equivalence from the carrier at `T` to the carrier at `T'` whose forward map is
restriction along `e.inv`. Its inverse is restriction along `e.hom`.
`primeToFiniteAdeleAlgebraTestIso A i hAway e` is the corresponding away
equivalence. The inverse laws use restriction of a composite and the two
categorical inverse identities.

For each family, `_apply` and `_symm_apply` identify the forward and inverse
maps. The `_refl` lemma identifies transport by the reflexive isomorphism with
the identity. If `f : T' ≅ T''`, the `_trans` lemma says that transport by
`e.trans f` first transports by `e`, then by `f`. Because the definition
restricts along inverses, this is covariant transport. The proof is the
contravariant restriction composition law applied to `e.inv` and `f.inv`.

These are algebraic maps on actual Tate carriers over arbitrary test schemes.
They establish no rational topology, geometric monodromy, pairing compatibility,
or invariant PEL level structure. They supply a prerequisite for transporting
frames across the canonical test-scheme isomorphisms in base-change coherence.
