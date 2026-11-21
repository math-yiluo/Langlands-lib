# Reductions of both general-position prime branches of Proposition 4.8

`Proposition48PrimeBranchReductionStatement` and
`Proposition48PrimeBranchReductionTCStatement` end at the exact existing
`Proposition48PrimeBranchStatement` and `Proposition48PrimeBranchTCStatement`.
Both retain independent `uF` and `uV`. They use the named propositions in
`Proposition48PrimeBranchCommonInputs` and the corresponding named
conjugate self-duality implication. All seven foundations remain in each
published branch telescope. The concluding existential is `Q.HasSolution`
for the original `Q.ξ`.

## Actual child classes and the Mackey enumeration

From auxiliary validity take normality of the closure, the auxiliary
compatibility and the unique place of the closure over `Q.Ps.v`. Choose
its place on `D`. `finitePlacesAbove_subsingleton` makes this the unique
`w : FinitePlacesAbove D Q.Ps.v`. The prime cyclic step gives the Galois
and cyclic instances, and `IsCyclic.exists_generator` gives `σ` and its
generating property. Use `cyclicNormKernelCharacter` for `η` on `Q.E`.

`Proposition48MackeyFibreStatement` makes `D` a subfield of the identity
copy of `Q.E'` and identifies the double cosets with the restrictions of
automorphisms to `D`. Choose representatives with `IsMackeyEnumeration`,
including the identity in its fibre. At every representative choose the
actual `R, ν, χs, r, S, T` from the branch hypothesis and the field maps
of `IsAuxiliaryMackeyChild`. The raw transported realization is
`S.arithmeticComap e.symm`. `Proposition48MackeyChildTransportStatement`
provides its weak induction from the corresponding actual Mackey
character. `Proposition48CorrectedChildTransportStatement` pulls back the
actual corrected realization with correction `HeckeCharacter.comap e.symm ν`,
its regular algebraic infinity type and its norm-twisted inducing character.
The CSD and supercuspidal transport statements move those properties of
both realizations. The unique-place argument identifies the transported
auxiliary place with `w` in each case. For the identity use
`Proposition48PrimeOrbitBasepointStatement` to choose the field maps with
this place identity in its exact predicate.

If `a` restricts to `τ` on `D`, the shared Galois-conjugation statement
makes the `τ`-conjugate of the transported identity constituent a weak
induction of the Mackey character of `a`. The same-inducing-character
Euler formula gives cofinite equality with the raw child at `a`, and
Euler constituent recovery on singletons identifies their actual classes.
This also identifies the classes from any two representatives of the same
fibre, since their restrictions coincide. For corrected choices the
actual determinant multiples have the transported corrections. To
compare in one normalization, multiply one by the ratio of corrections.
The identity of the inducing characters after that correction and
constituent recovery, or transport of the equivalent determinant-twisted
models, identifies the resulting classes. The raw family is the one used
in the isobaric multiset.

## Actual monomial restriction and isobaric invariance

Set `b = [Q.E':Q.E] − 1`. The parent and the raw children have the
inherited parity `b`. Their inducing characters are unitary by
conjugate inversion on the CM fields. The actual isomorphisms transport
unitarity and algebraicity after the norm twist to the Mackey characters.
Choose the avatars of their algebraic norm twists by
`AlgebraicHeckeAvatarExistenceStatement` with one coefficient field and
embedding for the parent and all selected children. Use
`HeckeMonomialCollectionStatement` to construct the parent collection and
the collections of the constituent characters. Their weak associations
follow by comparing the unitarized Euler products with the weak induction
witnesses. Both sides use every place in `WeakInduction.inducedEulerPolynomial`,
with the exponent `f(w|v)` from the full place fibre.

`Proposition48MonomialMackeyRestrictionStatement` identifies the actual
restriction of the parent collection with the direct sum of the induced
collections indexed by the chosen representatives. Then
`FiniteDirectSumWeakAssociationStatement` gives the associated finite-sum
spectrum. Use `IsobaricEnumerationSpectralAttachmentStatement` to attach
that system, with its rank cast, to the actual multiset. Use
`IsobaricSpectralConjugationStatement` to attach the transported spectra to
the actual conjugate. `GaloisRestrictionEulerInvarianceStatement` identifies
their cofinite Euler polynomials via the action of a lift in the parent
representation. Apply the given rigidity and isobaric invariance premises.
These make the actual isobaric multiset stable, preserving multiplicity.
The isobaric construction uses actual classes identified by rigidity and
spectral presentations of those classes. The Frobenius calculation provides
the equality of the attached numerical systems.

Harris's Theorem 1.2 is the given source of weakly associated compatible
families for regular algebraic conjugate self-dual classes with the split
square-integrable witness. In the source route it supplies membership of
the corrected constituents in Harris's class of automorphic
representations with associated families. Here the actual weakly induced
presentations and the monomial construction give the compatible families
used in the proof directly. Theorem 1.2 remains an exact branch premise.
Its conclusion about a finite sum with excluded coefficient places is
weaker than the common-weight single-collection data used for the local
comparison, which is built separately.

## Distinct local constituents and the cyclic lift

At the identity, let `U` be the transported raw realization. The child
is CSD, so `ConjugateSelfDualUnitaryCentralCharacterStatement` over `R.E`
and `ArithmeticComapUnitaryCentralCharacterStatement` give an actual
unitary central character of `U`. Use the child supercuspidal witness and
its arithmetic transport, and choose a presentation `P` of `U` whose
local component at `w` is supercuspidal via
`IsoClass.hasSupercuspidalComponent_iff`.

Feed the exact branch's general-coefficient comparison and the basepoint
data to `Proposition48PrimeLocalDistinctnessStatement`. This gives actual
supercuspidal presentations for every power of `σ`, a pairwise injective
family of local classes and agreement with `P` at the zeroth index. Its
proof separates the common determinant normalization, the genuinely pure
local monomial comparisons of a common weight and the rank-one class
field theory case. It uses the forward comparison once both supercuspidal
witnesses are known. In particular the freeness assertion for positive
powers yields the required nonstability for cyclic induction and the
orbit lift. Using the cyclic generator, it yields nonstability under
every nonidentity automorphism. The isobaric multiset identified above is
the full orbit. One can see this by stability, the identity constituent,
and the full number of distinct orbit classes, or by the direct
representative transport comparison.

Apply the regular-induction premise to the actual `U`, `η`, `σ` and
freeness data. Use `Proposition48PrimeInductionStagesStatement` to obtain
weak induction of `Q.ξ` for its output `c`. This uses `D ≤ a(E')` for the
identity label, the original raw Mackey char and cofinite Euler comparison
in stages. The conjugate self-duality implication uses this weak induction,
`Q.ξ` conjugate inverse and the given version of rigidity. On a representative
of `c` the CSD unitarity statement gives its unitary central character.
`isUnitarizable_of_hasUnitaryCentralCharacter` gives the invariant form
for the unitary singleton. `CyclicInductionOrbitBaseChangeStatement`
provides the weak base change of that singleton to the **actual** orbit.
Apply the given orbit-lift uniqueness to this unitary datum to identify
it with the orbit-lift output. For each positive power the actual
presentation from the local distinctness statement has a local class
unequal to the basepoint class via injectivity and the zeroth identity.
These are the witnesses of the Henniart–Herb premise, which now gives
supercuspidality of `c` at `Q.Ps.v`.

## Original infinity type and both universe-polymorphic targets

The raw identity child inherits the parent's parity. Use its actual
weak induction and unitary central character in
`Proposition48AuxiliaryChildComplexParametersStatement`. It uses the TC
isobaric base-change existence and TC complex-place compatibility at the
successive fields of the child's normal closure tower, plus the TC
Hecke-family endpoint and TC Euler constituent recovery. These fields
are totally complex by extension of the CM base. The endpoint matches the
cofinite spectra with those of the rank-one norm-conjugate characters and
hence supplies the actual induced parameters. This gives the raw child's
existing `HasInducedComplexPlaceParameters` predicate, which is then
transported to `D` by the parameter part of the shared child transport.

Apply the regular induction clause of `CyclicWeakBaseChangeComplexPlaceTCStatement`
to the unitary `U`, its full nonstability and the weak induction `c`.
It calculates the complex parameter from the Langlands sum over the places
of `D` above each complex place of `Q.E`. The shared parameter stages
statement combines this sum with the sums over the child inducing field.
Then `Proposition48InducedParameterRegularAlgebraicStatement` with
`CuspidalComplexParameterBridgeTCStatement` uses the resulting original
induced parameter, the given relative regularity, the parent parity and
conjugate inversion to give regular algebraicity of `c`. Together with
the weak induction, CSD and the auxiliary component, this is `Q.HasSolution`.

In the unrestricted reduction, its rigidity and invariance premises apply
as stated. Its local use of the Euler constituent recovery premise at the
normal closure gives the TC Euler premise by restricting the field
quantifier. In the TC reduction the corresponding rigidity, invariance,
cyclic and Henniart–Herb calls use `IsCMField.isTotallyComplex` on the base
and `NumberField.isTotallyComplex_of_algebra` on all its finite extensions.
The final CSD implication comes from the matching rigidity premise in each
route. There is a separate exact reduction statement for each target.

## Sources

- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), `harris-1998-local-langlands`, Definition
  1.3(b), p. 186, Proposition 2.4 and (2.4.2), p. 194, and Proposition 4.8,
  pp. 201–203. TeX lines 1574–1614 for the Mackey induction, 1616–1628 for
  general coefficients, 1630–1644 for invariance and 1646–1664 for the prime
  orbit. The parity remark and normalization are pp. 191 and 195.
- J. Tate, *Number theoretic background*, 1979, `tate-1979-number-theoretic-background`,
  (2.3.5), p. 12, for the sum over every place above the base place.
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced
  Theory of the Trace Formula*, 1989, `arthur-clozel-1989-base-change`,
  III.4.2(c), III.5.1, III.6.2 and III.6.4 (pp. 202–203, 212, 215–217).
- M. Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  1999, Theorem 5.9(ii), (5.4)–(5.6), and Lemma 5.8, for comparison with
  matching pure weight at a supplied split supercuspidal component.
- G. Henniart and R. Herb, *Automorphic induction for GL(n) (over local
  non-Archimedean fields)*, 1995, Proposition 5.5, pp. 152–153.
