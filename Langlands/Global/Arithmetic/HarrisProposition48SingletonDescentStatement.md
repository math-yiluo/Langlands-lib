# Harris’s Proposition 4.8 in the singleton case

The four proposition definitions in `Langlands.Global.Harris` state the
Galois stability, central character, complex parameter, and descent selection
inputs of the singleton branch. Each is a derived consequence of the arguments
and results cited below. The propositions (G) and (L16) use totally complex
spectral rigidity, with totally complex isobaric invariance in (G) and
totally complex cyclic descent in (L16).

The primary source is M. Harris, *The local Langlands conjecture for
GL(n) over a p-adic field, n < p*, Invent. Math. 134 (1998), 177–210
(`harris-1998-local-langlands`).

## Singleton Mackey data

A `Proposition48Problem` `Q` supplies the CM fields `E` and `E'`, the tower
`E ⊆ E' ⊆ L`, and the Hecke character `ξ = Q.ξ` of `E'`. Write `D` for an
intermediate field of `L/E`. For `IsNormalClosure Q.E Q.E' Q.L`, `L` is the
normal closure of `E'/E` and `L/E` is Galois. The type `Q.MackeyIndex D`
consists of double cosets `Gal(L/D) \ Gal(L/E) / Gal(L/E')`, using the
image of `E'` in `L`. The hypothesis `Nat.card (Q.MackeyIndex D) = 1`
allows the identity automorphism `1` of `L/E` as the representative.
Then `Q.mackeyField D 1 = D ⊔ Q.conjugateField 1` is the compositum
`M = D · E'` in `L`, with `E'` identified with its actual copy there.
`Q.mackeyCharacter D 1` pulls `ξ` back through that identification and
the idele class norm, giving `ξ ∘ N_{M/E'}`.

`Q.IsMackeyConstituent D 1 S.isoClass` says the class of the rank `r + 1`
cuspidal realization `S` over `D` is weakly induced from `Q.mackeyCharacter D 1`.
The underlying `IsWeakAutomorphicInductionOf` requires a spectral system from
an actual cuspidal presentation. The rank equals the degree of the inducing
extension and the system satisfies the induced Euler polynomial identity at
almost all finite places. This is Harris’s Definition 1.3(b) (p. 186,
PDF p. 10) in the case of induction from a character. The compact additive
adele quotient of `D` used for cuspidal realizations is supplied by
`compactSpace_adeleQuotient D`.

## (G) `Proposition48SingletonMackeyGaloisStableTCStatement`

Assume `CuspidalSpectralRigidityTCStatement`, which gives power-trace
independence and constituent recovery from power traces or Euler polynomials
over totally complex number fields. Assume also
`Proposition48IsobaricInvarianceTCStatement`, which uses that rigidity
to infer stability of a cuspidal multiset from equality of its Euler system
with the conjugate system. For the singleton Mackey data with `L` a normal
closure and any realization `S` as above, the conclusion says that
`S.isoClass.IsGaloisStable σ` for every `E`-automorphism `σ` of `D`.
This is arithmetic transport of the cuspidal class along `σ` back to itself,
or `S ≅ S ∘ σ⁻¹`.

Let `H = Gal(L/D)` and `K = Gal(L/E')`. The single double coset gives
`Gal(L/E) = H K`, so the degree formula with `H ∩ K = Gal(L/M)` gives
`[M : D] = [E' : E]`. Thus `D` and `E'` are linearly disjoint over `E`.
By normality an `E`-automorphism `σ` of `D` extends to `g ∈ Gal(L/E)`.
Write `g = h k` with `h ∈ H` and `k ∈ K`. Since `g` preserves `D` and `h`
fixes `D` pointwise, `k = h⁻¹ g` preserves `D` and restricts to `σ`.
It fixes `E'`, so it preserves `M` and the norm to `E'` is invariant under
its action. Thus `k` fixes `ξ ∘ N_{M/E'}`. Arithmetic transport
reindexes the unramified Euler factors, so the transported realization
is weakly induced from the same character and its Euler polynomials agree
with those of `S` almost everywhere. Since `D` contains the CM field `E`,
it is totally complex. Apply totally complex isobaric invariance with
totally complex rigidity to the one-constituent isobaric data of `S` to
obtain the asserted isomorphism.

This is the singleton specialization of the Galois-invariance argument in
Harris (1998), Proposition 4.8, printed pp. 202–203 (PDF pp. 26–27). Harris
uses strong multiplicity one on the whole isobaric spectrum. Here the
singleton character and its norm directly supply the Euler comparison. The
result gives the stability hypothesis for B1.

## (U) `WeakBaseChangeUnitaryCentralCharacterStatement`

Let `F` and `E` be number fields with an `F`-algebra structure on `E` and
compact additive adele quotients. Let `S` over `F` and `T` over `E` be
cuspidal realizations of the same positive rank `r + 1`.
`HasUnitaryCentralCharacter T` means a continuous complex idele class
character of absolute value one gives the scalar action of the center on
`T`. The predicate `T.isoClass.IsWeakBaseChangeOf S.isoClass` is witnessed
by spectral systems of actual presentations in arithmetic weak base
change. At almost every finite `v` of `F`, for every `w` above `v`, those
systems are defined, the extension is unramified at `w`, and the Satake
multiset at `w` is the `f(w|v)`-th power of the multiset at `v`, counted
with multiplicities. The conclusion is `HasUnitaryCentralCharacter S`.

Schur’s lemma gives central characters `ω_S` and `ω_T`
(`OperatorRealization.existsUnique_hasCentralCharacter`).
At a good place, the scalar matrix of a local uniformizer acts by the
product of the Satake parameters. Taking products in the weak
base change identity gives
`|ω_T(ϖ_w)| = |ω_S(ϖ_v)|^{f(w|v)}`. The positive character `|ω_S|`
is trivial on the compact norm-one idele classes because the positive
reals under multiplication have no nontrivial compact subgroup.
The idelic norm onto the positive reals therefore gives `|ω_S| = ‖·‖^t`
for some real `t`. At one such good place, unitarity upstairs yields
`1 = q_v^{-t f(w|v)}`, where `q_v > 1` and `f(w|v) > 0`. Hence `t = 0`.

This consequence uses the weak base change formula in Arthur–Clozel,
*Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
(1989, `arthur-clozel-1989-base-change`), Chapter III, Definition 1.1
(p. 199), the unramified central scalar calculation, and compactness of the
norm kernel. It gives the central character hypothesis downstairs for the
singleton branch’s local comparisons.
[CentralCharacterTopCoefficient](../../Automorphic/CentralCharacterTopCoefficient.md) and
[NormOneIdeleClassCompact](../NormOneIdeleClassCompact.md).

## (P1) `Proposition48SingletonInducedParameterStatement`

Use the normal closure and singleton hypotheses above. The inclusion
`D ≤ Q.mackeyField D 1` supplies the `D`-algebra on `M`. Let `v` be a
complex place of `E` and `w` an actual place of `D` above `v`.
`complexPlaceAbove v w` packages `w` with proof that it is complex.
An enumeration `e : Fin d ≃ InfinitePlacesAbove M w` lists the places
of `M` above `w`. At each such `w'`, supply a block `dξ w'` of
`ComplexCharacterData` and a proof that it is the actual parameter of
the Mackey character at the complex place packaged by
`complexPlaceAbove (complexPlaceAbove v w) w'`. The list `ds` is assumed
to be a permutation of `complexPlaceLanglandsSum` for this enumeration
with one block at each `w'`. The sum transports each list to the
selected coordinates of `w` and concatenates the lists in the order
of `e`. `complexPlaceParameterTransport` applies complex conjugation
to each block when the selected embedding upstairs restricts to the
conjugate of the selected embedding downstairs. This changes the sign
of each angular weight and retains its exponent.

The conclusion `Q.IsInducedComplexPlaceParameter v
(complexPlaceParameterTransport v w ds)` says the transported list is
the corresponding permuted sum of actual parameters of `ξ` at all the
places of `E'` above `v`, in some enumeration. Indeed the singleton
degree calculation gives `M ≅ D ⊗_E E'`. With the selected embedding
of `D` at `w` fixed, extending it to `M` and restricting to `E'`
identifies places over `w` with places of `E'` over `v`. The local
norm to the restriction of `w'` in `E'` is the inverse of the completion
map, which is an isomorphism of degree one at these complex places.
Thus the parameter of `ξ ∘ N` at `w'` is the parameter of `ξ` there
read in the coordinates at `w'`. The two ways of reading this block at
`v`, through `w` and through the restriction of `w'` to `E'`, have the
same conjugation parity. Restriction of embeddings composes and complex
conjugation is an involution. Transporting the sum therefore produces
the induced list at `v` up to permutation.

This derives the parameter identity for the branch from Harris’s
Langlands sums (2.4.1) and (2.4.2) (p. 193, PDF p. 17) and the
Mackey restriction in the proof of Proposition 4.8
(pp. 201–203, PDF pp. 25–27).
It converts the child’s parameter list, transported down by restricted
B7(1), into the list induced from `Q.ξ` in the normalization fixed by
the Library’s archimedean bridge.

## (L16) `Proposition48SingletonDescentSelectionTCStatement`

In addition to `CuspidalSpectralRigidityTCStatement`, assume
`CyclicStableDescentTCStatement` (B1), which describes the cuspidal
descents of a stable cuspidal class with unitary central character over
a cyclic extension of a totally complex field. Assume
`Harris1998Theorem12CuspidalStatement` (Theorem 1.2), which associates
a sum of pure compatible λ-adic families of the correct rank to a
regular algebraic conjugate self-dual cuspidal class over a CM field
`E = E₀ K₀`. Here `E₀` is totally real and `K₀` imaginary quadratic.
The theorem requires a square-integrable component at a place whose
rational residue prime splits in `K₀`.

The one-place validity predicate `Q.IsAuxiliaryValid` supplies
normalized reciprocity, the split imaginary quadratic subfield `K₀`,
the scalar tower and normal-closure conditions, and the compatible
auxiliary place datum `Q.Ps` above `p`. Its completion identifications
link `E`, `E'`, and `L` at the chosen places to `F`, `F'`, and the
local Galois closure. It requires unique places above the auxiliary
place `Q.Ps.v` and its conjugate in `L`. The auxiliary Weil character
from `Q.χs` is in general position, `ξ` has the prescribed component
`Q.χs` at `Q.Ps.v'`, and `ξ` is relatively regular and
conjugate-inverse. Relative regularity means that the complex
components above each place of `E` are pairwise distinct in the
coordinates of that place. Conjugate-inverse means `ξ ∘ c = ξ⁻¹`
for the CM involution. The predicate supplies algebraicity after
the twist by `‖·‖^(([E' : E] − 1)/2)`, as in Harris, p. 195.

`Q.IsPrimeCyclicStep D` says that `D/E` is Galois, its automorphism
group is cyclic, and `ℓ = [D : E]` is prime. The singleton Mackey
hypothesis gives `M` and its character as above. The statement makes
the CM structure on `D` explicit. It takes a rank `r + 1` cuspidal
realization `S` with unitary central character whose class is both a
Mackey constituent and stable under every `E`-automorphism. Its class
is also `IsConjugateSelfDual`, meaning a full operator realization is
isomorphic to its contragredient composed with the CM involution.
Each class over `E` of which `S` is a weak base change is assumed
`IsRegularAlgebraic`, meaning a representative has the infinitesimal
character of an irreducible algebraic representation. It also has a
`HasSupercuspidalComponent` witness, an actual spectral presentation
with supercuspidal local component at `Q.Ps.v`.

B1 gives exactly the `ℓ` descents `c ⊗ η^i`, for the norm-kernel Hecke
character `η` of order `ℓ` and `0 ≤ i < ℓ`, with twists through the
determinant. The kernel of `η` is the image of the idele-class norm from `D`.
As in Lemma 1.6, weak base change commutes with conjugation and
contragredients. The conjugate contragredient of a descent is therefore
another descent, hence a twist by a power of `η`. Since `D/E`
comes from the extension of the maximal totally real subfields, this
power has the form `η₀ ∘ N_{E/E₀}`. A finite-order character `α`
extending `η₀` satisfies `α · (α ∘ c_E) = η₀ ∘ N_{E/E₀}`, where
`c_E` is CM conjugation. Harris obtains the extension on the compact
idele-class quotient by the archimedean factors. Twisting the descent
by `α` makes it conjugate self-dual and preserves both regular algebraicity
and supercuspidality. By the argument of (U) the descent has a unitary
central character, which the finite-order twist preserves. The unitary
supercuspidal component is square-integrable modulo the center, and
the splitting condition at this place comes from `IsAuxiliaryValid`.
Apply Theorem 1.2 to the twist and undo the finite-order twist on the
λ-adic side.

Harris uses a rank-one λ-adic family `σ'` for the inducing character.
Obtaining it is part of the selection argument. The Library defines
`IsLambdaAdicRealization` for Hecke characters, with constructions for
finite-order characters. In rank one Theorem 1.2 can supply an
attachment to a cuspidal realization of `ξ` when the character is
algebraic and conjugate-inverse in that rank’s normalization and the
other hypotheses of the theorem are verified. In general the
algebraicity provided here is for the norm twist above. The usual
λ-adic construction for algebraic Hecke characters supplies an attachment
to that twist, as discussed after Theorem 1.7 (p. 191, PDF p. 15).
The conjugate-inverse condition makes `ξ` unitary because its absolute
value is a norm power that is fixed by CM conjugation and equals its own
inverse. The unitary normalization of the rank-one family’s Euler
factors therefore recovers the character `ξ`.

The monomial family over `D` is the induction from `M` of the
restriction of `σ'`, corresponding by norms to `ξ ∘ N_{M/E'}`.
Relative regularity distinguishes its conjugate inducing characters
over a common normal closure by their infinity types, so the induced
family is irreducible by Mackey’s criterion. Its unitary Euler factors
match those of `S` by weak induction. Weak base change gives the same
match for the restriction of a descent’s family. Harris’s comparison
uses Chebotarev after passing to a common arithmetic normalization
of the pure families. The passage between the two normalizations is
accounted for by the weights (Harris, p. 184, PDF p. 8). In that
normalization the semisimple restriction of the descent’s family to
the absolute Galois group of `D` is the monomial family.
The extensions of an irreducible representation through the cyclic
quotient are the `ℓ` twists of one extension by the quotient
characters. The singleton Mackey formula makes
`Ind_{E'}^{E} σ'` one of those extensions. The corresponding descent
has the weakly induced Euler factors of `ξ`. This gives the
existential conclusion, a class `c` for which `S` is a weak base
change of `c` and `c.IsWeakAutomorphicInductionOf Q.ξ`.

This is the descent-selection consequence of Harris’s Lemma 1.6
and proof (printed pp. 188–189, PDF pp. 12–13), as invoked in the
singleton case of Proposition 4.8 (p. 203, PDF p. 27). The underlying
attachment is Theorem 1.2 (p. 185, PDF p. 9). B1 is the stable
cuspidal descent of Arthur–Clozel, Chapter III, Lemma 6.3 (p. 217)
and Theorem 4.2(d) (p. 202) in prime degree.
Harris cites Lemma III.6.4 for the adjacent prime-orbit case.
The Library records the two forms of B1.
[CyclicTransferStatement](../../Automorphic/Unramified/CyclicTransferStatement.md) and
[CyclicTransferInputsTCStatement](../../Automorphic/Unramified/CyclicTransferInputsTCStatement.md).
Harris obtains conjugate self-duality of the selected class by
strong multiplicity one from `ξ ∘ c_E = ξ⁻¹`, where `c_E` extends
to the inducing CM field by its own CM involution. In the branch
this is a separate consequence of
`WeakInductionConjugateInverseSelfDualTCStatement`.

## Use in the singleton branch

1. Use `Proposition48MackeyChildTransportStatement` (module
   `HarrisProposition48MackeyTransportStatement`) to
   transport the child at `a = 1` to a Mackey constituent `S` over `D`
   with the child’s induced complex-place parameters.
   `ConjugateSelfDualUnitaryCentralCharacterStatement` (module
   `HarrisAuxiliaryConjugatePairStatement`) gives
   a unitary central character for the conjugate self-dual child.
   The arithmetic transport statements of
   `CuspidalArithmeticTransportStatement` preserve the unitary
   central character, supercuspidal component and conjugate self-duality.
   Part (G) gives Galois stability and B1 gives the descents of `S`.
2. For each descent, (U) gives a unitary central character.
   The statements of `HarrisAuxiliaryConjugatePairStatement` give
   supercuspidality of `S` at the conjugate auxiliary
   place by conjugate self-duality, and show that the places in the
   pair are distinct by splitting in `K₀`. B5 gives supercuspidality
   of each descent at `Q.Ps.v` and its conjugate. Restricted B7(1) compares the
   complex-place parameters across this step on these unitary
   cuspidal classes with the auxiliary supercuspidal components.
   Part (P1) then gives `Q.HasInducedComplexPlaceParameters` for the
   descent, an actual parameter of the class of the induced form at
   every complex place of `E`.
3. `Proposition48InducedParameterRegularAlgebraicStatement`
   gives regular algebraicity through `CuspidalComplexParameterBridgeTCStatement`.
   Together with B5 at `Q.Ps.v`, this gives the hypotheses on every
   descent for (L16). Apply (L16) and then
   `WeakInductionConjugateInverseSelfDualTCStatement` to obtain the
   required weak induction with conjugate self-duality.

The ordinary branch specializes rigidity to the totally complex
input. Ordinary rigidity and ordinary isobaric invariance together
give the totally complex isobaric invariance input.

The project route follows Section 4.8, Remark 4.2 (lines 859–894) and
the singleton discussion (line 909) of `external-inputs-plan.tex`
(`operator-external-inputs-plan-2026-11-16`). In this design the singleton’s
parameters are obtained through restricted B7(1). Its unitary central character
and auxiliary conjugate-pair supercuspidality hypotheses explain
the use of (U) before the comparison and of (P1) to obtain the
induced form afterward.
