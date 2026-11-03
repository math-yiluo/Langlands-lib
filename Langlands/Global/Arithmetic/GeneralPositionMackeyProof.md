# Exact stabilizers and irreducibility of all Mackey constituents

Worker 60 authored these group-theoretic helpers and their application to the
Library's actual Mackey constituents. The imported
`GeneralPositionInductionProof` is Worker 34's finite-coordinate
irreducibility argument. The two modules are internal components of the joint
proof of `Langlands.Global.GeneralPositionOfExactStabilizerStatement`.

The original source is Michael Harris, *The local Langlands conjecture for
GL(n) over a p-adic field, n < p* (1998), registered source
`harris-1998-local-langlands`, proof of Lemma 4.7, printed pp.204–205,
equation (4.12) and the following paragraph. The retained original TeX proof
was read directly. Harris asserts the sufficiency by Clifford–Mackey theory;
the coordinate separation and subgroup calculations below expand that step.
The source-folder `CORRECTION_SOURCE.md` concerns corrections to Harris's
1997 article contained in the 1998 paper. It does not alter this passage.

Let `N` be a normal subgroup of an arbitrary group `G`, and let `H` be a
subgroup containing `N`. Let `χ : H →* ℂˣ`, write `ψ` for its restriction to
`N`, and assume its exact stabilizer under `a(ψ)(n) = ψ(a⁻¹ n a)` is `H`.

For `K` containing `N` and every `g : G`, the theorem
`mackeyConstituent_irreducible_of_exactStabilizer` proves irreducibility of

\[
  \operatorname{Ind}_{g H g^{-1}\cap K}^{K} \bigl[x\mapsto\chi(g^{-1}xg)\bigr].
\]

This is the exact `GeneralPosition.mackeyConstituent` constructed in the
existing statement module. In Lean, its inducing subgroup is
`(conjugate H g).subgroupOf K`, the map to `H` is `conjugateRestriction`,
and induction is `FiniteRepresentation.induce`. The character line has
carrier `ULift.{0} ℂ`; its actual restriction along `conjugateRestriction`
is definitionally the character line of the composed homomorphism. Thus the
final proof applies the imported criterion to this actual representation.

The implemented steps are:

1. `conjugateCharacters_eq_iff` proves that the two homomorphisms
   `n ↦ ψ(a n a⁻¹)` and `n ↦ ψ(b n b⁻¹)` agree if and only if
   `a b⁻¹ ∈ H`. For the forward implication, evaluate equality after
   conjugation by `a⁻¹` and use exactness at `a b⁻¹`. For the converse,
   evaluate the stabilizer equality after conjugation by `a`.
   `conjugateCharacter_stabilizer` also records that conjugating `ψ`
   conjugates its exact stabilizer to `g H g⁻¹`.
2. `exactStabilizer_separation` turns this equality criterion into a
   witness `n : N` distinguishing each two distinct right cosets. The
   quotient relation tests membership of `b a⁻¹`; taking inverses
   reconciles this with the preceding membership condition.
   `induce_irreducible_of_exactStabilizer` applies Worker 34's criterion
   to prove irreducibility of the induced character of `G` itself.
3. `normal_le_conjugate` and `normal_subgroupOf_le_conjugate` place the
   normal subgroup inside every Mackey inducing subgroup.
   `mackeyCharacter_restriction` identifies the restricted character
   there with the restriction of the conjugated original character.
4. `mackeyCharacter_separation` proves separation inside `K` directly.
   If two coordinates indexed by `x,y : K` were indistinguishable on
   `N.subgroupOf K`, the inclusion `N ≤ K` would allow testing every
   `n : N`. The two conjugated homomorphisms indexed by `g⁻¹x` and
   `g⁻¹y` would then agree. Step 1 implies
   `g⁻¹ x y⁻¹ g ∈ H`, so `x y⁻¹ ∈ g H g⁻¹ ∩ K`. Taking its inverse
   equates the two right cosets, contradicting their distinctness.
5. The final theorem applies `induce_irreducible_of_separation` inside
   `K`, using its normal subgroup `N.subgroupOf K` and the just-proved
   separation.

The conjugation and separation helpers work with any group as codomain;
commutativity is not used in these calculations. The two irreducibility
theorems specialize to complex units. Only `H` has a finite-index premise;
the finite index of the actual Mackey inducing subgroup is obtained by
instance inference. The group universe is arbitrary. The character need
not have finite order, and no semisimplicity premise is supplied. The
result covers every `K` containing `N` and every `g`, including the two
endpoint subgroups needed for general position. The separate final
arithmetic module supplies the field tower and specializes these results
to the Galois-closure Weil subgroup.
