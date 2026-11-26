# Local cyclic base change of prime degree from the σ-lift statements

Module `Langlands.BaseChange.LocalCyclicBaseChangeReductionStatement`, namespace
`Langlands.BaseChange`. The module contains one declaration, the proposition
`LocalCyclicBaseChangeReductionStatement` (universe parameters `uK uV`, in this order). It
states an implication and proves neither the implication nor any of its premises.

## The statement

`LocalCyclicBaseChangeReductionStatement.{uK, uV}` says: if the seven propositions below
hold, then `Langlands.Henniart.LocalCyclicBaseChangeStatement.{uK, uV}` holds (module
`Langlands.Correspondence.HenniartCyclicBaseChange`). The premises are hypotheses of the
implication, in the order of the table. Each one is imported from the published module of
its own name, and none is restated in this module. Every field universe of a premise is `uK`
and every representation-space universe is `uV`. These are the universes of the conclusion,
whose fields live in `Type uK` and whose representation spaces live in `Type uV`.

The premises are about σ-lifts for `GL_n`: `F` is a nonarchimedean local field of
characteristic zero, `E` a cyclic `F`-algebra (`IsCyclicAlgebra σ l`) with generator `σ` of
order `l`, and `IsSigmaLift σ l π hπ ρ hρ A c` says that the admissible representation `ρ`
of `GL_n(E)`, with the σ-intertwiner `A` and the constant `c`, is a σ-lift of the
admissible representation `π` of `GL_n(F)`. HL is Henniart–Lemaire (2011) and AC is
Arthur–Clozel (1989), see *Sources*.

| # | Premise, as instantiated | Content | Source |
| --- | --- | --- | --- |
| 1 | `SigmaLiftUniquenessStatement.{uK, uK, uV, uV, uV}` (parameters `u v uV uW uW'`) | Two irreducible admissible σ-lifts of the same irreducible admissible `π` are isomorphic, whatever their intertwiners and constants. | HL II.2.9, Remarque (2), printed p. 70; AC Ch. 1, Thm. 6.2 (a) and Lemma 6.3, pp. 51–52 |
| 2 | `SigmaLiftTwistStatement.{uK, uK, uV, uV}` (parameters `u v uV uW`) | Let `τ`, with intertwiner `A` and constant `c`, be a σ-lift of the admissible `π`, let `ω` be a continuous character of `Fˣ`, and write `πω = π ⊗ (ω ∘ det)` and `τω = τ ⊗ ((ω ∘ N_{E/F}) ∘ det)`. For any supplied admissibility proofs of `πω` and `τω` and any σ-intertwiner `Aω` of `τω` whose underlying map is that of `A`, `τω` with `Aω` and the same constant `c` is a σ-lift of `πω`. The premise does not produce these proofs or `Aω`; they are hypotheses. | HL II.2.9, Remarque (4), printed p. 70 |
| 3 | `DiscreteSeriesSigmaLiftStatement.{uK, uK, uV, uV}` (parameters `u v uV uW`) | For a field `E`: an irreducible admissible `π` that is essentially square-integrable (`JacquetLanglands.IsEssentiallySquareIntegrable`) has an irreducible admissible σ-lift (with some intertwiner and constant), which is a σ-discrete series if `π` is square-integrable. | HL II.4.6, Théorème (1), and II.4.7, printed pp. 88–89 |
| 4 | `SigmaLiftFibreStatement.{uK, uK, uV, uV, uV}` (parameters `u v uV uV' uW`) | For a field `E`: two irreducible admissible essentially square-integrable `π`, `π'` with a common irreducible admissible σ-lift `τ` (possibly with different intertwiners and constants) satisfy `π' ≅ (κ ∘ det) ⊗ π` for a character `κ` of `Fˣ` trivial on `N_{E/F}(Eˣ)`. | HL II.4.8, Lemme (2), printed p. 90, in the essentially square-integrable case |
| 5 | `CuspidalSigmaLiftStructureStatement.{uK, uK, uV, uV}` (parameters `u v uV uW`) | For a local field `E`, `n > 0`, an irreducible admissible supercuspidal `π` of `GL_n(F)` and an irreducible admissible `P` of `GL_n(E)` that, with some intertwiner and constant, is a σ-lift of `π`: with `s` the order of `normTwistStabilizer E π`, `s ∣ l`, and there are `n₁ > 0` with `s n₁ = n` and an irreducible supercuspidal `P₁` of `GL_{n₁}(E)` with `P₁^{σ^i} ≅ P₁` exactly when `s ∣ i`, such that `P` is isomorphic to `sigmaOrbitProduct σ s P₁` (that is, `P₁ × P₁^σ × ⋯ × P₁^{σ^{s-1}}`) reindexed along `s n₁ = n`. | HL II.4.12, Proposition, printed p. 96 |
| 6 | `CuspidalSigmaLiftExistenceStatement.{uK, uK, uV, uV}` (parameters `u v uV uW`) | Conversely, for a local field `E`, `n₁ > 0`, a natural number `s` and an irreducible supercuspidal `P₁` of `GL_{n₁}(E)` with `P₁^{σ^i} ≅ P₁` exactly when `s ∣ i`: the product `sigmaOrbitProduct σ s P₁` is irreducible and admissible, and, with some intertwiner and constant, a σ-lift of an irreducible admissible supercuspidal `π` of `GL_{s n₁}(F)` whose stabilizer `normTwistStabilizer E π` has `s` elements. | HL II.4.12, Remarque, printed p. 97, case `a = 1` |
| 7 | `CuspidalSigmaLiftConductorStatement.{uK, uK, uV, uV}` (parameters `u v uV uW`) | For a local field `E`, let `π` be an irreducible admissible supercuspidal representation of `GL_{k+1}(F)`, `P₁` an irreducible supercuspidal representation of `GL_{k₁+1}(E)` with `s (k₁ + 1) = k + 1`, and `P` an admissible representation of `GL_{k+1}(E)` isomorphic to `sigmaOrbitProduct σ s P₁` reindexed along that equality and, with some intertwiner `A` and constant `c`, a σ-lift of `π`. Then for every `f` with `IsResidueDegree F E f`, every `d` with `IsDifferentExponent F E d`, and every finite set `X` whose elements are exactly the homomorphisms `κ : Fˣ → ℂˣ` trivial on the norms (`IsNormTrivial E κ`), `∑_{κ ∈ X} a(π ⊗ κ ∘ det) = f (s · a(P₁) + (k + 1) d)` in `WithTop ℕ`, where `a` is `Conductor.firstFixedLevel`. | AC Ch. 1, Prop. 6.9 (ii), printed pp. 60–61: the specialization of its ε-factor product formula to `π` and the trivial character of `GL_1(F)`, read on conductor exponents, with the conductor taken as the first fixed level |

The universe parameters are listed in the order in which the published declarations take
them; `u` is the universe of `F` and `v` that of `E`. The names, universe orders and argument
forms are those of the published premises.

The conclusion `Langlands.Henniart.LocalCyclicBaseChangeStatement.{uK, uV}` says: for every
prime `p` and every cyclic step `S : Numerical.CyclicPrimeStep.{uK} p` of p-adic fields
there is a map `Ch : Numerical.CyclicBaseChangeMap.{uK, uV} S` with
`Numerical.IsWeakCyclicBaseChange S Ch`, that is, with the clauses (W1), (W2), (W3a)–(W3c)
and (W4) of that definition.

## Scope

The conclusion is input (I3) in the weak form of Option II of the numerical LLC route note
(source `operator-numerical-llc-route-2026-11-16`, §6.4, Theorem `thm:BC`, and §7.1 item 6),
as stated in `Langlands.Henniart.LocalCyclicBaseChangeStatement`. It concerns supercuspidal
classes only: `Ch k π` is a multiset of supercuspidal classes over the top field, of positive
ranks, and the conclusion asks only for some map with (W1)–(W4). It says nothing about
non-supercuspidal representations, character identities or the uniqueness of `Ch`.

This module does not prove (I3). It reduces (I3) to the seven premises, and the implication
is meaningful whether or not the premises are proved.

## Instantiation

A proof applies the premises to a step `S` as follows.

- `F = S.base.Carrier` and `E = S.top.Carrier`, with the algebra `S.algebra` and, on each
  field, the topology, valuative relation and local-field structure of its
  `canonicalTopologicalData`.
- `l = S.degree`, a prime, and `σ` any generator of `S.Gal`, a group of prime order and so
  cyclic.
- `IsCyclicAlgebra σ l` holds because `E/F` is a Galois field extension of degree `l` whose
  group is generated by `σ`: `E` is finite of dimension `l` and reduced, `σ` has order `l`,
  and the elements fixed by `σ` are those of `F`.
- `CharZero F` holds because `F` is a finite extension of `ℚ_p`.

## Route for a proof

The following is a plan for a proof of the implication, with the clause of the conclusion
that each step gives. It is not a claim that the steps or the comparisons they use have been
carried out.

Write `Ξ = S.normCharacters` and `n = k + 1`. The norm subgroup `N_{E/F}(Eˣ)` is closed of
index `l` in `Fˣ` (local class field theory), hence open. So every character of `Fˣ` trivial
on it is continuous, there are exactly `l` of them, and they form a cyclic group of prime
order. The stabilizer of a class `π` in `Ξ` is therefore trivial or all of `Ξ`.

1. **Definition of `Ch`.** Let `π` be a supercuspidal class of rank `k + 1`. A supercuspidal
   representation is essentially square-integrable, so premise 3 gives an irreducible σ-lift
   `P` of a representative, unique up to isomorphism by premise 1. Premise 5 writes
   `P ≅ Π₁ × Π₁^σ × ⋯ × Π₁^{σ^{s-1}}` with `s ∣ l`. Since `l` is prime, `s = 1` or `s = l`.
   Define `Ch k π` as the multiset of the classes of `Π₁^{σ^j}`, `j < s`, chosen as a function
   of the isomorphism class of `P`, so that two classes with isomorphic σ-lifts get the same
   value. For `s = l` it is `S.galoisOrbit` of the class of `Π₁`; for `s = 1` it is the
   singleton of the class of `P`.
2. **(W1).** Rank: `s (k₁ + 1) = k + 1`. Galois invariance: for `s = 1`, `P` is σ-stable
   because a σ-lift carries a σ-intertwiner, so every `g ∈ S.Gal` fixes its class; for
   `s = l`, the orbit multiset is invariant under every `g ∈ S.Gal` by reindexing the orbit.
3. **(W2).** Let `η ∈ Ξ` and let `P`, with intertwiner `A` and constant `c`, be the σ-lift
   of a representative of `π` from step 1. Premise 2 needs three supplied data, obtained as
   follows. The character `η ∘ N_{E/F}` is trivial, so the twist of `P` by
   `(η ∘ N) ∘ det` is `P` itself (`Langlands.twist_one`); its admissibility proof and a
   σ-intertwiner with the same underlying map as `A` are those of `P`, transported along this
   equality. The twist of the representative by `η ∘ det` is admissible because `η ∘ det` has
   open kernel (`Langlands.isAdmissible_twist_iff`, with `IsNormTrivial.isOpen_ker`). With
   these data, and the continuity of `η`, premise 2 shows that `P` is a σ-lift of the twist
   of the representative by `η`, with the same constant `c`. Both classes have the same σ-lift,
   hence the same value of `Ch`.
4. **(W3a), (W3b).** A trivial stabilizer gives `s = 1` and the full stabilizer gives `s = l`
   (premise 5). Equal values of `Ch` have the same number `s` of elements, and give isomorphic
   σ-lifts: for `s = 1` directly, and for `s = l` because the two first factors differ by a
   Galois conjugation `σ^j`, so that the second lift is isomorphic to `P ∘ σ^j ≅ P`. After
   transporting the lift data to a common representation, premise 4 shows that the two
   classes differ by a twist by a norm-trivial character. In the trivial-stabilizer case this
   gives the fibre description of (W3a), whose converse is (W2); in the full-stabilizer case
   the twist fixes the class, which gives the injectivity of (W3b). The rank and orbit
   clauses of (W3b) come from premise 5 with `s = l`: `l ∣ k + 1`, and `Π₁^{σ^i} ≅ Π₁` only
   for `l ∣ i`, so `Π₁` has trivial Galois stabilizer.
5. **(W3c).** Premise 6 with `s = 1` (a `Γ`-invariant `τ`) or `s = l` (a `τ₁` with trivial
   Galois stabilizer) gives a supercuspidal `π` whose σ-lift is the required product. For
   `s = 1`, `sigmaOrbitProduct_one_equiv` identifies the product with `τ`. For `s = l`,
   identifying `Ch k π` with `S.galoisOrbit τ₁` needs the uniqueness of supercuspidal
   support, `Langlands.GLSupercuspidalSupportUniquenessStatement`, proved in the Library as
   `Langlands.glSupercuspidalSupportUniqueness`.
6. **(W4).** Apply premise 7 to the admissible lift `P` of step 1 and the irreducible
   supercuspidal block `Π₁` that premise 5 provides, with `X` the finite set of norm-trivial
   characters and `f`, `d` the residue degree and different exponent of `E/F`. It gives
   `∑_η a(π ⊗ η) = f (s · a(Π₁) + (k + 1) d)` for the conductors `a` (first fixed levels).
   The conductors are finite by `Langlands.Conductor.supercuspidalPadicConductorExponent`
   (Jacquet–Piatetski-Shapiro–Shalika 1981, Théorème (5.1)), and Galois conjugation preserves
   the first fixed level, so the conductors of the elements of `Ch k π` add up to
   `s · a(Π₁)`. Subtracting the ranks in `ℤ` and using `l = e f` gives (W4) for the signed
   differences `a - rank`. The target uses the truncated difference in `ℕ`, which leaves two
   separate obligations.
   - *Lower bound.* `a ≥ rank` for supercuspidal representations of rank at least two,
     including level zero. In total rank at least two, a rank-one element of `Ch k π` lies in
     a free Galois orbit and so is ramified, because unramified characters are Galois
     invariant.
   - *Total rank one.* Truncation changes the value exactly at conductor zero, and the
     required correction is that the number of unramified norm twists of `π` is `f` if the
     lift is unramified and zero otherwise. One route: by (W3c) and premise 7, the minimum
     over `π` of `∑_η a(π ⊗ η)` is `f d`, attained exactly when the lift is unramified. On the
     other hand, this sum is minimal precisely for the twist cosets that contain an
     unramified character. The unramified norm characters form a subgroup of order `f`, by
     the valuation of norms, so such a coset contains exactly `f` unramified characters.

## Library comparisons the route needs

These comparisons are listed, not proved, here.

- *Essential square-integrability.* Premises 3 and 4 use
  `JacquetLanglands.IsEssentiallySquareIntegrable`; the p-adic predicate is
  `PadicField.TopologicalData.IsEssentiallySquareIntegrable`, for which
  `Langlands.RankinSelberg.supercuspidal_isEssentiallySquareIntegrable` proves essential
  square-integrability of supercuspidal representations. The module
  `Langlands.JacquetLanglands.PadicSquareIntegrabilityComparison` relates the two predicates
  (`isEssentiallySquareIntegrable_iff_padic`) and proves
  `padicSupercuspidalEssentialSquareIntegrability` for the first one.
- *Topologies.* `IsModuleTopology F E` for the canonical topologies of `S.base` and `S.top`.
- *Invariants.* `IsResidueDegree` and `IsDifferentExponent` (module
  `Langlands.BaseChange.ExtensionInvariants`) against `S.residueDegree` and
  `S.differentExponent`, and `l = e f` with `S.ramificationIndex`.
- *Classes and representations.* Supercuspidal classes (`SupercuspidalAutomorphicClass`,
  that is `PadicField.SupercuspidalClass`, isomorphism classes of smooth irreducible
  supercuspidal objects) against the representations with admissibility proofs used in the
  premises, with the rank transports `k.succPNat`, `k + 1` and `s * n₁`. The σ-lift relation
  is transported along isomorphisms on both sides by `IsSigmaLift.transport`.
- *Characters.* `Numerical.supercuspidalCharacterTwist` by a `QuasiCharacter` against
  `Langlands.twist` by `κ ∘ det`; `S.normCharacters` against the homomorphisms satisfying
  `IsNormTrivial E` (`IsNormTrivial.isOpen_ker` proves that their kernels are open over a
  complete nontrivially normed base field of characteristic zero); the finite sum
  `∑ᶠ η ∈ S.normCharacters` against the sum over `X`.
- *Galois conjugation.* `S.galoisConjugate` against composition with `entrywiseAut`.
- *Conductors.* `Numerical.conductor`, the first fixed level of a class, against
  `Conductor.firstFixedLevel` of a representative. At rank one the module
  `Langlands.Representation.Conductor.RankOneCharacterLevel` computes the level of a
  character. In rank at least two,
  `Langlands.BushnellKutzko.max_exponent_eq_of_isNormalizedLevel` with a comparison of
  conductors gives the lower bound `a ≥ rank` at positive normalized level, but not at
  level zero.

## Characteristic

The reduction uses only the characteristic-zero instances of the premises. Henniart–Lemaire
give the corresponding statements in positive characteristic as well; Arthur–Clozel,
Chapter 1, give the characteristic-zero comparison where applicable. The argument does not
use character integrability in positive characteristic.

## Sources

- HL: G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. Soc. Math. Fr. 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61` (PDF page =
  printed page + 8): II.1.3 (printed p. 56, the group `K(E/F)`), II.2.9, Remarques (2) and
  (4) (p. 70), II.4.6 and II.4.7 (pp. 88–89), II.4.8 (p. 90), II.4.12, Proposition (p. 96)
  and Remarque (p. 97).
- AC: J. Arthur and L. Clozel, *Simple algebras, base change, and the advanced theory of the
  trace formula*, Annals of Math. Studies 120 (1989), source ID
  `arthur-clozel-1989-base-change` (PDF page = printed page + 14): Chapter 1, Theorem 6.2 (a)
  and Lemma 6.3 (pp. 51–52), Proposition 6.9 (ii) (pp. 60–61).
- H. Jacquet, I. Piatetski-Shapiro and J. Shalika, *Conducteur des représentations du groupe
  linéaire*, Math. Ann. 256 (1981), Théorème (5.1), finiteness of the conductor.
- The numerical LLC route note, source ID `operator-numerical-llc-route-2026-11-16`
  (file `numerical-LLC-route.tex`): §6.4, Theorem `thm:BC` (properties (BC1)–(BC4)), and
  §7.1 item 6, the weak form of the base-change premise.
