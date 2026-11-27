# Reducing (CI1) for Henniart's candidate to classes of finite image

`Langlands.Correspondence.HenniartCandidateBaseChangeFiniteImageReductionStatement`
defines two predicates in `Langlands.Henniart.Numerical` and states three
propositions in `Langlands.Henniart`. Here `S : Numerical.CyclicPrimeStep.{uK} p`
is a cyclic extension \(M/L\) of prime degree between \(p\)-adic fields, with
\(L=\) `S.base`, \(M=\) `S.top` and residue degree \(f(M\mid L)=\) `S.residueDegree`.
`Ch : Numerical.CyclicBaseChangeMap.{uK, uV} S` takes a supercuspidal class
over \(L\) in rank \(k+1\) to a multiset of rank-tagged supercuspidal classes over
\(M\). The candidate `Extension.rankExtension` is Henniart's extension of the
stable images to arbitrary irreducible Weil classes in a rank where
`StableExistsAt` holds (Henniart 2000, §§4.1–4.4).

## Why the map must commute with twists

Full (CI1) compares the candidate with restriction at every irreducible Weil
class. `LocalWeil.unramifiedTwistFiniteFactoring` writes any such class as an
unramified twist \(z\cdot b_0\) of a unitary class \(b_0\) factoring through a
finite quotient of the absolute Galois group. `Extension.rankExtension_twist`
commutes the candidate with that twist. To transfer (CI1) from \(b_0\) to
\(z\cdot b_0\), the comparison must also commute the twist past `Ch`.

The clauses (W1)–(W4) of `Numerical.IsWeakCyclicBaseChange` include invariance
under norm-trivial twists and give no equivariance for arbitrary \(z\).
`Automorphic.Unramified.RestrictedCyclicBaseChangeCompatibilityStatement`
compares the chosen map with global base change at components of regular
algebraic cuspidal representations with unitary central character. For
example, a determinant twist of such a local component by \(|z|\ne 1\) loses
unitary central character. The restricted comparison supplies no formula
relating images under arbitrary complex twists. The norm-twist law (BC2) of
the numerical correspondence route note, §6.4, and Henniart–Lemaire II.2.9,
Remarque (4), give the local route through σ-lifts.

## Definitions

### `Numerical.IsUnramifiedTwistEquivariant.{uK, uV}`

For every `k`, every `z : ℂˣ` and every supercuspidal class `π` of rank `k + 1`
over \(L\), the equation is

```text
Ch k (supercuspidalUnramifiedTwist S.base k z π) =
  (Ch k π).map fun ρ =>
    ⟨ρ.1, supercuspidalUnramifiedTwist S.top ρ.1 (z ^ S.residueDegree) ρ.2⟩
```

`Numerical.supercuspidalUnramifiedTwist` uses \(g\mapsto
z^{\operatorname{ord}(\det g)}\). This is the determinant twist by the
unramified character of the field's multiplicative group with value \(z\)
at a uniformizer. Normalizing the integer orders to take value one at
uniformizers gives
\(\operatorname{ord}_L(N_{M/L}y)=f(M\mid L)\operatorname{ord}_M(y)\) for
\(y\in M^\times\). Thus the pullback through the norm has value \(z^f\) at a
uniformizer of \(M\). In the Library this order identity follows from
`LocalClassField.residueDegree_mul_ord_relative_norm` and the residue
cardinality relation `Weil.Local.extensionResidueCardinality`.
On the Weil side, `Weil.Local.localUnramifiedCharacter_extensionWeilMap`
restricts the character with value \(z\) at geometric Frobenius of \(L\) to
the character with value \(z^f\) at geometric Frobenius of \(M\).

### `Numerical.IsCandidateBaseChangeCompatibleOnFiniteImage.{uK, uW, uV}`

This is (CI1) for every `k`, every `hL : StableExistsAt S.base k.succPNat`
and every `σ : IrreducibleWeilClass S.base k.succPNat` admitting a witness
`b₀ : LocalWeil.UnitaryBasis S.base` with `b₀.val = ⟨k.succPNat, σ⟩` and
`StableMap.IsFiniteFactoring S.base b₀`. For every multiset `m` satisfying
`IsRestrictionDecomposition S σ m` and every `hm` giving `StableExistsAt`
over \(M\) in the rank of each member of `m`, the equation is

```text
Ch k (Extension.rankExtension S.base hL σ) =
  m.pmap (fun τ h => ⟨τ.1, Extension.rankExtension S.top h τ.2⟩) hm
```

The equality compares supercuspidal classes with their ranks and
multiplicities, as in `Numerical.IsCandidateBaseChangeCompatible`.

## Propositions

The universes `uK`, `uW` and `uV` are those of the \(p\)-adic fields, the Weil
representation carriers and the supercuspidal representation carriers,
respectively. Both propositions involving candidate existence use
`CandidateExistenceStatement.{uK, uW, uV, uW, uK}`. The fourth universe
indexes the local constant systems in the candidate's factor conditions.
It is set to `uW` to match `StableExistsAt.{uK, uW, uV, uW}` here. The
fifth is the universe of the finite quotients in `StableMap.IsStableImage`.

### `CandidateBaseChangeTwistReductionStatement.{uK, uW, uV}`

Assume candidate existence. For every prime `p`, every step `S` and every
map `Ch`, unramified-twist equivariance of `Ch` and (CI1) on classes of
finite image imply full (CI1).

The intended proof is local. Use `hL` and
`Extension.exists_stableDecomposition_of_rank` to write
\(\sigma=z\cdot b_0\). The stable-image witness makes \(b_0\) finite
factoring by `StableMap.IsStableImage.isFiniteFactoring`. Untwist each
member of the supplied restriction decomposition of \(\sigma\) by
\((z^f)^{-1}\). The Weil restriction identity gives a decomposition of
\(b_0\) with the same ranks, so the stable-existence hypotheses still
apply. Use (CI1) there and transport the equality back by equivariance
of `Ch` and `Extension.rankExtension_twist` over \(L\) and \(M\).
`Extension.unramifiedTwistIndependence_of_reciprocity` supplies the twist
independence premise from candidate existence and
`LocalClassField.commonClosureReciprocityExistence`.

### `CertifiedCyclicBaseChangeTwistEquivarianceStatement.{uK, uV}`

Assume `BaseChange.SigmaLiftUniquenessStatement.{uK, uK, uV, max uK uV, max uK uV}`.
For every prime `p`, every step `S`, every map `Ch` and every `σ : S.Gal`
with `σ ≠ 1`, certification by `BaseChange.IsSigmaLiftOnSupercuspidals`
for this `σ` implies unramified-twist equivariance. The uniqueness premise
uses `uK` for each field, `uV` for the base representation and `max uK uV`
for each of the two lift carriers supplied by the certification.

The intended proof is local. Apply certification to a representative of
`π` and to its twist. In each case `IsSupercuspidalSupport` ensures that
the certified lift is irreducible. By `BaseChange.sigmaLiftTwist`, twisting
the first lift by the norm pullback of the unramified character produces
another lift of the twisted representative. Uniqueness identifies it with
the second certified lift. The twist transports the first lift's supercuspidal
support constituent by constituent (`IsSupercuspidalSupport.characterTwist`), and
`Langlands.glSupercuspidalSupportUniqueness` identifies the two supports.
The norm-order identity gives exactly `z ^ S.residueDegree` in the
resulting multiset of classes.

### `CandidateFiniteImageBaseChangeCompatibilityReductionStatement.{uK, uW, uV}`

Assume candidate existence. For every prime `p`, every step `S` and every
map `Ch`, if `Ch` is a weak cyclic base change and is certified by σ-lifts
on supercuspidal classes for every nonidentity `σ : S.Gal`, then `Ch`
satisfies (CI1) on classes of finite image. Stable existence is required
in the ranks specified in that predicate.

This global proposition is not a published result. Source (b) in §6.5 of
the numerical correspondence route note gives an assessment of how (CI1)
should follow from Henniart's construction. The intended argument starts
by globalizing a finite Galois extension \(K'/L\) containing \(M\) with
full decomposition group at a finite place \(v\). The extension should
be large enough for the stable-image quotients for the class over \(L\)
and its restriction constituents over \(M\). The intermediate global field
corresponding to \(\operatorname{Gal}(K'/M)\) is cyclic over the global
base, with a unique place \(w\) over \(v\) and completion \(M\).

Construct compatible candidates from the local supports of the global
automorphic data and the data attached to their restrictions. Henniart
(2000), §3, uses Brauer induction and the weak automorphic inductions of
Harris (1998), Proposition 4.8, with the local unramified twist corrections
of §3.7. The cyclic transfer inputs B1–B3 and the rigidity input
C2 in the external-inputs plan are intended to identify the automorphic
data for restriction with the weak base change.
Clause N′ of `Automorphic.Unramified.CyclicStrongBaseChangeSupportStatement`,
from Arthur–Clozel III.5.1, compares their actual supports at \(v\) and \(w\)
using the certified `Ch`. This uses strong compatibility for unitary
isobaric data because finite-image Galois data need not yield regular
algebraic cuspidal representations. Extend the comparison of actual
supports additively over the Brauer combinations. Then
`StableMap.IsStableImage.exists_quotient` identifies the constructed
candidate values at the enlarged quotients with the stable images.
Taking the trivial unramified twist in `Extension.rankExtensionBasis_eq`
gives the values of `rankExtension` on these classes.

## Composition

Assume candidate existence, uniqueness of σ-lifts and a certified local
cyclic base-change existence result. For each step take the supplied weak
map `Ch` certified for all nonidentity elements. The Galois group has
prime order, so it contains a nonidentity element. Apply
`CertifiedCyclicBaseChangeTwistEquivarianceStatement` at that element.
Then `CandidateFiniteImageBaseChangeCompatibilityReductionStatement`
gives (CI1) on classes of finite image for the same `Ch`, and
`CandidateBaseChangeTwistReductionStatement` gives full (CI1). The weak
map together with full (CI1) supplies the witness of
`CandidateCompatibleWeakBaseChangeReductionStatement`. The three
propositions here are statement definitions.

## Sources

- *The numerical local Langlands correspondence for GL_n* (16 November
  2026), `operator-numerical-llc-route-2026-11-16`, `numerical-LLC-route.tex`,
  §6.4, Theorem `thm:BC`, (BC2), and §6.5, lines 1150–1174, especially source (b).
- *Formalizing the large external inputs of the local Langlands
  correspondence for GL_n* (16 November 2026),
  `operator-external-inputs-plan-2026-11-16`, `external-inputs-plan.tex`,
  interfaces B1–B3 and C2, E3 at lines 240–241, and §4.6, lines 704–773.
- Guy Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique* (2000), `henniart-2000-simple-proof`, §3
  (printed pp. 448–451) and §§4.1–4.4 (pp. 452–453).
- Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic
  field, \(n<p\)* (1998), `harris-1998-local-langlands`, Proposition 4.8
  and its proof (printed pp. 201–203).
- Guy Henniart and Bertrand Lemaire, *Changement de base et induction
  automorphe pour GL_n en caractéristique non nulle* (2011),
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
  II.2.7 (printed p. 67) and II.2.9, Remarques (2) and (4) (p. 70).
- James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the
  Advanced Theory of the Trace Formula* (1989), `arthur-clozel-1989-base-change`,
  Chapter I, §6, especially Definition 6.1 and Theorem 6.2 (printed p. 51),
  and Chapter III, Theorems 4.2 and 5.1 (pp. 202–203 and 212–213).
