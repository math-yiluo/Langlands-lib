# Isobaric invariance in Harris's Proposition 4.8: proof from spectral rigidity

Author: Worker 998, under Task 7220 `549b134f-cd9d-42ad-94bc-2d2ff16386c1`.

The theorem `Langlands.Global.Harris.proposition48IsobaricInvariance.{uV}`
proves exactly the published statement
`Langlands.Global.Harris.Proposition48IsobaricInvarianceStatement.{uV}`
(module `Langlands.Global.Arithmetic.HarrisProposition48IsobaricInvarianceStatement`),
for an arbitrary local-factor universe `uV`. The module imports only that
statement module and changes no published declaration. Its single
auxiliary lemma, `univ_map_eq_of_equiv`, is private. The kernel check
reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

This is a conditional theorem. The deep premise
`CuspidalSpectralRigidityStatement.{0, uV}` stays a hypothesis of the
target, and nothing here proves it. Its proof belongs to Task 6446
`c4f0be57-1a49-4a42-b813-4354e297ab3f`.

## Implemented proof

The proof introduces the rigidity hypothesis `hR`, the fields `F` and
`K` with their instances, the automorphism `σ`, the isobaric data `D`,
the spectral systems `s` and `t`, the two attachments `hs` and `ht`, and
the Euler equality `hst : s.SameEulerPolynomials t`.

1. **Unpacking the attachments.** By the definition of
   `IsobaricData.HasSpectralSystem`, `hs` supplies a length `p`, an
   enumeration `c : Fin p → PositiveRankCuspidalClass K` with
   `Finset.univ.val.map c = D`, and spectral systems `s₀ j` attached to
   the classes `c j` through genuine spectral presentations
   (`PositiveRankCuspidalClass.HasSpectralSystem`). It also gives
   `(SpectralSystem.finiteSum s₀).SameEulerPolynomials s`. Similarly,
   `ht` supplies `q`, `d : Fin q → PositiveRankCuspidalClass K` with
   `Finset.univ.val.map d = D.galoisConj σ`, attached systems `t₀`, and
   `(SpectralSystem.finiteSum t₀).SameEulerPolynomials t`.
2. **Chaining the Euler equalities.** `SameEulerPolynomials.trans` and
   `SameEulerPolynomials.symm` combine these equalities with `hst`. The
   result is
   `(SpectralSystem.finiteSum s₀).SameEulerPolynomials (SpectralSystem.finiteSum t₀)`.
   All three relations use the Library's single convention: equality on
   a cofinite set of finite places, wherever both systems are
   unramified. Transitivity keeps that convention, so the exceptional
   sets are never fixed or enlarged by hand.
3. **Constituent recovery.** The third conjunct `hR.2.2` of the
   rigidity hypothesis is
   `CuspidalEulerConstituentRecoveryStatement.{0, uV}`. The proof applies
   it over the number field `K : Type`, at lengths `p` and `q`, to the
   lists `c` and `d` with their attached systems `s₀` and `t₀`. It yields
   a bijection `e : Fin p ≃ Fin q` with `c i = d (e i)` for every `i`.
   The other two conjuncts, power-trace independence and power-trace
   recovery, are not used.
4. **Multiset equality.** The private lemma `univ_map_eq_of_equiv`
   rewrites `c` as `d ∘ e`. Mathlib's `Multiset.map_map` and
   `Multiset.map_univ_val_equiv` then show
   `Finset.univ.val.map c = Finset.univ.val.map d`. Reindexing by a
   bijection keeps each class's multiplicity. Thus
   `D.galoisConj σ = map d = map c = D`, which is
   `D.IsGaloisStable σ` by definition.

## Scope

- Multiplicities are kept. The enumerations list each constituent as
  often as it occurs, and the conclusion is equality of multisets, not
  of their supports.
- Constituent ranks are arbitrary positive integers and may be mixed.
  The recovery clause concerns lists of `PositiveRankCuspidalClass K`
  of any ranks. The proof does not identify `D.rank` with
  `(D.galoisConj σ).rank`, because `SameEulerPolynomials` compares
  systems of possibly different ranks.
- No unitarity is assumed. The classes need not be unitarizable, and
  `IsobaricData.IsUnitary` is not used.
- The base field `F`, the algebra `F → K` and the automorphism `σ` are
  arbitrary. The proof uses `σ` only through the attachment `ht` to
  `D.galoisConj σ`. The same argument shows that any two isobaric data
  with attached systems whose Euler polynomials agree outside a finite
  set are equal. Galois invariance is the case `D' = D.galoisConj σ`.
- The isobaric multiset itself is the object proved invariant. No
  realized isobaric representation replaces it, and no single-class
  strong-multiplicity-one statement is used.

## Source correspondence

The step comes from M. Harris, *The local Langlands conjecture for GL(n)
over a p-adic field, n < p*, Invent. Math. 134 (1998), 177–210
(registered `harris-1998-local-langlands`, PDF SHA-256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`).
It appears in the proof of Proposition 4.8, printed p.202 (one-based PDF
p.26), companion `math_9611226v1.tex` lines 1630–1644. Harris notes that
the family `Σ_{t-1}` weakly associated to
`Π_{t-1} = ⊞_{a ∈ A_{t-1}} Π(a, t-1)` is the restriction of a family over
`E`, and hence `Gal(E_{t-1}/E)`-invariant. He concludes in lines 1641–1644:
"The weakly associated isobaric representation `Π_{t-1}` is thus also
`Gal(E_{t-1}/E)`-invariant, by strong multiplicity one."

The Lean proof formalizes this last inference. Harris's appeal to strong
multiplicity one for isobaric representations is replaced by the
Library's Euler constituent-recovery clause. The Library states that
clause as the Euler-polynomial form of the numerical recovery step in
Jacquet–Shalika's Theorem 4.4. It recovers the full list of cuspidal
constituents, with multiplicity, from the Euler product. The
attached systems `s` and `t` correspond to the families weakly
associated to `Π_{t-1}` and its conjugate. The hypothesis `hst` is the
Galois invariance of `Σ_{t-1}` that Harris obtains by restriction.
Constructing the attachments and proving `hst` from the restricted
monomial family are obligations of the Proposition 4.8 branch inputs,
not of this theorem. This split matches the statement's paired
Markdown.
