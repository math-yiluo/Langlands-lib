# Isobaric invariance in Harris's Proposition 4.8 over totally complex fields: proof

Author: Worker 998, under Task 7220 `549b134f-cd9d-42ad-94bc-2d2ff16386c1`.

The theorem `Langlands.Global.Harris.proposition48IsobaricInvarianceTC.{uV}`
proves exactly the published statement
`Langlands.Global.Harris.Proposition48IsobaricInvarianceTCStatement.{uV}`
(module `Langlands.Global.Arithmetic.HarrisProposition48ReductionTCStatement`),
for an arbitrary local-factor universe `uV`. The module imports only that
statement module and changes no published declaration. Its single
auxiliary lemma, `univ_map_eq_of_equiv_tc`, is private. The kernel check
reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

This proof is self-contained. It does not derive the companion from the
unrestricted theorem `proposition48IsobaricInvariance`, and it could not.
The companion's premise `CuspidalSpectralRigidityTCStatement.{0, uV}`
asserts rigidity only over totally complex number fields. It is
therefore weaker than the unrestricted
`CuspidalSpectralRigidityStatement.{0, uV}` assumed by that theorem.
The premise stays a hypothesis here. Its proof belongs to Task 6446
`c4f0be57-1a49-4a42-b813-4354e297ab3f`.

## Implemented proof

The argument is the one in the unrestricted proof
`HarrisProposition48IsobaricInvarianceProof`, run with the totally
complex rigidity clause. The proof introduces the hypothesis `hR`, the
fields `F` and `K` with their instances, including
`[NumberField.IsTotallyComplex K]`, the automorphism `σ`, the isobaric
data `D`, the systems `s` and `t`, the attachments `hs` and `ht`, and
`hst : s.SameEulerPolynomials t`.

1. **Unpacking the attachments.** `hs` supplies an enumeration
   `c : Fin p → PositiveRankCuspidalClass K` with
   `Finset.univ.val.map c = D`. It also supplies systems `s₀ j` attached
   to the classes `c j` through genuine spectral presentations, with
   `(SpectralSystem.finiteSum s₀).SameEulerPolynomials s`. Likewise `ht`
   supplies `d : Fin q → PositiveRankCuspidalClass K` with
   `Finset.univ.val.map d = D.galoisConj σ`, attached systems `t₀`, and
   `(SpectralSystem.finiteSum t₀).SameEulerPolynomials t`.
2. **Chaining the Euler equalities.** `SameEulerPolynomials.trans` and
   `SameEulerPolynomials.symm` give
   `(SpectralSystem.finiteSum s₀).SameEulerPolynomials (SpectralSystem.finiteSum t₀)`.
   They keep the Library's single convention: equality on a cofinite set
   of finite places, wherever both systems are unramified.
3. **Constituent recovery.** The third conjunct `hR.2.2` is
   `CuspidalEulerConstituentRecoveryTCStatement.{0, uV}`. The proof
   applies it over `K : Type`. The required
   `[NumberField.IsTotallyComplex K]` instance is the target's own
   hypothesis on `K`. The result is a bijection `e : Fin p ≃ Fin q` with
   `c i = d (e i)` for every `i`.
4. **Multiset equality.** The private lemma `univ_map_eq_of_equiv_tc`
   rewrites `c` as `d ∘ e`. `Multiset.map_map` and
   `Multiset.map_univ_val_equiv` then give
   `Finset.univ.val.map c = Finset.univ.val.map d`, so
   `D.galoisConj σ = D`, which is `D.IsGaloisStable σ`.

## Scope

The conclusion is multiset equality with multiplicities. Constituent
ranks may be any mixed positive integers. Unitarity is not assumed. The
base field `F`, the algebra `F → K` and `σ` are arbitrary, and `σ` enters
only through the attachment `ht`. Only the Euler constituent-recovery
clause of the rigidity hypothesis is used. No realized isobaric
representation or single-class strong-multiplicity-one statement is
used.

## Source correspondence

The source step is the same as for the unrestricted theorem: M. Harris,
*The local Langlands conjecture for GL(n) over a p-adic field, n < p*,
Invent. Math. 134 (1998), 177–210 (registered
`harris-1998-local-langlands`, PDF SHA-256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`). It
is in the proof of Proposition 4.8, printed p.202 (one-based PDF p.26),
`math_9611226v1.tex` lines 1630–1644. Lines 1641–1644 read: "The weakly
associated isobaric representation `Π_{t-1}` is thus also
`Gal(E_{t-1}/E)`-invariant, by strong multiplicity one."

Harris applies this step to a field `E_{t-1}` lying in the Galois
closure `Ẽ` of `E'/E`. Here `E'/E` is an extension of CM fields
(`math_9611226v1.tex` lines 1466–1468, setup before Proposition 4.8), so
`E_{t-1}` is a finite extension of the CM field `E` and is totally
complex. This is why the totally complex companion suffices for Harris's
argument. The Euler equality
`hst`, and the construction of the attachments, remain obligations of
the Proposition 4.8 branch inputs.
