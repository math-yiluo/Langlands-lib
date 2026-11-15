# Coefficient fields of equal-characteristic congruence quotients

This module provides the ring-theoretic input of the equal-characteristic case
of Kaletha–Prasad Theorem A.4.19. A *coefficient field* of the congruence
quotient `R / m^n` is a ring section of its residue map onto the residue field.
The module proves that such sections exist and that `R / m^n` is finite over any
such section when `R` is a DVR. The universe `u` is arbitrary. The ring `R` is a
commutative local ring in `Type u`. Here `m` is `IsLocalRing.maximalIdeal R` and
`n : ℕ+` is a positive level, as in the published `CongruenceTower` API, where
`congruenceRing R n = R ⧸ m ^ (n : ℕ)`.

## The residue map of a congruence quotient

- `congruenceResidue R n : congruenceRing R n →+* ResidueField R` is the
  actual factorisation `Ideal.Quotient.factor` of the residue quotient through
  `R ⧸ m^n`, using `m^n ≤ m`.
- `congruenceResidue_quotient` states the defining law: the residue of the class
  of `r` is `residue R r`. The proof is `rfl`.
- `congruenceResidue_surjective` states that the map is surjective.
- `mem_ker_congruenceResidue` states that every element of its kernel lies in
  the image ideal `m.map (congruenceQuotient R n)`.
- `isNilpotent_ker_congruenceResidue` states that the kernel ideal is nilpotent.
  Its `n`-th power lies in the `n`-th power of the image of `m`. That power is
  the image of `m^n`, which is zero in `R ⧸ m^n`.

## Existence of coefficient fields

- `formallySmooth_int_of_charZero` states that every field `K` of
  characteristic zero, with any `ℤ`-algebra structure, is formally smooth over
  `ℤ`. The proof first identifies the given algebra structure with the canonical
  one. It then chooses a transcendence basis of `K` over `ℚ`. The field `K` is
  algebraic, hence separable in characteristic zero, over the subfield generated
  by that basis. Mathlib's
  `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable` then gives
  formal smoothness of `K` over `ℚ`. Since `ℚ` is a localisation of `ℤ`, it is
  formally smooth over `ℤ`. Formal smoothness is transitive.
- `exists_coefficientField_of_charZero` assumes `CharZero (ResidueField R)`. It
  proves that there is a ring homomorphism
  `σ : ResidueField R →+* congruenceRing R n` with
  `(congruenceResidue R n).comp σ = RingHom.id _`. The residue map is a
  surjective `ℤ`-algebra map with nilpotent kernel. By formal smoothness of the
  residue field over `ℤ`, Mathlib's `Algebra.FormallySmooth.liftOfSurjective`
  lifts the identity of the residue field through it. No hypothesis on the
  characteristic of `R` is needed here.
- `exists_coefficientField_of_charP` assumes a prime `p` with `CharP R p`,
  `CharP (ResidueField R) p` and `PerfectRing (ResidueField R) p`. It proves the
  same section property. In characteristic `p` the `p^n`-th power map
  `r ↦ r ^ (p ^ n)` is the ring endomorphism `iterateFrobenius R p n`. Since
  `p^n ≥ n`, its composite with the quotient map sends `m` into `m^n`, hence to
  zero. The composite therefore factors through a ring homomorphism
  `τ' : ResidueField R →+* R ⧸ m^n`. The section is `τ'` composed
  with the inverse of the `n`-fold Frobenius automorphism of the perfect residue
  field. Its residue is
  `(x^{1/p^n})^{p^n} = x`.
- `exists_coefficientField` assumes `IsAlgClosed (ResidueField R)` and
  `ringChar R = ringChar (ResidueField R)`. It proves the same section property
  at every positive level `n`. It splits on the characteristic of the residue
  field. If that characteristic is a prime `p`, the characteristic equality gives
  `CharP R p`. An algebraically closed field is perfect through Mathlib's instance,
  so the positive-characteristic theorem applies. If the characteristic is zero,
  the characteristic-zero theorem applies.

The sections are chosen separately at each level. No compatibility between
levels is stated or needed. In characteristic zero the section is
noncanonical: it is the value of `liftOfSurjective`, which depends on choices.

## Finiteness over a coefficient field

- `congruenceRing_finite` assumes that `R` is a domain and a discrete valuation
  ring. It takes any ring section `σ` of `congruenceResidue R n`. It proves
  `Module.Finite (ResidueField R) (congruenceRing R n)` for the algebra structure
  `σ.toAlgebra`. Let `π` be the class of a uniformiser `ϖ`. By induction on
  `j ≤ n`, every element of `R ⧸ m^n` has the form `s + π^j y`, with `s` in the
  residue-field span of `1, π, …, π^{n-1}`. The induction step subtracts
  `σ` of the residue of `y`. The difference has zero residue, hence lies in
  `π · (R ⧸ m^n)`, because `m = (ϖ)`. Since `π^n = 0`, the span of these `n`
  powers is everything.

## Provenance

The source context is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The relevant
passage is the paragraph before Theorem A.4.19, printed p.628 / PDF p.659. There
the field `f` is the residue field. Weil restriction from `o/m^n` to `f` uses an
`f`-algebra structure on `o/m^n`. In equal positive characteristic this is the
canonical structure of Serre, *Local Fields*, Chapter II, §4, Proposition 8. In
characteristic zero it is a noncanonical structure from Proposition 6 of that
section. The book chooses it uniformly in `n` through the completion. The
registered `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF p.49,
adds perfectness of the residue field. In this module the residue field is
assumed algebraically closed, hence perfect.

Serre's *Local Fields* is not registered in the project literature and was not
consulted. The Lean proofs above are internal and were written without it. In
characteristic zero the section comes from formal smoothness of the residue
field over `ℤ` and lifting through a nilpotent kernel. In characteristic `p` it
comes from the explicit Frobenius construction above. The finiteness theorem is
an internal elementary argument. Only the existence of a section at each fixed
level is proved. The book's uniform choice and canonicity are not formalised.
