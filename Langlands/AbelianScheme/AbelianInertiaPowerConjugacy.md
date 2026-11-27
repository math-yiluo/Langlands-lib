# Quasi-unipotence from power conjugacy at the finite Tate levels

`Langlands.AbelianScheme.AbelianInertiaTatePowerConjugacyStatement` uses the data
of `AbelianInertiaQuasiUnipotentStatement`, including the actual geometric
point and the prime invertible in the strictly Henselian discrete valuation
ring. It asks for a positive integer `a` and a natural number `q > 1` for
each fundamental group element `g`. At each level `ℓ^n`, it requires a
`ZMod (ℓ^n)`-linear automorphism conjugating the action of `g^a` to the
action of `g^(a*q)`. The two exponents are fixed across the levels. The
conjugating automorphism is allowed to depend on the level.

`Tate.PrimeAdic.levelMonodromyZMod` is the Library's action
`Tate.levelMonodromy` on the actual torsion sections, regarded as a linear
endomorphism over the residue coefficient ring. The compatibility with
`ZMod (ℓ^n)` scalars is `Tate.levelMonodromy_zmod_smul`.

`Langlands.AbelianScheme.AbelianInertiaQuasiUnipotentReductionStatement`
is the implication from this power-conjugacy premise to the published
quasi-unipotence proposition. The theorem
`Langlands.AbelianScheme.abelianInertiaQuasiUnipotent_of_powerConjugacy`
proves the implication.

## Proof

The proof uses the geometric torsion rank theorem and compatible residue
bases from `Tate.PrimeAdicCoordinates`. In the induced basis of the integral
Tate module, reducing the matrix coefficients by `PadicInt.toZModPow n`
gives the matrix of the finite-level action. This follows by evaluating the
action on each coordinate basis vector. Characteristic polynomials commute
with coefficient reduction. Conjugacy at every level therefore identifies
the characteristic polynomials of the two integral actions by
`PadicInt.ext_of_toZModPow`. Scalar extension identifies their rational
characteristic polynomials as well.

For an invertible operator `T` over a field, suppose `T` and `T^q` have
equal characteristic polynomials with `q > 1`. Over an algebraic closure,
raising to the `q`-th power maps the finite spectrum of `T` to itself.
Two iterates of this map agree on the entire spectrum. If the iterate
indices are `i < j`, every eigenvalue is nonzero and cancellation shows
its `q^j - q^i` power is `1`. With `m = q^j - q^i`, every root of the
characteristic polynomial of `T^m - 1` is zero. The proof factors that
polynomial into its linear factors and applies Cayley–Hamilton.
Injectivity of scalar extension descends nilpotence to the original
field. The exponent for `g` is `a*m`.

## Provenance

The implication formalizes the linear algebra step of the arithmetic
monodromy argument using finite Tate levels and characteristic polynomials.
The tame action by conjugation and the quasi-unipotence conclusion are in
SGA 7 I, Exposé I, §0.3.1 and Proposition 1.1, pp. I-4 to I-6.
Variante 1.3, pp. I-6 to I-7, supplies the passage to a model over an
arithmetic base in the general geometric argument. The registered source is
`deligne-1972-sga7-i-expose-i-monodromie`, SHA-256
`b5a598de1362529cd2be9f71ba17a40e07bc36cef9431f0586caa317653957ce`.
