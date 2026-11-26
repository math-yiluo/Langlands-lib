# The generic fibre of a σ-lift from finite elliptic trace separation

The module `Langlands.BaseChange.SigmaLiftGenericFibreReduction` proves that the generic fibre
statement `SigmaLiftGenericFibreStatement` (Henniart–Lemaire 2011, II.4.8, Lemme (2)) follows
from finite elliptic trace separation, the Library statement
`EllipticDiscreteTraceSeparationStatement`. It does not prove that statement, so it does not
prove the generic fibre statement.

## The reduction statement

```lean
def SigmaLiftGenericFibreReductionStatement.{u₁, v₁, uV₁, uV'₁, uW₁} : Prop :=
  EllipticDiscreteTraceSeparationStatement.{u₁, u₁, max uV₁ uV'₁, uV'₁} →
  EllipticDiscreteTraceSeparationStatement.{u₁, u₁, uV₁, uV₁} →
  SigmaLiftGenericFibreStatement.{u₁, v₁, uV₁, uV'₁, uW₁}

theorem sigmaLiftGenericFibreReduction :
    SigmaLiftGenericFibreReductionStatement.{u, v, uV, uV', uW}
```

The universes are those of `SigmaLiftGenericFibreStatement`: `u` for `F`, `v` for `E`, `uV`,
`uV'`, `uW` for the spaces of `π`, `π'` and `τ`. Separation is used, through
`ellipticTwistRigidity_of_separation` (module `Langlands.BaseChange.EllipticTwistRigidity`), once
for the pair `(π, π')` (family carriers in `max uV uV'`, compared representation in `uV'`) and
once for the pair `(π, π)` (universes `uV`, `uV`). Let `D` be the character group of the finite
quotient `Fˣ/N`. The two finite index types of the separation invocations are the subtype of `D`
of characters `χ` whose twist `(χ ∘ det) ⊗ ρ'` of the compared representation `ρ'` is inequivalent
to `ρ'` (this subtype may be empty), used for the nonvanishing `t ≠ 0`, and the disjoint sum of
`D` and that subtype, used for the twist. Both lie in the universe `u` of `F`.

`EllipticDiscreteTraceSeparationStatement` (module of the same name): for irreducible admissible
essentially square-integrable representations of `GL_n(F)`, `0 < n`, if the trace of `π` is a
fixed linear combination of the traces of a finite family `ρ i` on all regular elliptic tests,
then `π` is equivalent to some `ρ i`. Its Markdown derives it from the elliptic orthogonality
relations.

## Helper lemma (namespace `Langlands.BaseChange.SigmaLiftGenericFibre`)

`distribution_eq_zero_of_localValues_zero`: on a locally compact, Hausdorff, totally disconnected
space, a distribution `D` with local value `0` (`HasLocalValue μ D x 0`) at every point `x` where
a test function `f` is nonzero satisfies `D f = 0`. Each such `x` has an open neighbourhood on
which the restriction `Distribution.restrictOpen` of `D` vanishes, so `x` is outside the
topological support of `D`, and `Distribution.mem_supportedOn_support` gives `D f = 0`. The same
argument is a private lemma of `Langlands.BaseChange.CommonShintaniLiftTrace`.

## The proof of `sigmaLiftGenericFibreReduction`

Fix the data of `SigmaLiftGenericFibreStatement` (rank `r + 1`), put the Borel σ-algebras on
`GL_{r+1}(F)` and `GL_{r+1}(E)`, and let `N = (Units.map (Algebra.norm F : E →* F)).range`. By
`IsCyclicAlgebra.normRange_isOpen_finiteIndex` (local class field theory), `N` is open and of
finite index in `Fˣ`.

1. *Schur.* `SigmaIntertwiner.exists_smul_toLinearMap` (module
   `Langlands.BaseChange.CommonShintaniLiftNonvanishing`, Schur's lemma for the irreducible
   admissible `τ`) gives `a ≠ 0` with `A' = a • A`. Put `t = a c / c'`; it is nonzero since the
   constants `c`, `c'` of σ-lifts are.
2. *Proportional characters on the elliptic norms.* Let `μ` be a Haar measure on `GL_{r+1}(F)`
   and `f` a test function supported in the regular elliptic set (`IsEllipticSupported f`) with
   `det g ∈ N` whenever `f g ≠ 0`. By the elliptic norm criterion (`ellipticNormCriterion`), every
   point of the support of `f` is a norm, so `f` vanishes off norms
   (`vanishesOffNorms_of_isNorm_support`). The second half of regular transfer
   (`regularTransfer`, Henniart–Lemaire I.2.5) gives a test function `φ` on `GL_{r+1}(E)`
   concordant with `f` for `μ` and a Haar measure `μE`. The two σ-lift identities give
   `Θ^A_τ(φ) = c Θ_π(f)` and `Θ^{A'}_τ(φ) = c' Θ_{π'}(f)`, and `twistedDistribution_smul` gives
   `Θ^{A'}_τ(φ) = a Θ^A_τ(φ)`. Hence `Θ_{π'}(f) = t Θ_π(f)`.
3. *`π'` is essentially square-integrable.* Otherwise, transported to the p-adic realization
   `CharZeroLocalField.padicField F` with its topological data
   `CharZeroLocalField.topologicalData F` (module
   `Langlands.LocalField.CharZeroPadicRealization`, on the carrier `F` itself) by
   `isEssentiallySquareIntegrable_iff_padic`, the generic `π'` is not essentially
   square-integrable in the p-adic sense, so `padicGenericEllipticCharacterVanishing` (module
   `Langlands.Representation.Classification.GenericEllipticCharacter`: such a `π'` is a proper
   parabolic induction, whose character vanishes on the regular elliptic set) gives `Θ_{π'}` the
   local value `0` at every regular elliptic element. By
   `distribution_eq_zero_of_localValues_zero`, `Θ_{π'}(f) = 0` for the tests of step 2, so
   `Θ_π(f) = 0` for them since `t ≠ 0`. Thus `Θ_π = 0 · Θ_π` on these tests, and
   `ellipticTwistRigidity_of_separation` for the pair `(π, π)` with factor `0` gives `0 ≠ 0`, a
   contradiction.
4. *Conclusion.* `ellipticTwistRigidity_of_separation` for the pair `(π, π')`, with `H = N` and
   the factor `t` of step 2, gives `κ : Fˣ →* ℂˣ` trivial on `N` with `π' ≅ (κ ∘ det) ⊗ π`.
   Triviality on `N` is `IsNormTrivial E κ`.

The genericity hypothesis gives the irreducibility of `π'` (first component of
`Whittaker.IsGeneric`) and is used in step 3.

## Comparison with Henniart–Lemaire

Henniart–Lemaire's proof of Lemme II.4.8 (2) (printed pp. 90–91; source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`) uses character
functions: the identity "à la Shintani" (II.2.9) transports the nonvanishing of `Θ_π` on the
elliptic norms (Lemme (1)) to the twisted character of `Π` and back to `Θ_{π'}`; the vanishing of
the characters of proper parabolic inductions on the elliptic set (II.4.5) shows that `π'` is
essentially discrete; formula (3) gives `π' ≅ κπ`. The proof here works with distributions.
Regular transfer (HL I.2.5, Proposition (2)) and the σ-lift identities give the proportionality
of `Θ_π` and `Θ_{π'}` on the tests supported in the elliptic norms directly, so the identity
"à la Shintani" (`SigmaLiftCharacterIdentityStatement`) is not used. The nonvanishing of
Lemme (1) and the use of formulas (1)–(3) are replaced by `ellipticTwistRigidity_of_separation`,
which uses HL's averaging over the characters of `Fˣ/N_{E/F}(Eˣ)` and finite elliptic trace
separation. The elliptic norm criterion (HL I.6.12; Arthur–Clozel 1989, Chapter 1, Lemma 1.4)
identifies the elliptic norms with the regular elliptic elements of norm determinant.

The proof uses no global result: its inputs are local theorems of the Library named above and
the separation statement.
