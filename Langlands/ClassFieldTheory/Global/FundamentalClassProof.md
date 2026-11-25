# Global class field theory in fundamental-class form (proof)

This module `Langlands.ClassFieldTheory.Global.FundamentalClassProof` proves the published
statement `Langlands.ClassFieldTheory.Global.GlobalFundamentalClassStatement` (module
`Langlands.ClassFieldTheory.Global.FundamentalClassStatement`, unchanged). The statement says
that `H¹(Gal(E/F), C_E)` vanishes for every finite Galois extension `E / F` of number
fields in `Type u`, where `C_E` is the actual idele class group. It also says that for
every local family `I` satisfying `RelativeClassFormation` and `ArithmeticNormalization`
there is a unique family of classes `c F E ∈ H²(Gal(E/F), C_E)` with `Generates`,
`Restriction`, `Inflation` and `LocalCompatibility I`.

## Main results

- `globalFundamentalClassStatement : GlobalFundamentalClassStatement.{u}`: the target.
  Its universe `u` is arbitrary, and it has no hypotheses.
- `fundamentalClass_exists I hI`: for a local family `I` with
  `hI : ∀ p [Fact p.Prime], (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization`,
  there is a `c : ClassFamily.{u}` with
  `Generates c ∧ Restriction c ∧ Inflation c ∧ LocalCompatibility I c`.
- `fundamentalClass_unique I hI hc hc'`: two families `c, c'` that both satisfy
  `Inflation` and `LocalCompatibility I` are equal.

The H¹ vanishing component is the published theorem
`Langlands.ClassFieldTheory.Global.ideleClassH1Vanishing : FundamentalClass.IdeleClassH1Vanishing.{u}`
(module `Langlands.ClassFieldTheory.Global.H1VanishingProof`). This module uses it and does not
restate it.

## Proof

Everything is an application of published results; this module proves nothing new.

- The published module `Langlands.ClassFieldTheory.Global.FundamentalClassReduction` proves
  `fundamentalClass_exists_of`, `fundamentalClass_unique_of` and
  `globalFundamentalClassStatement_of`. These derive existence, uniqueness and the target
  from the hypothesis `GlobalInvariantStatement.{u}` (and, for the target, also
  `IdeleClassH1Vanishing.{u}`).
- `GlobalInvariantStatement.{u}` (module `Langlands.ClassFieldTheory.Global.InvariantStatement`)
  is proved by `Langlands.ClassFieldTheory.Global.globalInvariantStatement` (module
  `Langlands.ClassFieldTheory.Global.InvariantProof`). It gives, for each such `I`, global
  invariant maps `inv_{E/F} : H²(Gal(E/F), C_E) → ℚ/ℤ` with `IsGlobalInvariant I inv`.
- `IdeleClassH1Vanishing.{u}` is proved by `ideleClassH1Vanishing`.

So `fundamentalClass_exists` and `fundamentalClass_unique` are the reduction theorems
applied to `globalInvariantStatement.{u}`. `globalFundamentalClassStatement` is
`globalFundamentalClassStatement_of ideleClassH1Vanishing globalInvariantStatement`.

## Checks

The module compiles with no errors or warnings. Inspection of each of the three theorems,
unapplied, shows that it uses only the axioms `propext`, `Classical.choice` and
`Quot.sound` and has the single universe parameter `u`. The types have no hypotheses
beyond the binders shown above. These are development checks; exact-target validation
and independent review are separate.

## Provenance

Derived. The mathematics is that cited by `FundamentalClassStatement`: E. Artin and
J. Tate, *Class Field Theory* (2009), `artin-tate-2009-class-field-theory`, Chapter VI §1
Theorem 1 (printed p.19) for `H¹(G, C_K) = 0`, and Chapter VII §3 (printed pp.41–50) for
the fundamental classes. The proofs of the two inputs are documented in their own
modules.
