# The global invariant maps of idele-class cohomology

This module states the existence of the global invariant maps of class field theory on
the actual second cohomology of the idele class group, with the properties that the
proof of `Langlands.ClassField.Global.GlobalFundamentalClassStatement` uses. It is a
statement only; nothing here is proved. The closing declaration is
`Langlands.ClassField.Global.GlobalInvariantStatement`, a `Prop` at universe `u`. The
helper predicates are in the namespace `Langlands.ClassField.Global.FundamentalClass`,
next to the predicates of the published module
`Langlands.ClassField.Global.FundamentalClassStatement`, which this module imports.

## Actual objects

All objects are those of `FundamentalClassStatement`: number fields in one universe
`Type u`, the actual idele class group `IdeleClassGroup (𝓞 E) E` with the published
action `relativeIdeleClassAut`, the published `relativeIdeleClassCohomology F E 2`
(Mathlib group cohomology), the published normalized cocycles `RelativeIdeleCocycle`
with `cohomologyClass`, the idele-class inclusion `ideleClassInclusion`, Mathlib's
`IdeleClassGroup.ofAdicCompletion`, the published `decompositionHom v w`, the published
local `InvariantFamily`, `unitsRepresentation`, `padicField v` and `residuePrime v`.
The target group of the invariants is the published `RationalModIntegers`
(`ℚ ⧸ zmultiples 1`), the same group as for the local invariants, and
`denominatorSubgroup n` is its subgroup `{x | n • x = 0} = (1/n)ℤ/ℤ`.

## Definitions

- `GlobalInvariantMaps : Type (u + 1)` assigns to every finite Galois extension `E / F`
  of number fields in `Type u` an additive homomorphism
  `relativeIdeleClassCohomology F E 2 →+ RationalModIntegers`. No law is assumed.
- `InvariantImages inv`: every `inv F E` is injective and its range is
  `denominatorSubgroup [E : F]`. Hence `H²(Gal(E/F), C_E)` is cyclic of order `[E : F]`.
- `InvariantRestriction inv`: for number fields `F ⊆ F' ⊆ E` with `E / F` Galois, a
  cocycle `x` of `E / F` and a cocycle `y` of `E / F'`, the restriction of `x` along
  `σ ↦ σ.restrictScalars F` is related to `y` by an explicit cochain `b`, in the
  convention of the published `FundamentalClass.Restriction`, if and only if
  `inv F' E [y] = [F' : F] • inv F E [x]`. This is `inv ∘ Res = [F' : F] · inv`.
- `InvariantInflation inv`: for `F ⊆ E ⊆ L` with `E / F` and `L / F` Galois, cocycles
  `x` of `E / F`, `y` of `L / F` and `m : ℕ`, the inflation of `x` along
  `AlgEquiv.restrictNormalHom E`, pushed into `C_L` by `ideleClassInclusion`, is
  related to the pointwise power `y ^ m` by an explicit cochain, in the convention of
  the published `FundamentalClass.Inflation`, if and only if
  `m • inv F L [y] = inv F E [x]`. This is `inv ∘ Inf = inv`. The exponent `m` matches
  the factor `y ^ [L : E]` of `FundamentalClass.Inflation`.
- `InvariantLocal I inv`: let `w` be a finite place of `E` over the finite place `v`
  of `F`, with `E_w / F_v` Galois. For a local `2`-cocycle `z` of
  `Gal(E_w / F_v)` with values in `E_wˣ` and a global cocycle `y` of `E / F`, the image
  of `z` in `C_E` under `IdeleClassGroup.ofAdicCompletion` at `w` is related to
  `y ∘ decompositionHom v w` by an explicit cochain, in the convention of the
  published `FundamentalClass.LocalCompatibility`, if and only if
  `([E : F] / [E_w : F_v]) • inv F E [y]` equals the local invariant
  `(I (residuePrime v)).relative (padicField v) E_w [z]`. The quotient is natural-number
  division; for Galois `E / F` the local degree divides the global degree, so it is
  exact. Mathematically: if `F'` is the decomposition field of `w`, then
  `[E : F] / [E_w : F_v] = [F' : F]`, the class of `y ∘ decompositionHom` is
  `Res_{F'} [y]`, of invariant `[F' : F] · inv [y]`, and the image of a local class in
  `H²(Gal(E/F'), C_E)` has the local invariant as its global invariant.
- `IsGlobalInvariant I inv` is the conjunction of the four properties.
- `GlobalInvariantStatement`: for every family `I : ∀ p [Fact p.Prime],
  InvariantFamily.{u,u} p` satisfying the published `RelativeClassFormation` and
  `ArithmeticNormalization` at every prime, there is `inv` with
  `IsGlobalInvariant I inv`.

## Why this form

Each compatibility is an equivalence between the cochain relation used in
`FundamentalClassStatement` and an equation of invariants. With such maps,
`u_{E/F} := (inv F E)⁻¹(1/[E : F])` satisfies `Generates`, `Restriction`, `Inflation`
and `LocalCompatibility` by the "if" directions, and the "only if" directions give the
uniqueness argument explained in the Markdown of `FundamentalClassStatement` (with a
cyclic `K' / F` of degree `[E : F]`). The cochain relations need no separate
cocycle constructions: the equivalences quantify over the representatives directly.

The statement is true for the classical global invariant. For a family `I` with the
hypotheses, the local invariants are the classical ones: in `H²` of a finite Galois
`L / F_v`, inflate to an extension containing the unramified extension of degree
`[L : F_v]`; there `ArithmeticNormalization` and `InflationCompatibility` fix the
invariant of the unramified fundamental class, and `RelativeImages` makes the invariant
an isomorphism, so two such families agree. The classical global invariant is the sum
of the local invariants on `H²(G, J_E)` (semilocal Shapiro lemma) extended to
`H²(G, C_E)` (Artin–Tate VII §3). Archimedean places contribute their canonical
invariants; they do not occur in the statement.

## Boundaries

- As in `FundamentalClassStatement`, the cochain relations presume that
  `E_wˣ → C_E` is equivariant along `decompositionHom` and that
  `ideleClassInclusion : C_E → C_L` is equivariant along
  `AlgEquiv.restrictNormalHom`. These facts are true but are neither proved nor
  assumed here; they are needed to read the relations as equalities of classes.
- `[IsGalois F_v E_w]` is a binder of `InvariantLocal`; it holds whenever `E / F`
  is Galois. Archimedean places are not used.
- The existence of a family `I` with the hypotheses is a separate local statement
  and is not imported; without such an `I` the closing statement is vacuous.
- Nothing is proved here. The proof of `GlobalInvariantStatement`, and its use for
  `GlobalFundamentalClassStatement`, are separate tasks.

## Provenance

Derived. The invariant map, its image, its behavior under restriction and inflation and
the invariant of the image of a local class are in the sources below; the
cochain-level equivalences, the exponent `m` in the inflation clause and the
natural-number quotient in the local clause are derived formulations, chosen to match
the predicates of `FundamentalClassStatement`.

- E. Artin and J. Tate, *Class Field Theory* (2009), registered as
  `artin-tate-2009-class-field-theory`, SHA256
  `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`
  (PDF page = printed page + 9): Preliminaries §1, printed pp.1–2 (semilocal
  decomposition); Chapter VII §3, printed pp.41–50: local components and the global
  invariant on `H²(G, J_K)` as the sum of the local invariants (p.42); Lemma 1
  (inflation preserves invariants) and Lemma 2 (restriction multiplies invariants by
  `[E : k]`) for `H²(G, J_K)`, p.43; Remark 1 (p.47), Remarks 2–3 and the definition of
  the invariant of a regular idele-class element through an inflation, independent of
  the auxiliary field (p.48); Lemma 4 (restriction multiplies invariants by `[E : k]`
  on `H²(C_K)`, p.49); Lemmas 5–6 and the general case (pp.49–50); Theorem 7 (the
  invariant is an isomorphism onto the rationals mod 1, p.50); Chapter XIV §3,
  Axiom II (`inv` maps `H²(K/F)` onto `(1/n)ℤ/ℤ` and `inv_E ∘ res = [E : F] · inv_F`,
  p.151) and Proposition 4 (restriction of fundamental classes, p.153).
- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II
  (1979), registered as `tate-1979-number-theoretic-background` (PDF page = printed
  page + 9): §1.2, printed pp.4–5 (`H²(Gal(E/F), C_E)` cyclic of order `[E : F]`,
  restriction and inflation of the canonical classes).
