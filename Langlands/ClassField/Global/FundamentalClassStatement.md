# The global fundamental classes of idele-class cohomology

This module states the cohomological core of global class field theory: the
vanishing of `H¹(Gal(E/F), C_E)` and the existence and uniqueness of a coherent
family of fundamental classes `u_{E/F} ∈ H²(Gal(E/F), C_E)`. It is a statement
only; nothing here is proved. The closing declaration is
`Langlands.ClassField.Global.GlobalFundamentalClassStatement`, a `Prop` at
universe `u`. The helper predicates are in the namespace
`Langlands.ClassField.Global.FundamentalClass`.

## Actual objects

All number fields are in one universe `Type u`. For a finite Galois extension
`E / F`, the coefficient group is Mathlib's actual idele class group
`IdeleClassGroup (𝓞 E) E`. It carries the published arithmetic action
`relativeIdeleClassAut F E` of `E ≃ₐ[F] E`. The cohomology groups are the
published `relativeIdeleClassCohomology F E n` of
`Langlands.ClassField.Global.Cohomology`, which are Mathlib group cohomology.
Classes are compared through the published normalized multiplicative cocycles
`RelativeIdeleCocycle F E` and their `cohomologyClass`. Every class has such a
representative by the published `cohomologyClass_surjective`.

- `ClassFamily : Type (u + 1)` assigns to every finite Galois extension `E / F`
  of number fields in `Type u` one class in `relativeIdeleClassCohomology F E 2`.
- `IdeleClassH1Vanishing` says that every `relativeIdeleClassCohomology F E 1`
  is a subsingleton.
- `Generates c` says that `c F E` has additive order exactly `[E : F]`
  (`Module.finrank F E`) and generates the whole group.

## Cochain convention

Restriction, inflation and local compatibility are stated by explicit cochains,
not through Mathlib's restriction or inflation maps. The convention is that of
the published `RelativeIdeleCocycle.cohomologyClass_eq_of_cochain`: an equation
`c(σ,τ) · b(στ) = b(σ) · σ(b(τ)) · d(σ,τ)` for some idele-class cochain `b`
means that `c` and `d` have the same class. Each predicate quantifies over all
representatives of the classes involved and asks for such a cochain.

- `Restriction c`: for number fields `F ⊆ F' ⊆ E` with `E / F` Galois
  (`E / F'` is then Galois by `IsGalois.tower_top_of_isGalois`), a representative
  `x` of `c F E`, restricted along `E ≃ₐ[F'] E → E ≃ₐ[F] E`
  (`AlgEquiv.restrictScalars`), is related by a cochain to any representative
  `y` of `c F' E`. That is, `Res u_{E/F} = u_{E/F'}`.
- `Inflation c`: for `F ⊆ E ⊆ L` with `E / F` and `L / F` Galois, a
  representative `x` of `c F E` is inflated along
  `AlgEquiv.restrictNormalHom E : (L ≃ₐ[F] L) → (E ≃ₐ[F] E)`. Its values are
  pushed into `C_L` by `ideleClassInclusion` from the companion module
  `Langlands.Global.AdelicFunctoriality.Inclusion`. The result is related by a
  cochain to `y ^ [L : E]` for any representative `y` of `c F L`. That is,
  `Inf u_{E/F} = [L : E] • u_{L/F}`.
- `decompositionHom v w : Gal(E_w/F_v) →* Gal(E/F)` first forgets
  `F_v`-linearity down to `F`-linearity, then restricts to `E`
  (`AlgEquiv.restrictScalarsHom`, `AlgEquiv.restrictNormalHom`). Here `w` is a
  finite place of `E` lying over the finite place `v` of `F`, and the
  completions are Mathlib's `adicCompletion`s with the published scoped
  algebra `F_v → E_w` of `FiniteExtension`. No decomposition subgroup of
  `Gal(E/F)` is identified with `Gal(E_w/F_v)`.
- `LocalCompatibility I c`: let `w` lie over `v` with `E_w / F_v` Galois. Take a
  local cocycle `z` whose class in `H²(Gal(E_w/F_v), E_wˣ)` is a fundamental
  class for `I`. Map its values to `C_E` by Mathlib's
  `IdeleClassGroup.ofAdicCompletion` at `w`: the idele with `w`-coordinate the
  given unit and all other coordinates `1`. The result is related by a cochain
  to `y ∘ decompositionHom` for any representative `y` of `c F E`. The action
  on the cochain is through `decompositionHom`. That is, the image of the local
  fundamental class is the restriction of `u_{E/F}` to the decomposition group.
  Here `F_v` is the published `CompletionPadic.padicField v`, a
  `PadicField (residuePrime v)`. The local cohomology is the published
  `relativeCohomology` of `unitsRepresentation`. "Fundamental class for `I`"
  is the published `IsFundamentalClass` for
  `(I (residuePrime v)).relative (padicField v) E_w`: invariant
  `1 / [E_w : F_v]` (`reciprocalClass`). Finiteness of `E_w / F_v` is the
  published `FiniteExtension.local_finite`.

The closing statement is

`IdeleClassH1Vanishing ∧ ∀ I, (∀ p, (I p).RelativeClassFormation ∧
(I p).ArithmeticNormalization) → ∃! c, Generates c ∧ Restriction c ∧
Inflation c ∧ LocalCompatibility I c`.

`I` ranges over families `∀ p [Fact p.Prime], InvariantFamily.{u,u} p` of
local invariant maps. The hypotheses are the published finite-level
class-formation axioms and the published arithmetic normalization of
`Langlands.ClassFieldTheory.Local`. The existence of such an `I` is a separate
local statement and is not assumed or imported here. The hypotheses and
`LocalCompatibility` use only `I.relative`; `I.absolute` is unconstrained.
Nothing is claimed about uniqueness of `I`: the uniqueness asserted is that
of the family `c` for the given `I`.

## Normalizations

The local classes have invariant `+1 / [E_w : F_v]` for the arithmetic
normalization, as in Artin–Tate. Global invariants are not formalized. In the
literature `inv_{E/F} u_{E/F} = 1 / [E : F]`, and the stated degree factors are
those forced by it. Restriction multiplies invariants by `[F' : F]`
(Artin–Tate XIV §3, Axiom II b), so `Res u_{E/F}` has invariant
`[F' : F] / [E : F] = 1 / [E : F']`. Inflation preserves invariants
(Artin–Tate VII §3, Lemma 1), so `Inf u_{E/F}` has invariant
`1 / [E : F] = [L : E] / [L : F]`, which is the invariant of `[L : E] • u_{L/F}`.
This agrees with Tate's `infl α_{E'/F} = [E : E'] α_{E/F}` (Tate 1979, (1.2.4)).

## Why the family is unique, and why inflation is included

Restriction to the decomposition groups does not determine `u_{E/F}`. Let `m`
be the least common multiple of the local degrees. By Artin–Tate VII §4,
Theorems 11–12, the classes coming from local classes have invariants in
`(1/m)ℤ/ℤ`, and `m` can be smaller than `[E : F]`. Example:
`E = ℚ(√13, √17)` over `ℚ`, of degree 4. Here `13 ≡ 8² (mod 17)`,
`17 ≡ 2² (mod 13)` and `17 ≡ 1 (mod 8)`, and every decomposition group
has order at most 2. Replace `u_{E/ℚ}` alone by `3 • u_{E/ℚ}`. The new family
still satisfies `Generates`, `Restriction` and `LocalCompatibility`, but not
`Inflation`.

With `Inflation`, the family is unique. Suppose `c` and `c'` both satisfy the
conditions. For `E / F` of degree `n`, take a cyclic `K' / F` of degree `n` and
`L = E K'`. A cyclic extension has, for each prime power exactly dividing `n`,
a prime that stays prime in the corresponding subfield (Artin–Tate VII §3,
Lemma 5 and the paragraph before Theorem 7). Hence `n` divides the least
common multiple of the finite local degrees of `L / F`. `LocalCompatibility`
makes `c F L - c' F L` restrict to zero at every finite decomposition group.
Its invariant is therefore a multiple of `m_L / [L : F]`. By `Inflation`, the
inflation of `c F E - c' F E` is `[L : E] • (c F L - c' F L)`. Inflation
preserves invariants, so the invariant of `c F E - c' F E` is a multiple of
`[L : E] · m_L / [L : F] = m_L / n`, hence `0`. So `c F E = c' F E`, since the invariant is
injective (Artin–Tate VII, Theorem 7). This is a variant of Tate's own argument
(Tate 1979, §1.2): inflate to `E E₁` with `E₁ / F` cyclic of the same degree.
Only finite places are used. Archimedean local classes are therefore omitted
from `LocalCompatibility`. `Generates` is stated explicitly, as in the
sources; it is not used in this uniqueness argument.

Existence holds for the classical fundamental classes. Their local
compatibility is the standard relation between global and local canonical
classes, which Tate 1979 uses in the proof of (1.6.1). It is derived from
Artin–Tate as follows. Restrict `u_{E/F}` to the decomposition field `F'` of
`w`; this gives `u_{E/F'}` (Proposition 4 of XIV §3). Over `F'`, the place `w`
is the only place above `v' = w ∩ F'`, and `F'_{v'} = F_v`. So the image of the
local fundamental class in `H²(Gal(E/F'), J_E)` has a single nonzero local
component, of invariant `1 / [E : F']` (VII §3, the local components and
invariants on p.42). Hence its image in `H²(Gal(E/F'), C_E)` is `u_{E/F'}`.
The class `u_{E/F'}` is defined by its invariant (Theorem 7).

## Boundaries

- The cochain equations presume that `E_wˣ → C_E` is equivariant along
  `decompositionHom` (`i_w(σx) = ρ(σ) i_w(x)`), and that
  `ideleClassInclusion : C_E → C_L` is equivariant along
  `AlgEquiv.restrictNormalHom`. With equivariance the conditions are
  independent of the chosen representatives. These facts are true but are not
  proved here, and the predicates do not assume them.
- `[IsGalois F_v E_w]` is a binder of `LocalCompatibility`. It holds whenever
  `E / F` is Galois, but this is not proved here.
- The existence of a normalized local family `I` is a separate local
  statement. It is not imported. Without such an `I` the second conjunct would
  be vacuous; with it, the statement asserts the actual global fundamental
  classes.
- Global invariant maps, the Weil groups built from the classes, and
  reciprocity are later work. A proof of this statement is a separate task.

## Provenance

Derived. The parts of the statement are in the sources below; the
cochain-level formulation, the choice of finite places and the inclusion of
`Inflation` to make the family unique are derived as explained above.

- E. Artin and J. Tate, *Class Field Theory* (2009), registered as
  `artin-tate-2009-class-field-theory`, SHA256
  `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`
  (PDF page = printed page + 9):
  Preliminaries §1, printed pp.1–2 (semilocal decomposition of `H^r(G, J_K)`
  and the injection `C_k → C_K`); Chapter VI §1, Theorem 1, printed p.19
  (`H¹(G, C_K)` is trivial); Chapter VII §3, printed pp.41–50 (local
  components and invariants, Lemma 1 on inflation, Lemma 5, Theorems 7–8:
  `(G, C_Ω)` is a class formation and the invariant is an isomorphism);
  Chapter VII §4, Theorems 11–12, printed p.53; Chapter XIV §3, Axiom II,
  printed p.151, and the fundamental class of invariant `1/n` with
  Proposition 4 (restriction), printed p.153.
- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33,
  Part II (1979), registered as `tate-1979-number-theoretic-background`
  (PDF page = printed page + 9): §1.2, printed pp.4–5 (the classes
  `α_{E/F}`, (1.2.4) `infl α_{E'/F} = [E : E'] α_{E/F}` and
  `res α_{E/F} = α_{E/E'}`, `H¹ = 0`, `H²` cyclic of order `[E : F]` generated
  by `α_{E/F}`, and the identification with the fundamental class); §1.6,
  (1.6.1), printed pp.8–9 (the map `E_vˣ → C_E` to the class of the idele with
  one nontrivial component, and the relation between global and local
  canonical classes).
