# Irreducible mirabolic functionals and twisted pairings

Author: Worker 440. Worker 353 supplied the target specification and its route
from JPSS to the equal-rank uniqueness argument.

This module states three inputs from Jacquet–Piatetski-Shapiro–Shalika (1983),
Proposition 1.4 and the two corollaries in §1.5, printed pp.380–384. The third
input is the compact-standard pairing used explicitly on p.398 in §2.10.
The four declarations below are Prop-valued definitions. This module proves
none of these propositions and asserts no classification theorem.

## Field, group and actual compact model

Each declaration has the arguments `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p`, `T : F.TopologicalData`, and `n : ℕ`.
Thus every prime, every finite extension of the p-adic field in an arbitrary
universe, and every supplied compatible local-field realization are covered.
The local topology is `T.topology`. An `IsTopologicalRing F.Carrier`
certificate is derived internally from `T.valuativeRel` and `T.localField`;
it adds no hypothesis and no choice of a different topology. No normed-field
instance replaces the supplied data.

Write

```text
r = n + 1,
G = Langlands.GeneralLinear (n + 1) F.Carrier,
P = GeneralLinear.mirabolic n F.Carrier,
N = GeneralLinear.Mirabolic.upperUnipotent n F.Carrier,
θ = Whittaker.mirabolicCharacter ψ n,
τ = Whittaker.mirabolicCompactInduced ψ n,
q = T.residueCardinality,
abv = RankinSelberg.normalizedAbsoluteValue T.
```

The existing `ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`
is continuous, nontrivial and unitary. The actual subgroup `P` consists of
invertible matrices whose last row is `(0,…,0,1)`, and `N` is its full upper
unipotent subgroup. The character is the positive adjacent-entry product
`∏ i : Fin n, ψ.complex (u.val.val.val i.castSucc i.succ)`.

The carrier of `τ` is the published `MirabolicCompactFunctions ψ n`, in
`Type uF`. Its vectors are actual smooth covariant functions on `P` with
compact projected nonzero support in `N \ P`. They satisfy
`f(u * g) = θ(u) * f(g)` and the action is `(τ(h)f)(g) = f(g * h)`.
The module imports this representation directly from `MirabolicModels`.
It uses no abstract substitute for the carrier and no smooth-induced
representation in place of compact induction.

JPSS defines this compact model on p.378, despite writing `Ind` in §1.1.
Its general induction convention on p.377 includes modular factors, but
both modular characters restrict trivially to `N`, so the covariance here
has no extra factor. Bernstein–Zelevinsky (1976), §§2.21–2.22, pp.21–22,
distinguishes the smooth and compact models with this same unnormalized
covariance and right action. Its §5.7, p.45, calls them `τ_P` and `τ_P⁰`,
respectively. The present `τ` is BZ's compact `τ_P⁰`, and is JPSS's `τ_r`.

## Full character-functional space

`Langlands.Whittaker.MirabolicFunctionalMultiplicityStatement.{uF,uV}`
quantifies over `ψ`, every `V : Type uV` with `AddCommGroup V` and
`Module ℂ V`, and every `ξ : Representation ℂ P V`. Under just
`IsSmooth ξ` and `Representation.IsIrreducible ξ`, put

```text
L = Whittaker.functionals N θ ξ.
```

This is the existing full submodule of algebraic complex-linear functionals
`ℓ : V →ₗ[ℂ] ℂ` satisfying `ℓ(ξ(u)v) = θ(u) ℓ(v)`. No topology on the
carrier or its dual is imposed. The conclusion is the conjunction

```text
(∀ ℓ ℓ' : L, ℓ ≠ 0 → ∃ c : ℂ, ℓ' = c • ℓ) ∧
(Nonempty (L ≃ₗ[ℂ] ℂ) ↔ Nonempty (ξ.Equiv τ)) ∧
(¬ Nonempty (ξ.Equiv τ) → ∀ ℓ : L, ℓ = 0).
```

The first assertion gives dimension at most one by scalar uniqueness, also
when the whole space is zero. The second includes existence and says that
the space is exactly one dimensional precisely for the compact-standard
isomorphism class. The last assertion makes vanishing in every other case
explicit. None uses finite `finrank` to stand for the dimension of a possibly
infinite space. These are the direct conclusions of JPSS §1.5, Corollary 1,
p.384, for the actual model and its character.

## Finite spectral exceptions for irreducible pairs

`Langlands.Whittaker.MirabolicTwistedPairingRigidityStatement.{uF,uV,uW}`
quantifies over the same field data and `ψ`, independent complex-module
carriers `V : Type uV` and `W : Type uW`, and representations `ξ` and `ξ'`
of `P` on them. Each is assumed smooth and irreducible. Neither is assumed
admissible, finite dimensional, finitely generated, or of finite length.

For this pair it asserts

```text
∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint q s ∉ E →
  ∀ β : InvariantBilinear.forms ξ ξ'
    (fun g => determinantWeight abv g.val (-s)),
    β ≠ 0 → Nonempty (ξ.Equiv τ) ∧ Nonempty (ξ'.Equiv τ).
```

The submodule is the published `Langlands.InvariantBilinear.forms`, imported
from `Langlands.Representation.Filtration.InvariantBilinear`. It is not
redefined. Its underlying vectors are curried bilinear maps
`β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ` with

```text
β (ξ(g)v) (ξ'(g)w) = determinantWeight abv (g : G) (-s) * β v w
```

for every `g : P`, `v`, and `w`. The subtype's `β ≠ 0` means a nonzero
bilinear map in this actual submodule.

The absolute value is the residue-cardinality normalization:
`abv(x) = T.normalizedAbs x`, and for nonzero `x` it is
`(q : ℝ)^(-T.ord x)`, so a uniformizer has value `q⁻¹`.
The weight is the usual complex power `(abv(det g) : ℂ)^(-s)`.
Thus this space is precisely `Bil_P(ξ ⊗ α^s, ξ')` in JPSS notation,
where `α(g) = |det g|`: moving the first action's `α^s` factor to the
other side yields `|det g|^(-s)`.

The existing `spectralPoint q s` is `(q : ℂ)^(-s)`. The finite set is
chosen after the representations and before both `s` and `β`; it is
a set of spectral values, not a finite set of exponents. This is §1.5,
Corollary 2, p.384, which derives the assertion from Proposition 1.4 and
the classification by index. The present target needs no chosen index
function and adds no classification hypothesis.

## The compact-standard pairing for every exponent

`Langlands.Whittaker.MirabolicCompactTwistedPairingStatement.{uF}` states,
for every `ψ` and every `s : ℂ`,

```text
Nonempty ((InvariantBilinear.forms τ τ
  (fun g => determinantWeight abv g.val (-s))) ≃ₗ[ℂ] ℂ).
```

This asserts existence of a nonzero form as well as scalar uniqueness,
for every exponent without exceptions. It is the compact-standard case
of Proposition 1.4 together with twist invariance of its isomorphism
class, used as `dim Bil_P(τ_r ⊗ α^s, τ_r) = 1` on JPSS p.398.

There is no silent replacement of the second model by a different character.
The proof of Corollary 1 on p.384 introduces the opposite-character
compact induction and identifies its isomorphism class with `τ_r`.
For the actual model, BZ76 §5.6's character-change is effected by the
diagonal matrix with alternating entries `±1` and last entry `1`.
It lies in `P`, normalizes `N`, and conjugation multiplies every adjacent
upper entry by `-1`. Precomposing functions with left multiplication by
this matrix switches `θ` to `θ⁻¹`, preserves compact projected support,
and commutes with right translation. Unitarity identifies `θ⁻¹` with
the conjugate character in the source.

Likewise multiplying a function by `|det g|^s` identifies the determinant
twist of the compact model with the same model: the multiplier is trivial
on `N`, is smooth, and preserves support. These facts explain the source
correspondence and the chosen same-character formulation. This module
does not implement these maps or prove their properties or irreducibility
of the compact model.

## Packaging, boundary cases and proof scope

`Langlands.Whittaker.MirabolicPairingStatement.{uF,uV,uW} F T n` is the
conjunction of the three named clauses, in the order above. The field,
first carrier and second carrier universes are independent; the compact
model uses its natural field universe and representation equivalences
may cross universes.

Every `n : ℕ` is retained. At `n = 0`, the matrix rank is one,
`P = N = {1}`, the character product is empty, and the compact model is
the scalar representation. An irreducible representation of this group
is one dimensional, so the functional and pairing statements include
this case, and the exception set may be empty. JPSS makes the `P₁ = {e}`
base case explicit on p.383. Arbitrary carriers include the zero module
without a separate `Nontrivial` input; Mathlib's `IsIrreducible` already
excludes the zero representation. Zero functionals and zero forms are
retained, and the implications with a nonzero premise handle them.

On pp.397–398, JPSS §2.10 passes to finite mirabolic filtrations and
selects a minimal pair of factors. The functional clause singles out the
compact-standard factor, the finite-exception clause eliminates other
nonzero pairings, and the last clause compares the remaining forms.
This statement family concerns only those irreducible inputs. It does
not assert finite length of restrictions, existence of the filtrations,
the final trilinear uniqueness theorem, or transport to canonical topology.

A proof following the original may need separately constructed
classification-by-index and derivative/Fourier results, including the
irreducibility and character/twist equivalences of the actual compact
model. None is supplied as a hypothesis here. Worker 127's separate
compact-minimality/Kirillov scope concerns inclusion of the compact model
in the smooth model and the coefficient/support adapters; it is not a
proof of this statement family. The source correspondence to BZ76
§§5.11–5.15, pp.46–50, explains potential prerequisites, without asserting
that the derivative construction is already formalized.

## Sources and preserved dependencies

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
  *Rankin–Selberg Convolutions*, Amer. J. Math. 105 (1983), 367–464.
  Registered original `jpss-1983-rankin-selberg`, retained at
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
  SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
  Visually read induction and compact-model conventions on pp.377–378,
  §§1.1–1.5 on pp.378–384, and the minimal-pair argument on pp.397–398.
- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
  GL(n,F) where F is a non-Archimedean local field*, Russian Math. Surveys
  31:3 (1976), 1–68, English translation.
  Registered original `bernstein-zelevinsky-1976-representations-gln`,
  retained at
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`,
  SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  Read §§2.21–2.22 on pp.21–22; the model and character definitions and
  the statement of §5.12 on pp.44–47 (the proof continues on p.48);
  and §§5.15–5.23 on pp.49–51. Visually checked the character and model
  formulas on p.45.

Both retained hashes were verified. No matching source-specific erratum
was found in the checked project literature/notes or public Library notes.
The imported model, functional, bilinear-form and normalization definitions
are existing implementation infrastructure. The new propositions are
source-derived p-adic specializations, and do not turn those definitions
into proofs of the cited representation-theoretic results. All existing
Library Lean/Markdown pairs are preserved.
