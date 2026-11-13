# Invariant functions of a finite group of permutations

Module `Langlands.Representation.CuspidalSupport.FiniteGroupInvariantFunctions`,
namespace `Langlands.CuspidalSupport.InvariantFunctions`.

## Provenance

This is a general commutative-algebra helper. It is internal to the proof of Renard VI.7.1
(Theorem; Renard 2026, French version dated 9 July 2026, printed pp.180–181), where the
coordinate algebra of `X(M)/W` is taken to be the `W`-invariant regular functions on `X(M)`.
Renard treats this step as standard and does not prove it. The proof below uses only Mathlib:
the Artin–Tate lemma, integrality over the invariants of a finite group, lying over, and
Zariski's lemma.

## Setting

`X` is a type, `R : Subalgebra ℂ (X → ℂ)` is an algebra of complex functions on `X`, and
`W : Subgroup (Equiv.Perm X)` is a group of permutations of `X`. A permutation `w` *preserves*
`R` when `f ∘ w ∈ R` for every `f ∈ R`.

## Declarations

- `fixedSubalgebra R W : Subalgebra ℂ R` contains the elements `f` of `R` with
  `f (w x) = f x` for all `w ∈ W` and `x : X`.
- `action hW : MulSemiringAction W R` is the action `w • f = f ∘ w⁻¹`. It is defined when every
  element of `W` preserves `R` (hypothesis `hW`).
- `fixedSubalgebra_isInvariant`: under this action, `fixedSubalgebra R W` is exactly the
  subring of `W`-invariants (`Algebra.IsInvariant`).
- `fixedSubalgebra_isIntegral`: if `W` is finite, `R` is integral over `fixedSubalgebra R W`.
  This is Mathlib's `Algebra.IsInvariant.isIntegral`.
- `fixedSubalgebra_finiteType`: if `R` is a finitely generated `ℂ`-algebra and `W` is finite,
  then `fixedSubalgebra R W` is a finitely generated `ℂ`-algebra.
- `fixedSubalgebra_exists_eval`: suppose `R` is finitely generated, every `ℂ`-algebra map
  `R → ℂ` is evaluation at a point of `X` (hypothesis `hev`), and `W` is finite. Then every
  `ℂ`-algebra map `fixedSubalgebra R W → ℂ` is evaluation at a point of `X`.
- `exists_invariantSubalgebra` (main result) assumes that `R` is finitely generated and a
  domain, satisfies `hev`, separates points (`x ≠ y → ∃ f ∈ R, f x ≠ f y`), and that `W` is
  finite and preserves `R`. It then gives `O : Subalgebra ℂ (X → ℂ)` such that:
  - `O` as a set is `{f | f ∈ R ∧ ∀ w ∈ W, ∀ x, f (w x) = f x}`;
  - `O` is a finitely generated `ℂ`-algebra and a domain;
  - every `ℂ`-algebra map `O → ℂ` is evaluation at some `x : X`;
  - for all `x y`, `(∃ w ∈ W, w y = x) ↔ ∀ f ∈ O, f x = f y`. So `O` separates exactly the
    `W`-orbits.

## Proofs

- **Finite type.** `R` is finitely generated over `ℂ`, so also over `S = fixedSubalgebra R W`
  (`Algebra.FiniteType.of_restrictScalars_finiteType`). `R` is integral over `S`, so it is a
  finite `S`-module (`Algebra.IsIntegral.finite`). The Artin–Tate lemma (`fg_of_fg_of_fg`)
  then shows that `S` is finitely generated over `ℂ`.
- **Evaluations.** Let `φ : S → ℂ`. Its kernel `P` is maximal. Since `R` is integral over `S`
  and `S → R` is injective, lying over (`Ideal.exists_ideal_over_maximal_of_isIntegral`)
  gives a maximal ideal `Q` of `R` above `P`. The field `R/Q` is a finitely generated
  `ℂ`-algebra, hence finite over `ℂ` (`finite_of_finite_type_of_isJacobsonRing`), hence equal to
  `ℂ` (`IsAlgClosed.algebraMap_bijective_of_isIntegral`). The composite `R → R/Q ≅ ℂ` is a
  `ℂ`-algebra map `ψ`, so by `hev` it is evaluation at some `x`. For `f ∈ S`, `f - φ(f)` lies in
  `P ⊆ Q`, so `φ(f) = ψ(f) = f(x)`.
- **Main result.** Take `O = S.map R.val`, the image of `S` in `X → ℂ`. It is isomorphic to `S`
  (`Subalgebra.equivMapOfInjective`). Finite type and the evaluation property transfer along
  this isomorphism. `O` is a domain as a subring of the domain `R`, via `MulEquiv.isDomain`.
  - *Orbits ⇒ equal values:* immediate from invariance.
  - *Equal values ⇒ same orbit:* argue by contradiction. Suppose `w x ≠ y` for all `w ∈ W`.
    Separation and rescaling give `h_w ∈ R` with `h_w y = 0` and `h_w (w x) = 1`. Let
    `g = 1 - ∏_w (1 - h_w) ∈ R`, so `g y = 0` and `g (w x) = 1` for every `w`. Then
    `F = ∏_{w ∈ W} g ∘ w` lies in `R`, is `W`-invariant (reindex the product by right
    multiplication), and has `F x = 1`, `F y = 0`. This contradicts `F x = F y`.

A finite option `synthInstance.maxHeartbeats 200000` is set for `fixedSubalgebra_exists_eval`.
Instance search for subtraction in the nested subalgebra needs it.
