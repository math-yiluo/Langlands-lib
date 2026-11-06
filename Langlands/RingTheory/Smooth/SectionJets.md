# Jets along a section of a smooth algebra are finite projective

The theorem `Algebra.Smooth.finite_projective_quotient_ker_pow` concerns a smooth
`R`-algebra `A` with an augmentation `ε : A →ₐ[R] R`. For every `n`, the quotient
`A ⧸ (ker ε) ^ (n + 1)` is finite and projective as an `R`-module. In geometric terms,
the `n`-th infinitesimal neighbourhood of a section of a smooth affine scheme is finite
locally free over the base.

## Provenance

This module is internal supporting content for the task proving
`Langlands.GroupScheme.SelfNormalizingProperAmbientStatement`. There, `A` is the
coordinate ring of a smooth affine group scheme, `ε` is its counit, and the quotients
`A ⧸ I ^ (n + 1)` are the finite projective modules of jets that carry the ambient
Grassmannian. The statement is a standard fact about smooth algebras. The Lean proof is
new: a retract argument built only on Mathlib, porting no outside source.

## Conventions

`R : Type u` and `A : Type v` are commutative rings in independent universes, and `A` is an
`R`-algebra.
`I` is `RingHom.ker ε`. For a type `σ`, `MvPolynomial.idealOfVars σ R` is Mathlib's ideal
of `MvPolynomial σ R` spanned by the variables `X i`. `MvPolynomial.restrictSupport R s`
is the `R`-submodule of polynomials with support in `s`. `Finsupp.degree x` is the total
degree of the exponent vector `x`. `Module.Finite` and `Module.Projective` are Mathlib's
classes.

## Declarations

### Truncated polynomial rings

These declarations live in the namespace `MvPolynomial`, for a type `σ` and a
commutative ring `R`.

- `isCompl_restrictSupport_degree σ R n`: the polynomials supported in degrees `≥ n + 1`
  and the polynomials supported in degrees `≤ n` are complementary `R`-submodules of
  `MvPolynomial σ R`.
- `quotientIdealOfVarsPowEquiv σ R n` is an `R`-linear equivalence from
  `MvPolynomial σ R ⧸ idealOfVars σ R ^ (n + 1)` to the polynomials supported in degrees
  `≤ n`.
- `free_quotient_idealOfVars_pow σ R n`: the quotient
  `MvPolynomial σ R ⧸ idealOfVars σ R ^ (n + 1)` is a free `R`-module.
- `finite_quotient_idealOfVars_pow σ R n`: if `σ` is finite, this quotient is a finite
  `R`-module.

### Jets

These declarations live in the namespace `Algebra.FormallySmooth`. They assume
`[Algebra.FormallySmooth R A]` and `[Algebra.FiniteType R A]` and take `ε : A →ₐ[R] R`
and `n : ℕ`.

- `exists_retract_quotient_ker_pow ε n`: there are `m : ℕ` and `R`-algebra maps
  `q : MvPolynomial (Fin m) R ⧸ idealOfVars (Fin m) R ^ (n + 1) →ₐ[R] A ⧸ I ^ (n + 1)` and
  `s` in the opposite direction with `q.comp s = AlgHom.id R _`.
- `finite_projective_quotient_ker_pow ε n`: `A ⧸ I ^ (n + 1)` is a finite and
  projective `R`-module.

### Export

`Algebra.Smooth.finite_projective_quotient_ker_pow ε n` assumes `[Algebra.Smooth R A]`,
takes `ε : A →ₐ[R] R` and `n : ℕ`, and states

```
Module.Finite R (A ⧸ RingHom.ker ε ^ (n + 1)) ∧
  Module.Projective R (A ⧸ RingHom.ker ε ^ (n + 1))
```

## Proof

**Truncated polynomial rings.** The two support conditions, degree `≥ n + 1` and degree
`≤ n`, are disjoint and together cover all exponent vectors. So the two
`restrictSupport` submodules meet in `0`, and their spans together give everything
(`restrictSupport_eq_span`, `restrictSupport_univ`). By `pow_idealOfVars`, the ideal
`idealOfVars σ R ^ (n + 1)` is the first of these submodules. The quotient by it is
therefore linearly equivalent to the complement (`Submodule.quotientEquivOfIsCompl`).
That complement has the basis `basisRestrictSupport` indexed by the exponent vectors of
degree `≤ n`. This basis is finite when `σ` is finite (`Finsupp.finite_of_degree_le`).

**Generators in `I`.** `Algebra.FiniteType.iff_quotient_mvPolynomial''` gives a surjection
`f₀ : MvPolynomial (Fin m) R →ₐ[R] A`. Set `x i = f₀ (X i) - ε (f₀ (X i))` and
`g = aeval x`. Each `x i` lies in `I`. The range of `g` contains every `f₀ (X i)`, so it
contains the range of `f₀`, and `g` is surjective. The composite `ε ∘ g` sends every
variable to `0`, so it is the constant coefficient. Hence `ε (g p) = 0` implies
`p ∈ idealOfVars`, by `mem_pow_idealOfVars_iff'` with exponent `1`.

**The truncated surjection.** Let `J = idealOfVars ^ (n + 1)`. Since `g` maps the
variables into `I`, it maps `J` into `I ^ (n + 1)`. So `g` induces a surjective algebra
map `gq` from the quotient by `J` to `A ⧸ I ^ (n + 1)` (`Ideal.quotientMapₐ`). Let `N`
be the image of `idealOfVars` in the quotient by `J`; then `N ^ (n + 1) = 0`. If `gq`
kills the class of `p`, then `g p ∈ I ^ (n + 1) ⊆ I`, so `p ∈ idealOfVars`. Hence the
kernel of `gq` lies in `N` and is nilpotent.

**The section.** `Algebra.FormallySmooth.lift`, applied with this nilpotent kernel, lifts
the quotient map `A → A ⧸ I ^ (n + 1)` to an algebra map `t` into the quotient by `J`,
with `gq ∘ t` equal to the quotient map (`FormallySmooth.mk_lift`). For `a ∈ I`, write
`t a` as the class of `p`. Then `g p - a ∈ I ^ (n + 1) ⊆ I`, so `ε (g p) = ε a = 0`, and
`t a ∈ N`. Hence `t` maps `I ^ (n + 1)` into `N ^ (n + 1) = 0` and descends to
`s : A ⧸ I ^ (n + 1) →ₐ[R] MvPolynomial (Fin m) R ⧸ J` (`Ideal.Quotient.liftₐ`). The
identity `gq.comp s = AlgHom.id` is checked on classes (`Ideal.Quotient.algHom_ext`).

**Finite projective.** `finite_projective_quotient_ker_pow` uses only the retract
`q.comp s = AlgHom.id` and the truncated polynomial ring results. Since `q ∘ s` is the
identity, `q` is surjective. Its source is finite, so `A ⧸ I ^ (n + 1)` is finite
(`Module.Finite.of_surjective`). Through `s` and `q` it is a linear retract of a free
module, so it is projective (`Module.Projective.of_split`). A smooth algebra is formally
smooth and of finite type, which gives the export.
