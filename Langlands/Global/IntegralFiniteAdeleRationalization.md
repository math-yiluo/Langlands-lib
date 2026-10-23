# Rationalization of the integral finite adeles of the rationals

`Langlands.Global.IntegralFiniteAdeleRationalization : Prop` is an internal
statement comparing objects that are already published. It has no parameters
and no hypotheses. It asserts that there exists a `ℚ`-algebra equivalence

```
E : (ℚ ⊗[ℤ] integralFiniteAdeles ℚ) ≃ₐ[ℚ] FiniteAdeles ℚ
```

such that for every rational `q` and every everywhere-integral finite adele `a`,

```
E (q ⊗ₜ[ℤ] a) = algebraMap ℚ (FiniteAdeles ℚ) q * (a : FiniteAdeles ℚ).
```

In words: rationalizing the ring of everywhere-integral finite adeles of `ℚ`
gives back the full finite adele ring of `ℚ`, via the map `q ⊗ a ↦ q · a`.

The Lean file only defines this proposition. It does not prove it, does not
construct or choose an equivalence, and does not assume the statement anywhere.
A separate proof task must establish it.

## Exact objects

- `FiniteAdeles ℚ` is the abbreviation in `Langlands.Global.Adelic` for
  Mathlib's `IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ`.
  This is the restricted product of the actual adic completions
  `v.adicCompletion ℚ` with respect to their valuation subrings. The index set
  is `HeightOneSpectrum (NumberField.RingOfIntegers ℚ)`, the nonzero primes of
  the ring of integers of `ℚ`. No product indexed by the natural primes is used
  in its place.
- `integralFiniteAdeles ℚ` is the published `Subring (FiniteAdeles ℚ)` in
  `Langlands.Global.IntegralFiniteAdeles`. It consists of the finite adeles `a`
  with `a v ∈ v.adicCompletionIntegers ℚ` for every finite place `v`. In the
  tensor product it is used as a type, the subtype of that subring. Its
  commutative ring structure is the one inherited from `FiniteAdeles ℚ`, and
  `(a : FiniteAdeles ℚ)` is the subring inclusion.

The statement does not redefine either ring, and it does not change any
published definition.

## Tensor orientation and algebra structures

The source `ℚ ⊗[ℤ] integralFiniteAdeles ℚ` is Mathlib's algebraic tensor
product `TensorProduct ℤ ℚ (integralFiniteAdeles ℚ)`. The rationals are the
left factor and the integral subring is the right factor. The pure tensors are
written `q ⊗ₜ[ℤ] a`.

- **`ℤ`-structures.** Both factors are tensored over `ℤ` using their canonical
  `ℤ`-module structures, `AddCommGroup.toIntModule`. These are the structures
  of the unique ring maps from `ℤ` (Mathlib's `Ring.toIntAlgebra`). For the
  subring, this `ℤ`-structure comes from the ring structure it inherits. No
  other `ℤ`-action is chosen.
- **Ring structure.** The multiplication on the tensor product is Mathlib's
  `Algebra.TensorProduct.instSemiring`, so
  `(q ⊗ a) * (q' ⊗ a') = (q q') ⊗ (a a')`.
- **`ℚ`-algebra structure on the source.** This is
  `Algebra.TensorProduct.leftAlgebra`, so `ℚ` acts through the left factor. Its
  structure map sends `q` to `q ⊗ₜ 1` (Mathlib's
  `Algebra.TensorProduct.algebraMap_apply`, which holds by `rfl`). In the
  pinned environment, `rfl` checks also confirm that the statement elaborates
  with this instance and with `AddCommGroup.toIntModule` on the subring.
- **`ℚ`-algebra structure on the target.** This is Mathlib's existing
  `FiniteAdeleRing` instance `Algebra K 𝔸ᶠ[R, K]`, built from
  `FiniteAdeleRing.algebraMap`. It is the diagonal embedding: by
  `FiniteAdeleRing.algebraMap_apply`, the coordinate of
  `algebraMap ℚ (FiniteAdeles ℚ) q` at each finite place `v` is the image of `q`
  in `v.adicCompletion ℚ`.

`E` is required to be a `ℚ`-algebra equivalence for these two structures, so it
is a ring isomorphism that commutes with the structure maps. No topology on the
tensor product is defined or asserted, and the statement says nothing about
continuity.

## Pure-tensor normalization

The product on the right of the formula is taken in `FiniteAdeles ℚ`. The
factor `(a : FiniteAdeles ℚ)` is the subring inclusion of `a`. Two special
cases are:

- `E (1 ⊗ₜ a) = a`: on the integral factor, `E` is the inclusion.
- `E (q ⊗ₜ 1) = algebraMap ℚ (FiniteAdeles ℚ) q`: on the rational factor, `E`
  is the diagonal.

So the formula fixes the comparison map. A bare abstract isomorphism between
the two rings does not satisfy the proposition. Pure tensors span the tensor
product additively, so at most one additive map satisfies the formula. The proposition
does not state this uniqueness separately.

Mathematically, the content is that `q ⊗ a ↦ q · a` is bijective. The context
of the requesting task suggests a proof plan. For surjectivity, show that every
finite adele has a common nonzero integer denominator, so that it has the form
`(1/n) · a` with `a` integral. For injectivity, use the fact that tensoring
with `ℚ` over `ℤ` is a localization, for example through
`Mathlib.RingTheory.Localization.BaseChange`, together with the injectivity of
the inclusion. This plan is a pointer only; the Lean file contains no proof.

## Provenance and scope

This is an internal auxiliary statement and is not quoted from any source. It
was requested by Worker 212 for the exact proof task
`a00cc878-6690-45e4-924b-a11707ae6bf1`. That task proves the published
`Langlands.Global.RationalProfiniteIntegerAdeleComparison`. Its second clause
asks for a `ℚ`-algebra equivalence
`(ℚ ⊗[ℤ] ProfiniteIntegerRing) ≃ₐ[ℚ] FiniteAdeles ℚ` with
`q ⊗ a ↦ q · e₀ a`, where `e₀ : ProfiniteIntegerRing ≃+* integralFiniteAdeles ℚ`.
The present proposition is that clause with `ProfiniteIntegerRing` replaced by
the integral subring itself and `e₀` replaced by the inclusion. The parent proof
plans to transport this equivalence along a ring equivalence `e₀`. That
transport is not part of this statement. The proposition is also logically
independent of the comparison between the residue ring and the `p`-adic
product, and it has no prime-to-`p` variant. For the parent's literature
motivation (Harris–Taylor's rational Tate space `TA ⊗_ℤ ℚ`), see the
Markdown of `Langlands.Global.RationalProfiniteIntegerAdeleComparison`. The
present statement makes no further claim about that source.
