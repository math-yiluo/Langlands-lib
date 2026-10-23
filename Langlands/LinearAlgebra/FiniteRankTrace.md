# Genuine trace of finite-rank complex endomorphisms

For an arbitrary complex vector space `V : Type uV`,
`Langlands.finiteRankEnd V` is the existing Mathlib submodule
`LinearMap.finiteRange ℂ V V` of `Module.End ℂ V`. Mathlib defines its
membership by the range being Noetherian. The proved
`mem_finiteRankEnd_iff` identifies this condition with
`FiniteDimensional ℂ T.range`: over a field a finite-dimensional module
is Noetherian, and a Noetherian module is finitely generated.
No topology or finite-dimensionality of `V` is assumed.

The main construction is the complex linear map
`Langlands.FiniteRankEnd.trace : finiteRankEnd V →ₗ[ℂ] ℂ`.
Its value is the ordinary finite-dimensional trace of `T` acting on its
own range. This range is an actual subspace of `V`, finite-dimensional
by membership, and is preserved by `T`. In particular, the construction
does not apply Mathlib's ambient trace to a possibly infinite-dimensional
carrier; that ambient definition has a zero fallback when no finite basis
exists.

## Finite stages and linearity

`FiniteRankEnd.onSubspace T S h` restricts the domain and codomain of `T`
to `S` whenever `h : T.range ≤ S`. Such an `S` is automatically invariant.
The implemented map is `T.codRestrict S ...` composed with the inclusion
`S.subtype`. Its underlying value on `v : S` is exactly `T v`.

`traceValue` first defines the trace on the range. For any
finite-dimensional `S` containing that range,
`traceValue_eq_subspace` proves that the trace of `onSubspace T S h`
equals this value. The proof uses the maps

- `i : range T →ₗ[ℂ] S`, the inclusion;
- `f : S →ₗ[ℂ] range T`, the restriction of `T.rangeRestrict`.

The two composites are the restrictions of `T` to the range and to `S`.
Mathlib's finite-dimensional identity `LinearMap.trace_comp_comm'`
equates their traces. Thus neither a chosen containing stage nor a chosen
basis changes the value; basis independence is already part of Mathlib's
finite-dimensional trace.

For additivity, the proof compares `T`, `U`, and `T + U` on the common
finite-dimensional stage `range T ⊔ range U`. Their restrictions satisfy
the same addition identity, so linearity of finite-dimensional trace
applies. For scalar multiplication, `range T` contains `range (c • T)`,
and the restrictions satisfy the scalar identity. These two proofs bundle
`traceValue` into `trace`. The public `trace_eq_subspace` is the same
comparison law for the bundled map.

## Factorizations and consumer laws

`ofFactorization f g` packages `g ∘ f` as a finite-rank endomorphism of
`V` when `f : V →ₗ[ℂ] W`, `g : W →ₗ[ℂ] V`, and `W` is
finite-dimensional. The finite-range composition lemmas supply membership.
More generally, `trace_eq_of_factorization` proves
`trace T = LinearMap.trace ℂ W (f ∘ g)` whenever `T = g ∘ f`.
It compares `T` with its restriction to `range g`, then applies
`trace_comp_comm'` between the finite-dimensional spaces `range g` and
`W`. Evaluation identifies the resulting composite with `f ∘ g`.
`trace_ofFactorization` specializes this to the packaged construction.

If `V` itself is finite-dimensional, use the factorization of `T`
through `id : V →ₗ[ℂ] V`. This gives `trace_eq_ambient`, agreement with
`LinearMap.trace ℂ V`.

`rankOne ell w` is exactly the map `v ↦ ell(v) • w`, factored through
the scalar space `ℂ`. Its `rankOne_apply` theorem records that value.
The factorization formula and Mathlib's `trace_smulRight` give
`trace_rankOne : trace (rankOne ell w) = ell w`, including the zero cases.

For a linear equivalence `e : V ≃ₗ[ℂ] W`, `conjugate e T` packages
the actual map `w ↦ e (T (e.symm w))`. Its finite-rank property follows
from closure under composition. To prove `trace_conjugate`, factor this
map through `range T` using `T.rangeRestrict ∘ e.symm` and
`e ∘ (range T).subtype`. Their opposite composite is `T` on its range,
because `e.symm (e v) = v`. The factorization law therefore proves
invariance of genuine trace. The carrier universes `uV` and `uW` are
independent; neither ambient carrier is required to be finite-dimensional.

## Derived provenance and scope

This is an internal construction derived from the pinned Mathlib APIs in
`Mathlib.Algebra.Module.LinearMap.FiniteRange`,
`Mathlib.LinearAlgebra.FiniteDimensional.Basic`, and
`Mathlib.LinearAlgebra.Trace`. It reuses the existing finite-range submodule,
finite-dimensionality instances, and basis-independent finite-dimensional
trace. The finite-stage comparisons and resulting infinite-carrier trace
functional are proved here by the arguments above.

The motivating original is Bernstein and Zelevinsky,
*Representations of the group GL(n,F), where F is a non-Archimedean local
field (survey)* (1976), registered as
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Section 2.17, printed/PDF p.21, uses the trace of finite-rank integrated
operators to define an admissible representation's distribution character.
Section 2.18 on that page uses conjugation invariance of trace.
These passages motivate the intended application; they do not supply the
specific Lean implementation or its proof.

This module constructs the linear algebra prerequisite only. It does not
define the character of a representation or prove character separation,
distribution transpose invariance, or the generic contragredient theorem.
