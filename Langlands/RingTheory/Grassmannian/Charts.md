# Algebraic charts of the quotient Grassmannian

This module constructs coordinates on a chart of Mathlib's quotient
Grassmannian and gives that chart an explicit coordinate algebra. All rings,
modules and test algebras in these declarations have universe zero. Let `R`
be any commutative ring, `M` any `R`-module with an additive commutative group,
`k : ℕ`, and `x : Fin k → M`. There is no finiteness, freeness,
nontriviality or independence hypothesis on `M`, `R` or `x`.

For a commutative `R`-algebra `A`, Mathlib's
`Module.Grassmannian A (A ⊗[R] M) k` consists of submodules `N` for which the
**quotient** is finite projective and has stalk rank `k`. Write `q_N` for
`N.toSubmodule.mkQ`. The chart consists of those `N` for which

\[
 A^k\longrightarrow(A\otimes_R M)/N,\qquad
 v\longmapsto\sum_i v_i q_N(1\otimes x_i)
\]

is bijective. Here `A^k` is `Fin k → A`; this is a condition on the quotient,
not a rank condition on the submodule.

## Linear coordinates

The namespace `Module.Grassmannian.ChartLinear` contains the following
constructions and their compatibility proofs.

- `Chart` is the subtype just described, and `HomX` is the subtype of
  `R`-linear maps `ψ : M →ₗ[R] (Fin k → A)` satisfying
  `ψ (x j) = Pi.single j 1` for every `j`.
- `cmap` is the displayed linear combination map. `coordEquiv` promotes it
  to an `A`-linear equivalence using the chart's bijectivity proof.
  `toHomX` composes the inverse equivalence with `q_N` and `m ↦ 1 ⊗ m`.
- `ext' ψ` is Mathlib's `ψ.liftBaseChange A`. For `ψ : HomX`, its
  surjectivity follows by lifting `v` to `∑ i, v i ⊗ₜ[R] x i`.
  `quotEquiv` identifies its kernel quotient with `A^k`. `ofHomX` takes
  that kernel as its Grassmannian submodule. Finiteness and projectivity
  are transported through `quotEquiv`; stalk rank is the rank of `A^k`.
  At a prime of `A`, nontriviality of `A` follows from the existence of that
  prime. Thus no global nontriviality assumption is added.
- `ofHomX_toHomX` identifies the kernel with the original submodule, and
  `toHomX_ofHomX` checks the inverse on `1 ⊗ m`. These give `chartEquiv`.
- For `φ : A →ₐ[R] B`, `pushHomX` applies `φ` to every coordinate.
  `map_ofHomX_toSubmodule` identifies Mathlib's actual Grassmannian base
  change with the kernel of the extended coordinate map over `B`. Its
  proof composes the base change of `quotEquiv` with
  `TensorProduct.piScalarRight`. Consequently `map_mem_chart` proves that
  base change stays in the chart, and `chartEquiv_map` proves naturality.

The theorem `Module.Grassmannian.exists_chart_equiv_linearMap` packages
these equivalences simultaneously for every commutative `R`-algebra `A`.
It proves the reconstruction formula

\[
 \sum_i \psi_N(m)_i q_N(1\otimes x_i)=q_N(1\otimes m),
\]

identifies the inverse point's submodule with `ker (ψ.liftBaseChange A)`,
and proves that coordinates after base change are `φ (ψ_N(m)_i)`.
The base-change clause explicitly supplies the chart-membership proof for
the mapped point.

## The coordinate algebra

In `Module.Grassmannian.ChartAlgebra`, let

\[
 T=\operatorname{Sym}_R(M^k),\qquad
 J=\big(\iota(\operatorname{single}_i(x_j))-\delta_{ij}\big)_{i,j},
 \qquad S=T/J.
\]

Here `M^k` is `Fin k → M`, `ι` is the canonical linear map into the
symmetric algebra, and `δᵢⱼ` is `if i = j then 1 else 0` in `T`.
`rels` is the displayed set of generators and `S` is the actual quotient
by its ideal span. This algebra can have infinitely many generators when
`M` is not finite.

For normalized linear coordinates `ψ`, `theta ψ` sends a tuple `(m_i)`
to `∑ i, ψ(m_i)_i`. The lemma `theta_single` evaluates it on a single
coordinate. The induced homomorphism from `T` kills `J`, proved by span
induction, so `toPt` descends it to an `R`-algebra homomorphism `S →ₐ[R] A`.
Conversely, `ofPt` evaluates an algebra homomorphism on the classes of
`ι (Pi.single i m)`. The defining relations imply its normalization at
`x_j`. The two maps are inverse: one equality is checked coordinatewise,
and the other uses quotient and symmetric-algebra extensionality on
single-coordinate generators. They define `homEquivPt`.
`homEquivPt_natural` proves compatibility with postcomposition by every
`R`-algebra homomorphism, again by checking those generators.

The theorem
`Module.Grassmannian.exists_chart_equiv_algHom_symmetricAlgebra_quotient`
composes the linear-coordinate equivalence with `homEquivPt`. It supplies
`J`, its equality with the stated ideal span, and equivalences of the
chart with `S →ₐ[R] A` for every `A`. Evaluation on the class of
`ι (Pi.single i m)` gives the coefficient in the reconstruction formula.
Under base change `φ`, the resulting algebra homomorphism is
`φ.comp (pt A N)`, with an explicit proof that the mapped point is in the
chart.

These are algebraic point equivalences with the stated naturality. This
module does not construct a Grassmannian scheme, prove that its charts
glue, embed it into projective space, construct a Hilbert scheme, or prove
CM representability or a normalized CM comparison. Those remain separate
obligations of the host construction.

## Source, reuse and adaptations

The registered source is `anthropic-flt-complete-lean-source-6e837e75`,
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, retained distribution
SHA-256 `a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`.
The complete originals read for this port are:

- `P2M/Sol/S_Module_Grassmannian_exists_chart_equiv_linearMap.lean`,
  lines 1–238, SHA-256
  `027e32cab2dfbc3a4e0e745d3513e2fe80c3f2ff5312659bfc6abd10833747f0`;
- `P2M/Sol/S_Module_Grassmannian_exists_chart_equiv_algHom_symmetricAlgebra_quotient.lean`,
  lines 1–150, SHA-256
  `d8741ea0b611a6f446a70b05cf687604474b926006f84888c5c4f64fd9aa1e4f`;
- the corresponding `Theorems/Thm_*.lean` files, each lines 1–33, which
  state the two exported theorem types and invoke those solutions.

The port retains the source's universe-zero quantifiers, quotient
convention, hypotheses, constructions, reconstruction identities and
base-change conclusions. The source solution namespaces are renamed to
`Module.Grassmannian.ChartLinear` and
`Module.Grassmannian.ChartAlgebra`, and each `solution` theorem is given
its original exported `Module.Grassmannian` name directly. The wrapper
tactic and `P2M` imports are omitted. Focused Mathlib imports replace the
broad source imports. In `toPt_mk_ι`, an explicit `change` followed by
`SymmetricAlgebra.lift_ι_apply` replaces the original `simp [toPt]` to
handle the pinned Mathlib elaboration behavior. Four local `haveI`/`letI`
bindings use the current `have`/`let` style, and one unused
`LinearEquiv.trans_apply` simplifier argument is removed. No mathematical
hypothesis or conclusion is changed.

The port reuses Mathlib's actual `Module.Grassmannian`, `map`,
`baseChangeMkQ`, tensor base change, quotient equivalence and symmetric
algebra universal property. It adds the chart constructions still listed
as TODO in pinned Mathlib `Mathlib/RingTheory/Grassmannian.lean`.
A search of the current Library and Mathlib found no existing chart
equivalences of this type. The module does not depend on the pending
projective-space adapters or total-presheaf helper.

The original distribution is Apache 2.0 licensed. Its existing published
[LICENSE](../../../licenses/Anthropic-FLT/LICENSE),
[NOTICE](../../../licenses/Anthropic-FLT/NOTICE), and
[ATTRIBUTION](../../../licenses/Anthropic-FLT/ATTRIBUTION.md) apply.
The source attribution table has no separate entry for these two modules.
