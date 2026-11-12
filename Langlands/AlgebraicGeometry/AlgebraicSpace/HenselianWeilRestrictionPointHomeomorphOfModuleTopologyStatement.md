# Corrected finite Weil restriction point homeomorphism

Author: Worker 172. The statement follows Worker 105's published transcription
in `SpaceWeilRestrictionStatement`; the source correction and counterexample
were identified by Worker 111.

`Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianWeilRestrictionPointHomeomorphOfModuleTopologyStatement`
states Conrad's Proposition 5.11(1) with the additional hypothesis
`IsModuleTopology K K'`. This is a correction of the source wording, not a
literal transcription. This module defines a proposition and contains no
proof of it.

## Precise content

Let `K` and `K'` be nontrivially normed fields in the same universe with
`NormedAlgebra K K'`, `FiniteDimensional K K'`, and `IsModuleTopology K K'`.
Assume `IsHenselianValuedField K` and `IsHenselianValuedField K'`. For every
algebraic space `Y'` over `Spec K'` satisfying `IsQuasiSeparated Y'` and
`FiniteTypeOverRing K' Y'`, the proposition asserts the existence of

```lean
h : IsAlgebraicSpace _ ((ringWeilRestriction K K').obj Y'.toSheaf)
```

such that the canonical equivalence
`ringWeilRestrictionBasePointsEquiv K K' Y' h` is a homeomorphism from
`etaleChartTopology K (ringWeilRestrictionSpace K K' Y' h)` to
`etaleChartTopology K' Y'`.

The fields, sheaves, algebraic spaces and point maps are the existing Library
objects. `NormedAlgebra` makes the extension compatible with the given norms.
`IsHenselianValuedField` means that the norm extends uniquely to algebraic
extension fields. `FiniteTypeOverRing` means existence of an étale surjective
scheme atlas whose structure morphism is locally of finite type and
quasi-compact. Together with the explicit quasi-separatedness hypothesis, this
is the finite-type scope used here.

The restriction sheaf sends a `K`-scheme `T` to `Y'(T ×_K K')`; `h` supplies
its algebraic-space structure. The displayed equivalence is the actual
adjunction bijection `Res(Y')(K) ≃ Y'(K')`, using the canonical identification
`K' ⊗[K] K ≅ K'`. The two étale-chart topologies are defined independently as
final topologies for finite-type étale scheme charts with their scheme point
topologies. Neither topology is transported through this equivalence.

Representability is part of the conclusion. The proposition does not take
representability, quasi-separatedness or finite type of the restriction as an
additional premise. Conrad's Lemma 5.10 supplies those geometric facts for
finite projective ring maps; its exact proof is a separate obligation of
Task 5255.

## Correction of Conrad's wording

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*,
December 31, 2011, Example 2.4 (printed p.3) and Proposition 5.11(1) with its
proof (printed p.18). Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Example 2.4 assumes that the topology on the finite locally free algebra is
the quotient topology from a finite free module. For a finite-dimensional
field extension, this is the module topology: a basis identifies `K'`
homeomorphically with a finite product of copies of `K`. Mathlib expresses the
condition as `IsModuleTopology K K'`.

The proof of Proposition 5.11(1) invokes that affine Weil restriction
homeomorphism, but the printed proposition assumes only a finite extension of
henselian valued fields. Henselianity alone does not supply the module
topology for arbitrary inseparable extensions of incomplete fields. The
literal proposition and the faithfully transcribed
`HenselianWeilRestrictionPointHomeomorphStatement` therefore fail in that
generality. Their existing Lean file is left unchanged.

Complete `K` does supply the condition for finite-dimensional normed
extensions, by Mathlib's `isModuleTopologyOfFiniteDimensional`. Completeness
is sufficient, but is not imposed here. The only added hypothesis is
`IsModuleTopology K K'`; arbitrary finite extensions, including inseparable
ones, archimedean and nonarchimedean fields, and incomplete fields satisfying
that hypothesis remain covered. There is no separability, local
separatedness, separatedness, smoothness or scheme hypothesis.

## Concrete obstruction without the correction

Fix a prime `p`, give `M = F_p((t))` its `t`-adic norm with `|t| = 1/2`, and
choose `s ∈ M` transcendental over `F_p(t)`. Let `K` be the henselization of
`K_0 = F_p(t,s^p)` inside `M`, and put `L = K(s)`, with the restricted norms.
The extension `K/K_0` is separable algebraic, while `s` is purely inseparable
of degree `p` over `K_0`. Consequently `s ∉ K` and `[L:K] = p`. The field `K`
is henselian and its algebraic extension `L` is henselian. Since `F_p(t)` is
dense in `M`, the completions of both fields are `M`; in particular `K` is a
dense proper subfield of `L`, and both are incomplete.

For `Y' = A¹_L`, the Weil restriction is `A^p_K`. In the basis
`(1,s,...,s^(p-1))`, its canonical point bijection is

```text
f : K^p → L,     f(x_0,...,x_(p-1)) = Σ_i x_i s^i.
```

Choose Laurent-polynomial truncations `a_n ∈ F_p(t)` converging to `s`.
Then `f(-a_n,1,0,...) = s-a_n → 0`, while the vectors `(-a_n,1,0,...)`
do not converge to zero: their second coordinate is constantly `1`, outside
the open neighborhood `|x_1| < 1` of zero. Thus the inverse of `f` is
discontinuous. Scheme affine-space point topologies are the product
topologies; the Library comparison `isHomeomorph_schemeRingPointsEquiv`
identifies them with the étale-chart topologies. This already contradicts the
unrestricted proposition for a separated affine scheme of finite type.
It also shows that `IsModuleTopology K L` fails in this example.

The valued-field ingredients come from Michael Temkin, *Valued Fields*
(course notes), Exercise 1.8.11(i)–(ii), printed p.22; Lemma 1.9.3(ii),
printed p.24; and Theorem 1.9.5, Remark 1.9.6 and Section 1.9.7, printed
p.25. Registered source: `temkin-valued-fields-2018-course-notes`, SHA-256
`60cbfd7681abcb39ee111aff005434bd6b11054089cf48a78068c97e3d53abe3`.
The PDF states no date; the year in the registration ID is not an edition
claim. Exercise 1.8.11 gives inseparable extensions with the same completion,
and Remark 1.9.6 warns that a henselian discrete valuation field can fail to
be algebraically closed in its completion. The particular henselized example
and its application to Weil restriction are derived here, following
[Worker 111's published obstruction note](../../../notes/conrad-adelic/finite-weil-inseparable-obstruction.md);
they are not a Weil restriction theorem attributed to Temkin or a Lean
refutation in this module.
