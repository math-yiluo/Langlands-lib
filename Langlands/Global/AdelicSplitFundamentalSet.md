# Springer's split fundamental-set target on actual adelic points

Author: Worker 83.

This module states the split fundamental-set theorem as an independent
prerequisite for general reduction theory. It proves the inversion
conversion between two actual-point formulations. It does not prove the
split fundamental-set target.

## Right-action property

For a number field `F`, an affine group scheme `G` and the canonical
minimal parabolic `P = Standard.parabolicScheme i ν ∅`,
`HasRightAdelicFundamentalSet F G T i ν` says that there are a compact
set `C ⊆ G(𝔸_F)¹` and a positive unit `c : ℝ≥0ˣ` such that every
`g ∈ G(𝔸_F)¹` has a factorization

`g = x · i(s) · ι_P(p) · rational(q)`,

where `x ∈ C`, `s ∈ T(𝔸_F)`, `i(s) ∈ G(𝔸_F)¹`,
`p ∈ P(𝔸_F)¹`, and `|α(s)| ≤ c` for every simple relative root.
The last factor is a rational point of `G`, on the right. Here `|α(s)|`
is exactly `PositiveRealTorus.normCharacter F T α s`, using the Library's
normalized full idele norm.

The parabolic factor is its **own** norm-one subgroup, defined using all
characters of `P`. Replacing it by `P(𝔸_F) ∩ G(𝔸_F)¹` would permit
unbounded torus factors inside `p` and lose the force of the root bounds.
The torus factor is in the full adelic torus; it is not yet an intrinsic
positive point of the derived torus.

## Split theorem target and scope

`SplitAdelicFundamentalSetStatement` quantifies in universe `u` over
every number field, every connected reductive affine finite-type group
scheme `G`, and every actual algebraic Siegel setup. Its additional
hypothesis is `IsMaximalTorus i`. Since the setup already requires `i`
to be a maximal **split** torus, this is the split-group case. There
is no supplied fundamental set, compact quotient or chamber coverage.

The target includes split tori and empty simple-root sets; Springer states
(F) for isotropic groups, and the split-torus case follows from compactness
of the norm-one idele class group. The compactness of that base case
and the proof of the split theorem remain obligations of a proof of this
statement.

This is a derived actual-scheme formulation of Springer (1994),
§2.1 and §§3.2–3.3. It keeps an arbitrary number field rather than
first restricting scalars to `ℚ`. A proof may use the published
arbitrary-number-field GL(2) reductions, but must supply the actual
scheme-point comparisons, the other split rank-one cases, and the
rank induction. Merely supplying a matrix realization without proved
comparisons does not prove this target.

## Implemented inversion proof

`HasLeftAdelicFundamentalSet` uses the compact set on the right and
the equality

`ι_P(p) · i(s) · x = rational(q) · g`,

with the weak inequalities `t ≤ |α(s)|`. It retains `P(𝔸_F)¹`
and the full torus factor.

`HasRightAdelicFundamentalSet.hasLeft` applies the right property to
`g⁻¹`. If `g⁻¹ = x i(s) ι_P(p) rational(q)`, inversion and left
multiplication by `rational(q)` give
`rational(q) g = ι_P(p⁻¹) i(s⁻¹) x⁻¹`.
The proof takes `C⁻¹` and `t = c⁻¹`. Inversion is continuous on
`G(𝔸_F)¹`, so `C⁻¹` is compact. Homomorphisms preserve inverses,
and `|α(s)| ≤ c` implies `c⁻¹ ≤ |α(s⁻¹)|`.
This explicitly checks the factor order, rational-action side and weak
inequality needed by the eventual chamber theorem.

The intrinsic positive-torus comparison and replacement of `C` by an
arbitrary supplied Iwasawa subgroup are separate obligations. This
module supplies neither of them and proves no nonsplit reduction
theorem.

## Why the split input is separate

Springer's proof order is split (F), then anisotropic compactness (C)
by Galois descent, then nonsplit rank-one (F), and finally rank
induction for general (F). Keeping split (F) independent prevents a
cycle between the general compactness and fundamental-set targets.

## Source

T. A. Springer, *Reduction theory over global fields*, Proc. Indian Acad.
Sci. (Math. Sci.) 104 (1994), 207–216. Registered source:
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
Used: §1.7, printed p.209 (split solvable compactness);
§2.1, printed pp.211–212, definition of `S(c)` and statement (F);
§§3.2–3.3, printed pp.214–215, split reduction and its rank-one input.
The complete paper was read. No Springer errata entry is registered.
