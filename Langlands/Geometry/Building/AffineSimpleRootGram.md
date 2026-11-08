# The Gram matrix of the simple affine roots of a chamber

Fix `hΨ : IsAffineRootSystemWithRankZero Ψ` on a real affine space `A` over `V`
(independent universes `uV`, `uA`). This module builds the linear-algebra
input for the existence of faces of a chamber with prescribed simple-root types.
It gives a symmetric positive semidefinite form on `V*` and the sign
properties of the Gram matrix of the simple roots.

Source correspondence: the coroot vectors are those of AR 2 in KP Definition
1.3.1 (printed p. 14), via the existing `IsCoroot`. The simple affine roots and
simple reflections are the existing `simpleAffineRoots` and
`chamberSimpleReflections` (KP Definition 1.3.19). The form, the reflection
identity and the Gram sign properties are internal deductions from these
definitions and the existing APIs. They introduce no external assertion. KP's
own route to chamber geometry (Remark 1.3.16, Proposition 1.3.22) cites
Bourbaki and is not reproduced.

## Chosen simple roots

For `s ∈ chamberSimpleReflections Ψ C`, `chamberSimpleRoot s` and
`chamberSimpleCoroot s` are a simple affine root of `C` and a coroot of it whose
reflection is `s`. They are chosen from the membership witness.
`chamberSimpleRoot_mem`, `isCoroot_chamberSimpleCoroot` and
`coe_eq_affineReflection_chamberSimpleRoot` record these properties.
`apply_eq_self_iff_chamberSimpleRoot` states that `s` fixes `x` exactly when
its chosen root vanishes at `x`, by the existing
`affineReflection_apply_eq_self_iff`.

## Coroot vectors and the form

`corootSet Ψ` is the set of all coroot vectors `v` (`IsCoroot Ψ ψ v` for some
`ψ ∈ Ψ`).

`IsCoroot.reflect`: if `u` is a coroot of `ψ` and `v` a coroot of `η`, then
`v - ψ̇(v) u` is a coroot of `η - η̇(u) ψ`. The value `2` is checked by
expanding. For the stability clause, `ζ - ζ̇(v - ψ̇(v)u)(η - η̇(u)ψ)` is shown
to equal the root obtained from `ζ` by reflecting in `ψ`, then in `η`, then in
`ψ`, by an `ext`/`ring` computation.

`coroot_eq_of_linear_eq`: roots with the same derivative have the same coroot.
As in the existing `isCoroot_unique`, both coroots give reflections of `V*`
preserving the finite spanning set `derivativeRoots Ψ`, and Mathlib's
`Module.Dual.eq_of_preReflection_mapsTo` identifies them.
`finite_corootSet` follows. The coroot set is covered by the finitely many
derivative fibers, and each fiber contributes at most one vector.

`corootForm α α' = Σ_{v ∈ corootSet Ψ} α(v) α'(v)`, a finite sum.
`corootForm_comm` and `corootForm_self_nonneg` give symmetry and positive
semidefiniteness. `corootForm_self_pos` shows `β(ψ̇, ψ̇) > 0` for `ψ ∈ Ψ`,
because the coroot `u` of `ψ` contributes `ψ̇(u)² = 4`.

`two_mul_corootForm`: for a coroot `u` of `ψ` and any `α`,
`2 β(α, ψ̇) = α(u) β(ψ̇, ψ̇)`. The map `r(v) = v - ψ̇(v) u` sends the coroot set
to itself (by `IsCoroot.reflect` and AR 2) and is an involution. Reindexing the
sum by `r` (`Finset.sum_nbij'`) and using `α(r v) = α(v) - ψ̇(v) α(u)` and
`ψ̇(r v) = -ψ̇(v)` gives `β(α, ψ̇) = -β(α, ψ̇) + α(u) β(ψ̇, ψ̇)`.

## Simple roots of a chamber

Now let `c` be regular and `C = facet Ψ c`.

`eq_of_chamberSimpleRoot_eq_smul`: if the chosen root of `t` is `r` times that
of `s`, then `t = s`. The scalar is nonzero because roots are nonconstant, and
the existing `affineReflection_eq_of_eq_smul` identifies the reflections.

`exists_panel_point`: for each simple reflection `s` there is `p` in the
closure of `C` with `ψ_s(p) = 0` and `ψ_t(p) > 0` for every other simple
reflection `t`. The wall clause of `simpleAffineRoots` supplies a facet
`facet Ψ y` in the closure whose affine span is the hyperplane of `ψ_s`. Take
`p = y`. Simple roots are nonnegative on the closure
(`mem_facetClosure_iff_simple_nonneg`). If `ψ_t(y) = 0`, then `ψ_t` vanishes on
`facet Ψ y` (facet-related points have the same root signs). So the hyperplane
of `ψ_s` lies in that of `ψ_t` (`affineSpan_le`), hence `ψ_t` is a multiple of
`ψ_s` (`eq_smul_of_hyperplane_le`) and `t = s`.

`linear_chamberSimpleCoroot_nonpos`: for `s ≠ t`, `k = ψ̇_s(ψ̇_t∨) ≤ 0`.
Otherwise the root `η = ψ_s - k ψ_t` (AR 2) satisfies `η(p) = -k ψ_t(p) < 0` at
the panel point `p` of `s`, and `η(q) = ψ_s(q) > 0` at the panel point `q` of `t`.
Both points lie in the closure, where every root has either sign zero or its
sign at `c`. This is impossible.

`mul_comm_of_linear_chamberSimpleCoroot_eq_zero`: if `ψ̇_s(ψ̇_t∨) = 0` and
`ψ̇_t(ψ̇_s∨) = 0`, then `s t = t s`. Each reflection leaves the other root
unchanged, so both products send `x` to
`(-ψ_s(x)) • ψ̇_s∨ + (-ψ_t(x)) • ψ̇_t∨ +ᵥ x`.

## The Gram matrix

`chamberSimpleGram s t = β(ψ̇_s, ψ̇_t)`. `chamberSimpleGram_comm` gives symmetry,
`chamberSimpleGram_self_pos` positive diagonal entries, and
`two_mul_chamberSimpleGram` the identity
`2 G(s,t) = ψ̇_s(ψ̇_t∨) G(t,t)`.

`chamberSimpleGram_nonpos`: for `s ≠ t` in the chamber of `c`, `G(s,t) ≤ 0`, by
the identity and `linear_chamberSimpleCoroot_nonpos`.

`chamberSimpleGram_ne_zero`: if `s t ≠ t s`, then `G(s,t) ≠ 0`. If it vanished,
the identity in both orders would make both Cartan integers zero, and the
reflections would commute.

## Scope

These results concern one chamber of an abstract affine root system, rank zero
allowed. They prove no structure theorem for the kernel of the Gram matrix and
construct no faces of `C`. They prove no witness of
`RootValuationBuildingConstructionStatement`.
