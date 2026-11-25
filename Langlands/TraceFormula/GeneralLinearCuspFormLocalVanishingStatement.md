# Cusp forms at one finite place give vanishing two-block unipotent integrals (statement)

Module `Langlands.TraceFormula.GeneralLinearCuspFormLocalVanishingStatement` contains one
proposition definition and no proof:

- `Langlands.TraceFormula.GeneralLinearCuspFormLocalVanishingStatement.{u}`.

The simple trace formula for `GL_n` is applied to test functions whose component at one finite
place `v` is a cusp form: all its constant terms along proper parabolic subgroups vanish. The
Library expresses this local condition as `Langlands.BaseChange.HasVanishingConstantTerms`
(module `Langlands.BaseChange.CuspForm`). The statements of this program that produce
cuspidal image and trace class (`GeneralLinearCuspidalImageStatement` and
`GeneralLinearRadicalIntegralVanishingStatement`) instead take as hypothesis the vanishing of
integrals over two-block unipotent subgroups at `v`, written in matrix coordinates. This
statement connects the two: the first condition implies the second.

## Notation from the Library

All names below are in the Library; the statement defines nothing new.

- `K` is a number field and `v : Langlands.Global.FinitePlace K` a finite place.
  `FiniteCompletion K v` is the completion `K_v`. `GeneralLinear n R` is
  `Matrix.GeneralLinearGroup (Fin n) R`, with Mathlib's topology on units.
- `AdelicGL K n` is `GL_n(𝔸_K)`. `FiniteAdelicGL.localInclusion K n v : GL_n(K_v) → GL_n(𝔸_{K,f})`
  puts a matrix at `v` and the identity matrix at every other finite place, and
  `AdelicGL.ofFinite K n` puts a finite-adelic matrix into `GL_n(𝔸_K)` with the identity at
  the infinite places. Their composite is written `ι_v` below.
- `blockUnipotent h Z`, for `h : a + b = n` and `Z` an `a × b` matrix, is the matrix
  `[[1, Z], [0, 1]]` in `GL_n`, with the first `a` coordinates in the first block
  (`Langlands/Group/GL/BlockUnipotent.lean`).
- `Langlands.BaseChange.HasVanishingConstantTerms φ` (`Langlands/BaseChange/CuspForm.lean`),
  for `φ : GL_n(R) → ℂ`, says: for every standard block shape `B` with at least two blocks and
  every Haar measure `μ` on the unipotent radical `U_B` of the standard upper block parabolic
  (Borel σ-algebra of `GL_n(R)`, subspace σ-algebra on `U_B`), and for all `x, y ∈ GL_n(R)`,
  the function `u ↦ φ(x u y)` is `μ`-integrable on `U_B` and `∫_{U_B} φ(x u y) dμ(u) = 0`.

## Statement

For every number field `K` (in universe `u`), every `n`, every finite place `v` and every
`f : GL_n(𝔸_K) → ℂ`, assume:

- (cusp form at `v`) for all `x, y ∈ GL_n(𝔸_K)`, the function
  `g ↦ f(x · ι_v(g) · y)` on `GL_n(K_v)` satisfies `HasVanishingConstantTerms`.

Then for all `a, b` with `h : a + b = n`, `0 < a` and `0 < b`, every additive Haar measure `ν`
on `a × b` matrices over `K_v` (with the Borel σ-algebra) and all `x, y ∈ GL_n(𝔸_K)`:

`∫ f(x · ι_v(blockUnipotent h Z) · y) dν(Z) = 0`.

In words: if every local slice of `f` at `v` (every two-sided adelic translate of `f`, restricted
to the copy `ι_v(GL_n(K_v))`) is a cusp form, then the integral of `f` over every two-sided
adelic translate of every upper two-block unipotent subgroup `{[[1, Z], [0, 1]]}` of
`GL_n(K_v)`, inserted at `v`, vanishes, for every Haar measure on the matrix coordinates `Z`.

The conclusion is, word for word, the local hypothesis of `GeneralLinearCuspidalImageStatement`
for `f`, and also the local hypothesis of `GeneralLinearRadicalIntegralVanishingStatement`, which
writes `F` for the number field `K`. The statement assumes
nothing about continuity, measurability or support of `f`; it only transfers the vanishing
integrals.

Remark (not part of the statement). For `f = f_v ⊗ f^v` (a product of a function `f_v` on
`GL_n(K_v)` and a function `f^v` of the other components),
`f(x ι_v(g) y) = f^v(x^v y^v) · f_v(x_v g y_v)`, so the hypothesis follows from
`HasVanishingConstantTerms f_v`: the Library proves that this property is preserved by left and
right translation and by multiplication by a complex constant
(`HasVanishingConstantTerms.comp_mul_left`, `comp_mul_right`, `const_mul` in
`Langlands.BaseChange.CuspForm`). This module neither states nor proves that deduction.

## Why it is true

Fix `a, b, h, ν, x, y`. Let `B` be the block shape with two blocks of sizes `a` and `b`
(`B.length = 2`). The Library numbers block coordinates consecutively (`B.indexEquiv` is
`finSigmaFinEquiv`), as `blockUnipotent` does (`finSumFinEquiv`), so the unipotent radical
`U_B` of the standard parabolic is exactly `{blockUnipotent h Z}`.

1. `Z ↦ blockUnipotent h Z` is an injective continuous homomorphism from the additive group of
   `a × b` matrices onto `U_B` (`blockUnipotent_add`), and its inverse (reading the upper right
   block) is continuous. So it is an isomorphism of topological groups onto `U_B`, and a
   measurable equivalence between the Borel σ-algebra on matrices and the subspace σ-algebra
   on `U_B` induced by the Borel σ-algebra of `GL_n(K_v)` (which is the Borel σ-algebra of the
   subspace topology).
2. Hence the image measure `μ` of `ν` on `U_B` is a Haar measure: it is left invariant because
   the map is a group isomorphism, finite on compact sets and positive on nonempty open sets
   because the map is a homeomorphism.
3. Apply the hypothesis at the adelic `x, y` with the block shape `B`, the measure `μ` and the
   local translates `1, 1`: `∫_{U_B} f(x ι_v(u) y) dμ(u) = 0`. By the change of variables
   formula for the image measure this integral equals `∫ f(x ι_v(blockUnipotent h Z) y) dν(Z)`.

## Source and what is derived

Derived content; no single source states it. It is a change of coordinates between two
formulations of the cusp-form condition at one place that the sources use.

- Getz–Hahn, *An introduction to automorphic representations* (2024), registered
  `getz-hahn-2024-automorphic-representations`, printed p. 430 (PDF p. 438). Definition 16.4.1
  calls `f_v ∈ C_c^∞(G(F_v))` supercuspidal if `∫_{N(F_v)} f_v(g n h) dn = 0` for every proper
  parabolic subgroup with unipotent radical `N` and all `g, h ∈ G(F_v)`. The Library's
  `HasVanishingConstantTerms` is this kind of condition for `GL_n`, imposed on the standard
  block parabolics, for every Haar measure on the radical and together with integrability.
  The proof of Lemma 16.4.2 (`R(f)` has cuspidal image when `f = f_v ⊗ f^v` with `f_v`
  supercuspidal) uses this vanishing for the unipotent radicals at `v`;
  `GeneralLinearCuspidalImageStatement` states that lemma for `GL_n` with the hypothesis in the matrix coordinates of the present conclusion.
- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique
  non nulle* (2011), II.6.3, printed p. 120 (PDF p. 128): the simple trace formula is stated
  under the condition `c_{v₁}(f)`, that the component `f_{v₁}` at one place `v₁` vanishes off
  the regular elliptic elements and is a linear combination of coefficients of irreducible
  smooth cuspidal representations of `G(F_{v₁})`. The Library models the cusp-form part of this
  condition by `HasVanishingConstantTerms`; the present module uses only that
  predicate and claims nothing about coefficients of cuspidal representations.

The step from the cusp-form condition to the matrix-coordinate hypothesis of
`GeneralLinearCuspidalImageStatement` and `GeneralLinearRadicalIntegralVanishingStatement`,
together with the choice of these exact quantifiers, is internal to this project.

## Relation to other statements

- `HasVanishingConstantTerms` is in the Library module `Langlands.BaseChange.CuspForm`.
- `Langlands.TraceFormula.GeneralLinearCuspidalImageStatement` and
  `Langlands.TraceFormula.GeneralLinearRadicalIntegralVanishingStatement` take the
  conclusion of this statement as hypothesis (the latter with `F` in place of `K`). This
  statement imports neither.
- The proof of this statement is `generalLinearCuspFormLocalVanishing`, in the separate module
  `Langlands.TraceFormula.GeneralLinearCuspFormLocalVanishingProof`.

## What this module does not claim

It does not claim that any particular function is a cusp form. The Lean statement does not
mention supercuspidal representations, cuspidal image or trace class, and it does not claim
the converse implication.
