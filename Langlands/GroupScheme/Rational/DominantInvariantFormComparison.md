# Comparing two dominant real characters through a Weyl-invariant form

Module `Langlands.GroupScheme.Rational.DominantInvariantFormComparison`.

## Purpose

Renard VII.4.2 (ii) compares the real parts `Re ψ₁`, `Re ψ₂` of two Langlands
triplets: both are dominant, and the exponent estimates coming from a nonzero
intertwining map place a Weyl conjugate of one above the other modulo a cone of
positive roots. This module supplies the purely combinatorial comparison in the
actual real character space `Vstar T` of a maximal split torus `i : T → G`. It
uses the averaged Weyl-invariant inner product `B = relativeWeylInvariantForm i hT`
(from `Langlands.Geometry.Building.RealTorusInvariantForm`). Renard argues with
the dominance order and the closed positive cone (V.3.18). Here we use an inner
product instead, which needs no projection onto the Levi part. The two-sided
hypothesis replaces Renard's one-sided positivity argument.

All statements are about given `RelativeRootReflectionData D` (coroots
`D.coroot α` with `⟨α, α̌⟩ = 2` and normalizer representatives acting by the
reflection formula). Dominance of `y` means `0 ≤ ⟨y, α̌⟩` for every simple relative
root `α` for the generic cocharacter `ν`.

## Declarations

- `fullRealAction_representative_root`: the supplied reflection of `α` sends
  `1 ⊗ α` to `-(1 ⊗ α)`. This is the reflection formula with `⟨α, α̌⟩ = 2`.
- `two_mul_invariantForm_root`: `2 B(x, α) = ⟨x, α̌⟩ B(α, α)`. Proof: apply
  invariance of `B` under the reflection `s_α` to the pair `(x, α)`. Then
  `B(x - ⟨x,α̌⟩α, -α) = B(x, α)`, and `linarith` concludes.
- `invariantForm_root_nonneg`, `invariantForm_root_eq_zero`: if `⟨y, α̌⟩ ≥ 0`
  (resp. `= 0`) then `B(y, α) ≥ 0` (resp. `= 0`). Both follow from the previous
  identity and `B(α, α) ≥ 0`.
- `invariantForm_positiveRoot_nonneg`: a dominant `y` has `B(y, β) ≥ 0` for every
  positive relative root `β`. The proof uses `positiveRelativeRoots_induction`
  (positive roots are generated from simple roots under addition).
- `invariantForm_weyl_le`: for dominant `x, y` and every `w` in the relative Weyl
  group, `B(y, w x) ≤ B(y, x)`. Proof: the displacement `x - w x` is shown to have
  nonnegative `B(y, -)` by strong induction on Coxeter length. The relative Weyl
  group carries the proved Coxeter structure `relativeWeylCoxeter`. The induction
  is the same as in `ParabolicRootPresentation.restrict_displacement_mem_nonnegCone_of_coxeter`:
  for a right descent `v = v' s_α`, `relativeWeylDisplacement_mul` gives
  `x - v x = (x - v' x) + ⟨x, α̌⟩ v'(α)`, and `v'(α)` is a positive root.
- `invariantForm_self_le_of_mem_restrictedRootNonnegCone` (one half of the
  comparison): let `x, y` be dominant, `J ⊆` simple roots, `y` annihilating the
  coroots of `J`, and suppose the kernel of restriction along `f : A → T` lies in
  the real span of `J`. If `res_f(w x) - res_f(y)` is in the restricted nonnegative
  cone `restrictedRootNonnegCone i ν J f hfin`, then `B(y, y) ≤ B(y, x)`. Proof:
  `mem_restrictedRootNonnegCone_iff_roots` writes the cone element as
  `Σ c_α res_f(1 ⊗ α)` over simple `α ∉ J`, with `c_α ≥ 0`. Lift it to
  `ĉ = Σ c_α (1 ⊗ α)`. Then `z = w x - y - ĉ` restricts to zero, so
  `z ∈ span(J)` and `B(y, z) = 0`. Also `B(y, ĉ) ≥ 0`, and `B(y, w x) ≤ B(y, x)`.
- `eq_of_mutual_mem_restrictedRootNonnegCone` (main result): for dominant
  `y₁, y₂`, annihilating the coroots of `J₁, J₂` respectively, with the span
  hypotheses for `f₁, f₂`: if `res_{f₂}(w₁ y₁) - res_{f₂}(y₂)` lies in the cone of
  `(J₂, f₂)` and `res_{f₁}(w₂ y₂) - res_{f₁}(y₁)` lies in the cone of `(J₁, f₁)`,
  then `y₁ = y₂`. Proof: the one-sided lemma gives `B(y₂,y₂) ≤ B(y₂,y₁)` and
  `B(y₁,y₁) ≤ B(y₁,y₂)`. With symmetry, `B(y₁-y₂, y₁-y₂) ≤ 0`, and positivity of
  `B` forces `y₁ = y₂`. Finiteness of the Weyl group and splitness of `T` come
  from `relativeWeylCoxeter` and `IsMaximalSplitTorus`.
- `selected_eq_of_pair`: if one character `y` annihilates the simple coroots of
  `J₁` and of `J₂`, and is strictly positive on the simple coroots outside each,
  then `J₁ = J₂`.

## Provenance

These lemmas are derived content. They support the comparison of the real parts
in Renard, *Représentations des groupes réductifs p-adiques*, VII.4.2 (ii)
(printed pp.244-246). The inner-product argument is the standard proof that a
dominant weight is maximal in its Weyl orbit for the dominance order. It is not
Renard's printed argument, which goes through V.3.18.
