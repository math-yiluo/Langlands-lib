# A split torus of dimension the Witt index in the connected isometry group

Author: Worker 350.

Module `Langlands.GroupScheme.Quaternionic.QuadraticHyperbolicSplitTorus`.

## Setting

`K` is a field of any characteristic, finite or infinite. `A` is a `K`-algebra and `R` ranges
over commutative `K`-algebras. In the quaternionic part, `D` is a finite-dimensional division
`K`-algebra, `σ : FirstKindInvolution K D`, `q` a `σ`-quadratic form on `D^n`,
`Q = Quotient.out q` a representing matrix, `τ = σ.matrix n` the involution `X ↦ ᵗX^σ` of
`M_n(D)`, and `T = σ.quadraticKernel n = {X - τ X}`. The published `IsometryCut.defect τ Q u`
is `u (1 ⊗ Q) τ_R(u) - 1 ⊗ Q` for `u ∈ R ⊗ M_n(D)`, and a point `u` of the matrix unit group
lies in `O(q) = σ.isometryGroup q` exactly when its defect lies in `R ⊗ T`
(`mem_range_isometryGroupι_iff`). Everything holds over every coefficient algebra `R`, not only
over rational points, so finite fields and characteristic `2` are covered.

## Scaling a family of orthogonal idempotent pairs (`FiniteAlgebraUnits`)

- `IsOrthogonalIdempotentPairs p p'` (for `p p' : I → A`) says that all `pₖ, p'ₖ` are mutually
  orthogonal idempotents: `pₖ pₗ = δₖₗ pₖ`, `p'ₖ p'ₗ = δₖₗ p'ₖ`, `pₖ p'ₗ = p'ₖ pₗ = 0`.
- `familyScalingSummand p p' R t k = (tₖ - 1)(1 ⊗ pₖ) + (tₖ⁻¹ - 1)(1 ⊗ p'ₖ)` for
  `t : I → Rˣ`, and `familyScalingValue p p' R t = 1 + ∑ₖ familyScalingSummand p p' R t k`. It
  multiplies `pₖ` by `tₖ` and `p'ₖ` by `tₖ⁻¹`. `familyScalingSummand_eq` rewrites the summand as
  `(tₖ - 1) ⊗ pₖ + (tₖ⁻¹ - 1) ⊗ p'ₖ`, and `familyScalingValue_one` is the value at `t = 1`.
- `summand_mul_of_ne`: summands with different indices multiply to `0`. `summand_mul`: writing
  `Xₖ(t)` for the summands, `Xₖ(ts) = Xₖ(t) + Xₖ(s) + Xₖ(t) Xₖ(s)`.
  `familyScalingValue_mul`: hence `v(ts) = v(t) v(s)`. The cross terms of
  `(∑ Xₖ(t))(∑ Xₗ(s))` collapse to the diagonal (`Finset.sum_mul_sum`, `Finset.sum_eq_single`).
- `IsOrthogonalIdempotentPairs.scalingUnits : (I → Rˣ) →* (R ⊗[K] A)ˣ` is the resulting group
  homomorphism with inverse `v(t⁻¹)` (`scalingUnits_val`). `scalingUnits_map` shows that it
  commutes with every coefficient algebra homomorphism `φ : R →ₐ[K] S`.
- `tmul_mul_familyScalingValue`: `(1 ⊗ pⱼ) v(t) = tⱼ ⊗ pⱼ`.
  `eq_zero_of_tmul_eq_zero`: if `a ≠ 0` in `A` and `r ⊗ a = 0` in `R ⊗[K] A`, then `r = 0`
  (apply `rid ∘ (R ⊗ φ)` for a functional `φ` with `φ(a) ≠ 0`).
  `scalingUnits_injective`: if every `pₖ ≠ 0`, then `scalingUnits` is injective, by these two
  lemmas.

## Defects of scaling elements (`IsometryCut`)

- `defect_idempotentScalingValue_mem`: suppose
  `Z₁ = p Q + Q τp - p Q τp' - p' Q τp`, its analogue `Z₂` with `p` and `p'` exchanged,
  `Z₃ = p Q τp` and `Z₄ = p' Q τp'` all lie in a `K`-subspace `M`. Then, for every `R` and
  `t ∈ Rˣ`, the published `idempotentScalingValue p p' R t = 1 + a(1 ⊗ p) + b(1 ⊗ p')`
  (`a = t - 1`, `b = t⁻¹ - 1`) has defect in `R ⊗ M`. Proof: since `ab = -(a + b)`, the
  defect expands (`linear_combination (norm := module)`) to `a Z₁ + b Z₂ + a² Z₃ + b² Z₄`,
  with each `Zᵢ` placed in the second tensor factor. No orthogonality of `p, p'` is used.
- `defect_familyScalingValue_mem`: for a stable subspace `M` (published `IsStable`: `R ⊗ M` is
  preserved by `z ↦ y z τ_R(y)`) and orthogonal idempotent pairs, if each single scaling
  `1 + Xₖ(t)` has defect in `R ⊗ M`, then so does `v(t)`. Proof by induction over finite sets
  of indices: `1 + ∑_{insert j s} X = (1 + Xⱼ)(1 + ∑_s X)` by orthogonality, and the published
  `defect_mul` gives `defect(uv) = u defect(v) τ(u) + defect(u)`.

## The split torus of a hyperbolic family (`FirstKindInvolution.IsHyperbolicFamily`)

Let `(x, y)` be a hyperbolic family (`QuadraticHyperbolicFamily`) indexed by a finite type `I`.
Write `Pₖ = hyperbolicLineMatrix q xₖ yₖ` and `P'ₖ = hyperbolicLineMatrix q yₖ xₖ`. Write
`𝕊 = splitTorus (Spec K) I = 𝔾ₘ^I` and `𝕌` for the unit group scheme of `M_n(D)`
(`FiniteAlgebraUnits.groupScheme` for `Module.finBasis K (Matrix n n D)`).

- `isOrthogonalIdempotentPairs`: `(Pₖ, P'ₖ)` are orthogonal idempotent pairs.
- `defect_familyScalingValue_mem`: for every `R` and `t : I → Rˣ`, the defect of `v(t)` lies
  in `R ⊗ T`. Each pair satisfies the hypotheses of `defect_idempotentScalingValue_mem` with
  `M = T` by `IsHyperbolicPair.lineMatrix_polar_mem` and `lineMatrix_congr_mem` (for `(xₖ, yₖ)`
  and the swapped pair `(yₖ, xₖ)`). `T` is stable (`isStable_alternatingSubspace`).
- `unitTorusPoints` / `unitTorus : 𝕊 ⟶ 𝕌`: the group-scheme homomorphism whose value on a
  `T`-point `t` of `𝔾ₘ^I` (an `I`-tuple of units of `R = Γ(T)`, via `splitTorus.pointsEquiv`)
  is the unit `v(t)` (via `FiniteAlgebraUnits.pointsEquiv`). It is built with the published
  `homOfPoints`; naturality is `scalingUnits_map`, and `pointsEquiv_unitTorus` records its
  value on points.
- `mono_unitTorus`: `unitTorus` is a monomorphism, by `scalingUnits_injective` and
  `lineMatrix_ne_zero`.
- `exists_isometryTorus`, `isometryTorus`, `isometryTorus_comp`: `unitTorus` factors through the
  closed inclusion `O(q) → 𝕌`. The universal point `𝟙 ≫ unitTorus` lies in the range of
  `isometryGroupι q` by `mem_range_isometryGroupι_iff` and `defect_familyScalingValue_mem`. The
  lift is a monoid morphism because the inclusion is a monomorphism (closed immersion,
  `IsClosedImmersion.iff_isFinite_and_mono`).
- `connectedTorus`, `connectedTorus_comp`: when `O(q)` is smooth (needed to form `O(q)⁰`),
  `𝔾ₘ^I` is connected (`IsSplitTorus.connectedSpace`). So `IdentityComponent.factor` factors
  `isometryTorus` through `O(q)⁰ = σ.connectedIsometryGroup q`.
- `mono_connectedTorus`: its composite with `O(q)⁰ → O(q) → 𝕌` is `unitTorus`, a
  monomorphism, so `connectedTorus` is a monomorphism.
- `isClosedSubgroup_connectedTorus`: a split torus mapping monomorphically into an affine group
  locally of finite type is a closed subgroup (`IsTorus.isClosedSubgroup_of_mono`).
- `card_le_splitRank_connectedIsometryGroup`: hence `|I| ≤ splitRank O(q)⁰`
  (`card_le_splitRank`).

## Lower bound

`FirstKindInvolution.quadraticWittIndex_le_splitRank_connectedIsometryGroup`: if `q` is
nondegenerate and `O(q)` is smooth, then `σ.quadraticWittIndex q ≤ splitRank O(q)⁰`. Proof:
`exists_isHyperbolicFamily` gives a hyperbolic family indexed by `Fin r`, with `r` the Witt
index. It is reindexed along `ULift.down` to an index type in universe `u`
(`IsHyperbolicFamily.comp`), and `card_le_splitRank_connectedIsometryGroup` applies.

## Provenance and scope

Internal derived module. Classically, the hyperbolic pairs `(xₖ, yₖ)` of a Witt decomposition
give the split torus `diag(t₁, …, t_r, t₁⁻¹, …, t_r⁻¹, 1, …)` of `O(q)`. Here this torus is
built as a group-scheme homomorphism by its action on points over every coefficient algebra.
The isometry condition is verified by the defect identities above rather than on rational
points, so no infinitude of `K` is needed. The module uses only that `D` is a
finite-dimensional division algebra, nondegeneracy of `q` (for the hyperbolic family), and
smoothness of `O(q)` (for the identity component). It uses no centrality, Tits-type or
characteristic hypothesis.
