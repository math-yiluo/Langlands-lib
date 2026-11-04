# The cokernel of a finitely filtered map from one surviving step

Author: Worker 757 (task `f7d95940-33d0-49d3-93d6-8d5ff8d89373`).

This internal algebraic helper extends the published
`Langlands.Representation.Filtration.FiniteFilteredExactness` (Worker 194).
It computes the actual cokernel `C ⧸ range g` of the last map of a filtered
three-term sequence `A → B → C`. The answer is one step `U (i₀ + 1)` of the
filtration of `C`. The hypotheses are graded surjectivity and graded exactness
in the grades above `i₀`, and vanishing of the step `T (i₀ + 1)` of `B`.
It works over any commutative ring `R`, with independent universes for the
ring and the three modules. It assumes no finite dimension, splitting,
topology, smoothness or representation theory.

All notation is that of `FiniteFilteredExactness`. A filtration is a family
`S : ℕ → Submodule R A`. `Preserves f S T` says that `f` maps each `S i` into
`T i`. `Graded S i` is the actual quotient of `S (i + 1)` by the inverse image
of `S i`, and `gradedMap f S T hf i` is the map induced by `f` on these
quotients.

## Declarations

For `f : A →ₗ[R] B`, `g : B →ₗ[R] C` and filtrations `S, T, U` preserved by
`f` and `g`:

* `reduction_of_graded_surjective`: assume `gradedMap g T U hg i` is
  surjective. Then every `c ∈ U (i + 1)` has some `b ∈ T (i + 1)` with
  `c - g b ∈ U i`. The proof lifts a preimage of the class of `c` along the
  actual quotient map and compares classes. No section is chosen.
* `exists_sub_mem_of_graded_surjective`: let `U` be monotone and let the
  graded maps of `g` be surjective in every grade `i` with `i₀ < i < n`.
  Then for every `j ≤ n` and `c ∈ U j` there is some `b` with
  `c - g b ∈ U (i₀ + 1)`. This is induction on `j`. Grades `j ≤ i₀ + 1`
  take `b = 0` by monotonicity. A higher grade applies the one-step
  reduction, then the induction hypothesis, and adds the two preimages.
* `map_eq_zero_of_graded_exact`: let `T` and `U` be monotone, `g (f a) = 0`
  for all `a`, and `T (i₀ + 1) = ⊥`. Let the graded sequences be exact at
  `B` (`range (gradedMap f) = ker (gradedMap g)`) in every grade `i` with
  `i₀ < i < n`. Then for every `j ≤ n`, every `b ∈ T j` with
  `g b ∈ U (i₀ + 1)` satisfies `g b = 0`. Again this is induction on `j`.
  At grades `j ≤ i₀ + 1` the vector `b` lies in `T (i₀ + 1) = ⊥`. At a
  higher grade, `g b ∈ U (i₀ + 1) ⊆ U j` by monotonicity. The published
  one-step `reduction_of_graded_exact` then gives `a` with `b - f a ∈ T j`.
  The remainder has the same image under `g`, because `g ∘ f = 0`.
* `bijective_cokernel_of_graded`: add the hypotheses `T n = ⊤` and `U n = ⊤`
  to those of the last two items, with graded surjectivity of `g` and graded
  exactness in every grade `i₀ < i < n`. Then the composite
  `(range g).mkQ ∘ₗ (U (i₀ + 1)).subtype` is bijective. This composite is
  the inclusion of the surviving step followed by the actual cokernel
  quotient. Injectivity: if `x ∈ U (i₀ + 1)` is `g b`, the previous item with
  `j = n` gives `g b = 0`. Surjectivity: by the second item, every
  `c ∈ C = U n` differs from `U (i₀ + 1)` by an element of `range g`.
* `cokernelEquiv`: the resulting linear equivalence
  `U (i₀ + 1) ≃ₗ[R] C ⧸ range g`, `LinearEquiv.ofBijective` of the composite
  above. `cokernelEquiv_apply` says that it sends `x` to the class of `x`.
  The map is canonical: it is the actual inclusion followed by the actual
  quotient. So the equivalence is natural for any commuting family of such
  sequences once the maps preserve the filtrations. This module states no
  such naturality lemma.

## Scope

The provenance is internal. These are direct finite inductions on actual
quotient representatives, in the style of `FiniteFilteredExactness`. The
intended use is the terminal step of the Aubert support-filtration argument.
There `g` is the Jacquet image of the last differential of the complex whose
cokernel is the retained cokernel, `f` is the preceding differential, and the
filtrations are the corrected support filtrations. The surviving step is the
open-cell step, the only grade without graded vanishing. This module proves
none of the inputs needed for that application: the finite filtration, its
preservation by the differentials, graded surjectivity or exactness, or
`T (i₀ + 1) = ⊥`. It makes no assertion about a smooth representation, a
Jacquet module or a Bruhat cell.
