# Rational complement from restriction to the split center

Author: Worker 1311.

This internal reduction isolates the linear algebra needed for the intrinsic
character/root complement. It uses the published actual character lattices,
relative root span, and rationalized restriction maps. It introduces no
replacement torus or root-system realization.

`Langlands.LinearAlgebra.isCompl_ker_range_of_bijective_comp` works for modules
over any ring: if `f : M → P` and `g : N → M` are linear and `f ∘ g` is
bijective, then `ker f` and `range g` are complementary in `M`. For the
intersection, a vector `g y` in the kernel satisfies `(f ∘ g) y = 0`, so
injectivity gives `y = 0`. For spanning, surjectivity supplies `y` with
`f (g y) = f x`, and the proof writes `x = (x - g y) + g y`. This argument
requires no dimension or nonzero-rank hypothesis.

`Langlands.LinearAlgebra.kerProdEquivOfBijectiveComp` constructs the resulting
linear equivalence `ker f × N ≃ M`, sending `(x, y)` to `x + g y`.
Injectivity of `f ∘ g` makes `g` injective and identifies `N` with its range;
the generic product equivalence of complementary submodules then supplies
the decomposition. The application lemma records its forward formula.

`rationalCharacterRestrictRat_comp` proves contravariant composition for the
existing rationalized restriction. Tensor extensionality reduces it to
precomposition of actual group-scheme characters.

`relativeRootSpan_isCompl_of_centralKernel` applies the module lemma to the
restriction maps of an actual factorization `A → T → G`. It assumes that
restriction from `T` to `A` has the actual relative root span as its kernel
and that rationalized restriction from `G` to `A` is bijective. Composition
identifies the composite with restriction along `A → G`. These are explicit
premises of this conditional helper. In its intended use, `A` is a split
component embedded in a maximal split torus; the helper itself needs neither
centrality nor maximality after the two stated premises have been supplied.

The provenance is internal: the proof is elementary kernel/range algebra and
functoriality of the published restriction maps. It does not prove the
geometric kernel comparison, injectivity or finite-index restriction to a
split component, or the unrestricted complement statement. Those remain
separate proof obligations.
