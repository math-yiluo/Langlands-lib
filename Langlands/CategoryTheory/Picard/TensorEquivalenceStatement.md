# Tensor inverses and equivalences

`Langlands.CategoryTheory.Picard.TensorInvertibilityEquivalenceStatement` states that, in a braided monoidal category `C`, an object `L` has an object `N` with `L ⊗ N ≅ 𝟙_ C` if and only if the functor `F ↦ L ⊗ F` is an equivalence of categories. The existential asks only for existence of an isomorphism, through `Nonempty`; no inverse or equivalence is an input assumption.

The category's object universe `u` and morphism universe `v` are independent. There is no smallness claim. The monoidal and braided structures are explicit hypotheses of this generic categorical statement. In the eventual application to `X.Modules`, these must come from the constructed sheaf tensor product; this file supplies no scheme instance.

This is a derived categorical abstraction of the first equivalence in Stacks Project Lemma 17.25.2. Definition 17.25.1 identifies invertibility of a sheaf with equivalence of left tensoring. The first paragraph of the proof of Lemma 17.25.2 uses essential surjectivity for one direction and tensoring with an inverse for the other. Those arguments require only monoidal associativity, unitors, and a braiding. The source itself states the result for ringed spaces, not arbitrary braided categories.

The statement makes no assertion about local freeness, finite presentation, or identification of the inverse with an internal Hom. Those further conclusions of Lemmas 17.25.2 and 17.25.4 need separate sheaf-theoretic arguments. This file defines a proposition and does not prove it.

Source: The Stacks Project Authors, *The Stacks Project*, Section 17.25, retained file `01CR.html`, Definition 17.25.1 and Lemma 17.25.2 (equivalence of (1) and (2), first proof paragraph). Registered source `stacks-local-freeness-invertibility-sections-2026-10-21`, content SHA-256 `6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`, HTML snapshot 2026-10-21. Retained folder: `literature/Stacks Project - Locally free sheaves and invertible modules, Sections 17.14 and 17.25 (HTML snapshot 2026-10-21)/`.
