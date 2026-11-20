# Natural Kummer cocycles in a central kernel

`kummerKernelCocycle` forms a natural cocycle valued in the actual kernel of a central isogeny equipped with an isomorphism from its kernel to `μ_n`. Its coefficients are the inverse images of the Kummer values under the roots-of-unity equivalence. The character to the multiplicative group is injective on these coefficients. Its naturality and the Kummer crossed identity therefore verify the hypotheses for forming the natural cocycle.

`exists_unit_radical_in_finiteGalois_refinement` finds an `n`-th root of a base-field unit after a finite Galois extension of a supplied finite coefficient field in characteristic zero. It chooses a root in the algebraic closure, adjoins the root, and passes to the Galois closure over the base. These internal results supply the global correction in the adjoint Hasse argument.
