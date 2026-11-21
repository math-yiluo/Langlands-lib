# Local matrix coordinates of rational norm pairs

`rationalLocalNormAssociation` proves `RationalLocalNormAssociationStatement`.
It takes an associated pair in the rational point groups of `GL_n`
and its Weil restriction. The rational norm relation uses the upper
matrices over `L` and base matrices over `K`. The conclusion gives
the norm relation after restricting the same adelic points to any
place of `K`, using the actual local matrices and the actual local
Galois action.

The ordinary localization formula follows by composing the affine
point maps for the rational embedding and the local projection.
For the Weil restriction, the rational coordinates use
`L ⊗[K] K ≃ L`. Naturality of the tensor-valued point equivalence
localizes the entries. Exchanging tensor factors then sends the
upper coefficient `b` to `1 ⊗ₜ b` in `LocalBaseChangeAlgebra`.
The same rational coordinates carry the rational Galois action to
the entrywise action on matrices over `L`.

The upper coefficient map intertwines the global and local Galois
actions and therefore commutes with the ordered cyclic norm.
It also agrees with base scalar extension on `K`. Applying it to
the rational conjugacy equation proves local association.

This is an internal compatibility of the Library point maps used
in the local-to-global matching argument of Henniart–Lemaire,
I.6.1 and I.6.8, printed pp. 39 and 49–50 (PDF pp. 47 and 57–58).
