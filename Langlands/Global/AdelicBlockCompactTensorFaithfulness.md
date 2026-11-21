# Faithfulness of the adelic compact tensor section map

`compactTensorSectionMap_injective` assumes that the finite evaluations jointly determine each finite source vector, the infinite evaluations jointly determine each infinite source vector, and the map on coefficient tensors is injective. The resulting map into scalar adelic sections is injective, and `compactTensorSectionRangeEquiv` identifies its source with its linear image.

For a nonzero tensor with a fixed left factor space, the Library supplies a dual functional on that space whose contraction is nonzero. Evaluating the right factor commutes with contraction, as is seen on pure tensors. This proves that faithful evaluations on the right distinguish the whole tensor. First apply this argument after a finite evaluation, then swap the factors and apply it to the finite evaluations. Finally, every pair of compact evaluation points occurs in the actual adelic compact group. If the scalar section vanishes, its normalized compact slices vanish, so injectivity on coefficients makes every paired evaluation zero. The tensor argument then makes the original tensor zero.

This is an internal consequence of the scalar compact model and algebraic dual separation. Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), describe the compact factor and scalar Levi slices for adelic induced sections.
