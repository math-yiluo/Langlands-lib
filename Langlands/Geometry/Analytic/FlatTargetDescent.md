# Flatness descent through the target

Author: Worker 310.

For a tower of commutative algebras `R → S → T`,
`flat_of_faithfullyFlat_target` proves that flatness of `T` over `R`
and faithful flatness of `T` over `S` imply flatness of `S` over `R`.
All three carrier universes are independent.

The proof tests an arbitrary injective linear map of `R`-modules.
Tensoring it with `T` preserves injectivity by flatness over `R`.
The canonical tensor cancellation equivalences identify that map with
the result of first tensoring with `S` and then with `T` over `S`.
Faithful flatness reflects injectivity of the map tensored with `S`,
which is the flatness criterion for `S` over `R`.

This internal supporting lemma is derived from Mathlib's tensor
cancellation, flatness criterion and faithful-flat injectivity criterion.
It asserts no affinoid-domain flatness result.
