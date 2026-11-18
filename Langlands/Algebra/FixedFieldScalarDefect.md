# Actual fixed-field splitting from restricted scalar defects

This internal derived unit proves
`Langlands.CentralSimple.split_over_fixedField_of_coprime_scalarDefect_power`.
Let `L/k` be a finite Galois extension, `A` a finite-dimensional `k`-algebra,
and `e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L` an actual chart with
`n ≠ 0`. Let `H` be any actual subgroup of `Gal(L/k)`. If a power `m` of
the actual chart's unit scalar defect is a coboundary and `m` is coprime
to the order of `H`, then `A` actually splits over the fixed field of `H`:
there is an algebra equivalence from its scalar extension to the same-size
matrix algebra over that fixed field.

The proof first restricts the original scalar cocycle and its power's
trivializing cochain to `H`. The explicit finite-group product cochain
and Bezout calculation from `ScalarTwoCocycleTorsion` trivialize the
restricted scalar defect. The published subgroup/fixed-field Galois
equivalence preserves its actual action on coefficients, so the same
cochain transfers to `Gal(L/Lᴴ)`.

To retain the actual algebra in this comparison, the unit constructs the
algebra equivalence cancelling two successive scalar extensions. This
construction allows a noncommutative algebra and uses the tensor
associator and right-unit equivalence. Its pure-tensor formula shows that
the actual intermediate-field chart action restricts the original action.
The old prescribed matrix lifts and the new chosen lifts thus have the
same actual conjugation action; scalar lift comparison transfers
coboundary triviality. Matrix Hilbert 90 and the earlier fixed-algebra
comparison then construct the claimed actual splitting.

The subsidiary lemmas apply to any intermediate field or any actual
subgroup, as indicated by their types. This unit does not assume that `H`
is Sylow and does not yet assert that its fixed field has odd degree.
