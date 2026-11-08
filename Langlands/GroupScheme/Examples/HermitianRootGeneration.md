# Elementary generation of anisotropic-middle Hermitian special-unitary matrices

This internal continuation combines the proved root, Levi and stabilizer
calculations. It identifies the actual two-root elementary subgroup with
the full determinant-one form-preserving matrix subgroup, under middle
anisotropy and existence of a nonfixed scalar for the involution. The field
and finite middle-index universes are independent; all characteristics and
the empty middle index are allowed.

`firstColumnReducer` is the actual general-linear product of the pure
trace-zero reflection and the inverse upper root recovered from a first
column with nonzero bottom entry. Subgroup closure proves its membership
in the two-root elementary subgroup. `firstColumnReducer_column` proves
that multiplying by it on the left puts the first column on the top axis,
with coefficient `s*M_bottom,top`. The existing inverse-root first-column
identity first leaves only the bottom entry; the pure reflection then
moves it to the top, with the displayed factor `s`.

`specialUnitary_mem_elementarySubgroup_of_bottom_eq_zero` handles the
stabilizer case. The proved stabilizer reduction supplies an upper root
whose inverse times the given matrix has an actual Levi matrix value.
Both factors remain special unitary. Prescribed Levi generation therefore
makes the reduced element elementary, and multiplication by the root
recovers the original element inside the elementary subgroup.

`specialUnitary_mem_elementarySubgroup_of_traceZero` assumes anisotropy,
a supplied nonzero trace-zero scalar `s`, and any actual special-unitary
matrix. If its bottom-top entry is zero, it uses the stabilizer case.
Otherwise the constructed elementary reducer makes that entry zero while
preserving special-unitary membership. The stabilizer result then applies
to the product, and multiplying by the reducer inverse recovers the
original element. `elementarySubgroup_eq_specialUnitarySubgroup_of_traceZero`
combines this inclusion with the established reverse containment.

Finally `elementarySubgroup_eq_specialUnitarySubgroup` replaces the supplied
trace-zero scalar by the hypothesis `∃ a, bar(a)≠a`. The scalar
`s=a-bar(a)` is nonzero, and involutivity gives `s+bar(s)=0`. This argument
uses no division by two, so it also covers characteristic two. The
conclusion is equality of the actual matrix subgroups, not a supplied
generation premise.

The hypotheses concern this anisotropic-middle coordinate model. No
comparison with all rational points of arbitrary classified group schemes,
identification with rational parabolic radicals, or unrestricted local
Kneser–Tits theorem is asserted here. Those remain separate obligations.
