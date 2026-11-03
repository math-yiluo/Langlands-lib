# Finite image prescription in profinite abelian groups

Author: Worker 1232.

These generic lemmas give a derived route to the subgroup-separation step in
Artin and Tate, *Class Field Theory* (AMS Chelsea, 2009), Chapter X, Section 2,
Theorem 4, printed p.79 (one-based PDF p.88). The registered source is
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The source proves a more general separation argument for its prescribed local
subgroup, using a comparison of two topologies. The present lemmas instead
assume that the ambient quotient is profinite and the relevant image is finite.
They are internal deductions from elementary subgroup algebra and Mathlib's
proved profinite open-subgroup neighborhood theorem. They do not assert that
the arithmetic hypotheses of this route hold for idele classes.

`exists_open_subgroup_inf_eq` takes subgroups `D ≤ H` of a Hausdorff compact
totally disconnected abelian topological group `Q`, with `H` finite. It constructs
an open finite-index subgroup `M` such that `H ⊓ M = D`. The finite set `H \ D`
is closed and avoids the identity. Mathlib's
`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` gives an open normal
subgroup `W` avoiding it. Set `M = D ⊔ W`. If an element of `H` is a product of
an element of `D` and an element of `W`, the latter factor also lies in `H`,
hence in `D`. This proves the intersection identity. Openness follows because
`M` contains `W`; compactness of `Q` makes its discrete quotient finite.

`exists_open_subgroup_comap_eq_of_finite_range` applies this to the finite range
of a homomorphism `g : A → Q` and its subgroup `g(U)`. If `ker g ≤ U`, the
preimage of `g(U)` is exactly `U`, so the constructed subgroup has preimage
`U`. The source group has an independent unrestricted universe and needs no
topology; the target universe is unrestricted as well.

`exists_open_subgroup_through_profinite_quotient` takes a continuous homomorphism
`f : A → C`, a subgroup `P` of an abelian topological group `C`, a Hausdorff
compact totally disconnected quotient `C/P`, and finiteness of the image of
`A` in that quotient. If `f⁻¹(P) ≤ U`, it constructs an open finite-index
subgroup `N` of `C` containing `P` and satisfying `f⁻¹(N) = U`. The preceding
lemma supplies a subgroup of `C/P`; continuity of the quotient map supplies
openness after pullback, and finite index also pulls back. No topology
comparison between the product domain and its image is needed.

`exists_open_subgroup_from_power_intersection` specializes this to power
subgroups. For natural numbers `m` and `n`, assume `A/A^m` is finite, `C/C^m`
is Hausdorff compact and totally disconnected, `f⁻¹(C^m) ≤ A^n`, and `U`
contains every `n`th power in `A`. It constructs an open finite-index `N`
containing every `m`th power in `C` with `f⁻¹(N) = U`. The source power subgroup
lies in the kernel of `A → C/C^m`, so the kernel has finite index. The first
isomorphism theorem then makes the image finite. The power-intersection
containment supplies the kernel condition in the preceding lemma.
Neither exponent needs a positivity hypothesis in this generic deduction;
all the stated algebraic and topological hypotheses are retained.

In the intended prescription application, `P` is the subgroup of `(2*n)`th
powers in actual idele classes. The topology of that power quotient, finiteness
of the local product modulo powers, and the arithmetic containment of the
preimage of `P` in the prescribed kernel remain separate obligations. These
lemmas alone do not prove Grunwald–Wang or any unconditional Hecke-character
existence statement.
