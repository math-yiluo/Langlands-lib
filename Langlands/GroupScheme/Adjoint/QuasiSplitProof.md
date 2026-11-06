# Quasi-splitness of a supplied adjoint quotient

`adjointQuotientQuasiSplitStatement.{u}` proves the unchanged
`AdjointQuotientQuasiSplitStatement.{u}`: for every field `k : Type u`, an
actual full-centre adjoint quotient `q : G → A` carries quasi-splitness of
`G` to quasi-splitness of `A`. The proof constructs an actual ground-field
geometric Borel in `A`. It imposes no perfectness or characteristic
restriction on `k` and no smoothness or connectedness condition on the
centre. The existing `IsAdjointQuotient` predicate supplies connected
reductivity of the target through its adjointness assertion.

The implementation follows the Borel-image route supporting the source
comparison in `Adjoint/QuasiSplitStatement.md`. Its intermediate lemmas are
internal deductions from the existing central-kernel, reduced identity
component, smooth connected image, rational-point and descent APIs; they
are not additional assumptions on the theorem.

Over an algebraically closed field,
`AdjointQuotientBorelImage.isSolvable_of_central_kernel` treats a subgroup
`C → G` mapping to a solvable group `J`, compatibly with `q` and a map
`J → A`. A rational point in the kernel of `C(k) → J(k)` maps into the
full centre of `G`, by `IsAdjointQuotient.mem_center_iff_comp_eq_one`.
The injective subgroup inclusion shows that this kernel is commutative.
The group extension solvability theorem, followed by the existing
algebraically closed rational-point comparison, proves that `C` is
solvable in the unchanged group-scheme sense.

`AdjointQuotientBorelImage.surjective_identityCore_comp` proves a useful
geometric step. For a flat homomorphism `r : N → J` locally of finite
presentation, with affine finite-type groups and connected `J`, the
reduced identity component of `N` maps onto `J`. The reduced identity
component has open underlying range in `N`; flatness and local finite
presentation make `r` open. Its composite range is also closed: the
existing smooth connected image theorem factors the composite through a
closed inclusion with surjective first map. The range contains the
identity. Connectedness of `J` therefore makes this open and closed range
all of `J`. This argument uses the topological range of the reduced
inclusion and does not require that inclusion to be smooth.

`AdjointQuotientBorelImage.isBorelSubgroup_image` now starts with a Borel
`i : B → G` and a supplied smooth connected closed image `j : I → A`,
with a surjective homomorphism `p : B → I` locally of finite type and
`i ≫ q = p ≫ j`. The rational-point lift through `p` proves solvability
of `I`. For any smooth connected solvable closed overgroup `J → A` of
`I`, form its preimage `P` in `G` and the reduced identity component `C`
of `P`. The map `B → P` factors through `C`, since `B` is smooth and
connected over the algebraically closed, hence perfect, field. The first
lemma makes `C` solvable. Borel maximality in `G` then makes `B → C` an
isomorphism. The preimage projection `P → J` is flat and locally of
finite presentation by base change, so the preceding lemma makes
`C → J` surjective. Thus `I → J` is surjective. It is a closed immersion
because both supplied inclusions into `A` are closed. A surjective closed
immersion into the smooth, hence reduced, `J` is an isomorphism. Reflecting
this through the forgetful functors proves Borel maximality of `j`.

For the final theorem over arbitrary `k`, choose a ground-field geometric
Borel `B → G`. The existing smooth connected image theorem constructs a
closed smooth connected affine image `I → A` of `B → G → A`, with a flat,
surjective factor locally of finite presentation. Base change this
factorization to the algebraic closure. The published adjoint-quotient
base-change theorem preserves the full quotient interface, and the
source inclusion is Borel there by its given geometric Borel property.
The algebraically closed Borel-image lemma applies. The existing
`isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure` descends the
Borel property and packages its algebraic-closure witness. This supplies
the required geometric Borel in `A`.

This is the supplied-adjoint-quotient prerequisite only. It does not
construct an adjoint quotient or a quasi-split inner form and does not
prove the host finite-extension norm-criterion theorem. Worker 1459
implemented the proof; Worker 1472 identified and formulated the
prerequisite used by the inner-form construction.
