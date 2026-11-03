# Points of dynamic extension inside its represented Levi

Author: Worker 1212.

This internal comparison identifies the actual subgroup points used when
induction in a represented dynamic centralizer is compared with induction
inside the ambient group. It does not prove finite length or transitivity.

## Exact extension and its points

Let `G` be a separated group scheme over any base scheme `S`, let `χ` be a
cocharacter, and let `j : L → G` represent `Dynamic.centralizer χ`. For any
subgroup functor `F` of `L`, the theorem
`Dynamic.centralizer_inf_extendFromCentralizer` proves

`Z(χ) ∩ extendFromCentralizer χ j hj F = F.map j`.

This is an equality of subgroup functors on every original test scheme.
The proof maps the published equality
`comap_extendFromCentralizer χ j hj F = F` back along `j` and uses the
published image-of-inverse-image identity. It uses separatedness for the
inverse-image equality. Closedness of `j` and reductivity are not needed
here.

`Dynamic.extendFromCentralizerPointsEquiv` restricts the published
`hj.pointsEquiv T` to an isomorphism from `F(T)` onto the literal subgroup
`extend(F)(T).subgroupOf Z(χ)(T)`. Its forward map is postcomposition by
`j`. Injectivity follows from the represented-point equivalence, and
surjectivity follows from the intersection equality just proved. The
evaluation theorem states this forward map explicitly.

## Realized inner parabolic, Levi and radical

Suppose `j` is also a closed subgroup and `ν` is a cocharacter of `L`.
If an ambient cocharacter `ψ` has the simultaneous realization identities

- `P(ψ) = extend(P(ν))`;
- `Z(ψ) = Z(ν).map j`;
- `U(ψ) = extend(U(ν))`,

then `realized_parabolic_subgroupOf`,
`realized_centralizer_subgroupOf` and
`realized_unipotent_subgroupOf` identify the subgroups of `Z(χ)(T)`
obtained by intersecting `P(ψ)`, `Z(ψ)` and `U(ψ)` with `Z(χ)`.
They are respectively the intersections of `P(ν ≫ j)`, `Z(ν ≫ j)` and
`U(ν ≫ j)` with that same outer centralizer. Each equality is between the
literal `Subgroup.subgroupOf` expressions, for every test scheme `T`.

For the parabolic and radical, the proof combines the exact-extension
intersection with the published closed-subgroup dynamic intersection
identity. For the centralizer, its image lies in the represented outer
centralizer, and the corresponding closed-subgroup identity applies.
No common maximal split torus is assumed or constructed.

`Dynamic.exists_realization_with_inside_subgroups` discharges the three
realization assumptions using the published
`dynamicLeviCocharacterRealization` theorem. Its only structural inputs
are a connected reductive group over an arbitrary field, a cocharacter,
a closed representative of its centralizer, and a cocharacter of that
representative. It retains all three realization identities as well as
the three inside-subgroup equalities for every test scheme.

## Provenance and boundary

These are derived comparisons for the Library's exact dynamic-extension
construction, rather than new statements transcribed from literature.
They compose `LeviParabolicExtension`,
`LeviCocharacterRealizationProof`, `Dynamic.ClosedSubgroup`, and
`RepresentedSubgroup`.

The all-test equalities specialize to the identity-test subgroups used by
the actual rational-point functors. No topology is introduced or changed
by this module. A normalized-functor comparison must still use the
actual point homeomorphism and compare the full-parabolic Haar
normalization. No connected reductivity of the representative, standard
parabolic classification, cuspidal embedding, supercuspidal finite-length
theorem, or proof of the host VI.6.2 target is supplied here.
