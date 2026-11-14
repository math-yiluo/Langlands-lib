# Transport of actual special-fibre quotients

This is an internal transport construction from the published `SpecialFibreQuotientData` interface and group-scheme isomorphism transport. It adds no literature assertion or quotient existence theorem.

Work over a local domain `R` and its fraction field `K`, in arbitrary universe `u`. Let `D` and `D'` be supplied relative-component models over `R`; their generic ambient groups may differ. An actual isomorphism `e : D.neutral.specialFibre ≅ D'.neutral.specialFibre` is required.

`SpecialFibreQuotientData.transportSpecialFibreIso Q e` transports the neutral special fibre, separately from the published generic-identification transport in `Transport.Model`. It retains exactly the radical scheme and affine quotient scheme of `Q`. Its radical inclusion is `Q.radicalInclusion ≫ e.hom`; its projection is `e.inv ≫ Q.projection`. The four `transportSpecialFibreIso_*` field lemmas record these formulas. No identification by rational-point images is substituted for the supplied scheme isomorphism.

`isReductiveQuotient_transportSpecialFibreIso` preserves the full validity predicate. The proof uses `IsUnipotentRadical.comp_iso` to transport closedness, smoothness, connectedness, unipotence, all-test normality and greatestness. `SubgroupFunctor.range_comp_iso` identifies the transported radical range with the inverse-image subgroup under `e.inv`; `RelativeRoot.IsFppfQuotient.comapIso` transports the fppf cover and exact all-test kernel. Connected reductivity is unchanged because the quotient group scheme is retained.

`transportSpecialFibreIso_hom_projection` states the exact recovery equation `e.hom ≫ (Q.transportSpecialFibreIso e).projection = Q.projection`, with a reassociated version. `transportSpecialFibreIso_torus_projection` applies it to supplied residue torus inclusions `t`, `t'` satisfying `t ≫ e.hom = t'`. The resulting equality of the actual maps to the retained quotient also identifies their adjoint-root sets without any change of torus character lattice.

In the unramified chamber construction this operation can be applied after coefficient base change, using the actual neutral-model recovery isomorphism on special fibres. Constructing that isomorphism, coefficient-base-change validity, maximality of the torus inclusions, root survival and the chamber itself remain separate obligations.
