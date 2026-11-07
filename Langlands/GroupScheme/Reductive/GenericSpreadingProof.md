# Generic reductivity on a nonempty principal open

`Langlands.GroupScheme.genericReductivitySpreading.{u}` proves the exact
Library proposition `GenericReductivitySpreadingStatement.{u}`. For every
supplied Noetherian domain `R : Type u`, fraction field `K : Type u` with
its `Algebra R K` and `IsFractionRing R K`, and actual smooth affine group
scheme `G` over `Spec R`, connected reductivity of the actual fraction-field
pullback yields a single nonzero `r : R`. Every supplied field `k : Type u`
and every `Algebra R k` on which `r` stays nonzero then give a connected
reductive actual pullback of the same `G`. The universe is arbitrary.

The implemented proof applies
`genericReductivitySpreading_of_identityComponentLocusOpen` to the proved
`identityComponentReductiveLocusOpen`. The second theorem discharges the
first theorem's openness premise. Thus the resulting theorem has exactly
the target type, with no additional openness or structural premise.

The imported assembly starts with the actual `R`, `K`, `G` and coefficient
maps in the target. It identifies the supplied fraction-field point with
the generic point and uses the canonical residue-field map into `K` and
the pullback-composition isomorphism to descend connected reductivity to
the generic residue fibre. Extension to that residue field's algebraic
closure gives connected reductivity of the actual geometric generic
fibre. Its identity component is therefore reductive. The proved openness
of this identity-component locus supplies a principal open `D(r₂)` through
the generic point inside the locus, with `r₂ ≠ 0`.

Separately, `exists_principalOpen_connected_fibers` supplies a nonzero
`r₁` such that all supplied field-valued fibres over `D(r₁)` are connected.
Its proof uses smooth connected affine generic-fibre geometry and spreading
of geometric irreducibility, as explained in `GenericFiberGeometry.md`.
The assembly chooses `r = r₁ * r₂` before quantifying over `k` and its
algebra structure. Both factors are nonzero in the domain, so `r ≠ 0`.

For an arbitrary supplied field point with `algebraMap R k r ≠ 0`, the
actual image of its closed point belongs to both principal opens. To use
the identity-component locus for the whole geometric fibre, the assembly
first obtains connectedness of that fibre. It represents the specified
geometric point by `geometricPointScalarMap`, equips its actual algebraic
closure with the resulting `R`-algebra structure, and applies the
connectedness conclusion for `r₁`. The equality of spectrum maps and the
residue-field point formula retain the exact base point. Thus membership
in the identity-component locus implies connected reductivity of the
whole actual geometric fibre.

Finally, `baseChangeCompIso` identifies this geometric fibre with the
actual residue-field fibre followed by algebraic closure. Reflection of
connected reductivity under that field extension gives the residue-fibre
assertion. `fieldReductive_iff_residueReductive` then returns to the exact
supplied pullback along `Spec.algebraMap R k`, using its canonical
residue-field factorization and field-extension preservation. This step
covers arbitrary extensions of residue fields as well as residue fields
themselves.

All reductivity assertions use the unchanged `IsConnectedReductive`,
including connectedness and triviality of the geometric unipotent radical.
The imported openness theorem constructs its torus and neighbourhood data;
none becomes a premise here. This file is an internal composition of the
published openness proof and the published generic-spreading assembly.
The companions `IdentityComponentLocusProof.md`,
`GenericSpreadingFromLocus.md` and `GenericFiberGeometry.md` describe those
proofs and their provenance. The target, its companion and its imports
remain unchanged.
