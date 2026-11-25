# Uniform finite parabolic types on an affine étale neighbourhood

`relativeParabolicEtaleLocalFiniteTypes` proves the unchanged published
`RelativeParabolicEtaleLocalFiniteTypesStatement` in every universe. The proof
uses the actual iterated pullback objects from the target statement throughout.

The published theorem `etaleLocalSplitReductive` gives an affine étale
neighbourhood through the chosen base point, a fibrewise maximal coordinate
split torus, and one full coordinate root datum valid on every field fibre.
A residue field at the supplied neighbourhood point is a reference field
algebra. `uniformStandardCocharacterFamily` chooses a finite index type and
fixed integer exponent vectors from this reference fibre; its specification
identifies them with one standard cocharacter for each simple-root face on
all further field algebras.

`UniformStandardCocharacterFamily.parabolic` and `inclusion` construct actual
affine dynamic parabolic models over the neighbourhood. Their
`relativeParabolic` theorem proves the required relative parabolicity. A single
`Fintype.equivFin` reindexes this fixed family by `Fin n`, before any subsequent
field, field-valued point, or parabolic is supplied.

For an arbitrary point `x : Spec k → Spec R`, the private lemma uses the ring
map `Spec.preimage x` to give `k` its `R`-algebra structure and rewrites with
`Spec.map_preimage x`. The proved `classifies_field` theorem then supplies the
unique family index and the rational conjugating point. That theorem uses the
fixed-exponent dynamic base-change identity and standard parabolic
classification, with equality of subgroup functors on every scheme test.
Transport along the finite indexing equivalence gives existence and uniqueness
in the precise target formulation. Uniqueness concerns the family index only.

This is the finite-type step described in Conrad, *Reductive group schemes*
(2014), proof of Corollary 5.2.9, p.157, registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The implemented route derives the uniform exponent family by comparing the
actual root lattices on different field fibres and uses the published rational
standard classification. The proof constructs neither a relative moduli scheme
nor descent data for a universal parabolic.
