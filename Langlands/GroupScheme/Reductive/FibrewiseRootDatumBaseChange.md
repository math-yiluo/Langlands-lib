# Base change of fibrewise coordinate root data

`FibrewiseRootDatumBaseChangeStatement` asserts that an affine group scheme over
`Spec R`, equipped with a map from the finite coordinate split torus and a full
coordinate fibrewise root datum `P`, retains that same datum after scalar
extension along any `R`-algebra `A`. Both rings are arbitrary commutative rings
in universe `u`; the root index has an independent universe `v`. The statement
requires neither a local nor a reduced coefficient ring. The theorem
`fibrewiseRootDatumBaseChange` proves it, using
`IsFibrewiseRootDatumOf.baseChange_implicit`.

The transported torus map is the actual map
`splitTorus.baseChangeHom (K := A) G I i`, obtained by pulling back the given
map `i` and composing with the inverse of the canonical coordinate-torus
identification. The predicate `IsFibrewiseRootDatumOf` retains finiteness and
reducedness of the abstract root datum and requires its entire coordinate
realization to be an actual root datum on every supplied field-valued fibre.
Thus the conclusion retains the character and cocharacter lattices, the
pairing, the root image, and the normalizer witnesses realizing the
reflections. It uses every field's supplied `A`-algebra structure.

The module also proves preservation of fibrewise maximality for smooth affine
groups: `IsFibrewiseMaximalTorus.baseChange` handles arbitrary scheme maps,
`IsFibrewiseMaximalTorus.iso_comp` changes the source by an isomorphism, and
`splitTorus.isFibrewiseMaximalTorus_baseChangeHom` combines these results for the
canonical coordinate torus. Smoothness is needed by this maximality argument;
it is not an assumption of the coordinate-root-datum transport statement.

The implemented proof proceeds through the following comparisons.

1. `splitTorus.baseChangeIso_comp_finite` identifies the coordinate isomorphisms for
   successive pullbacks with that for their composite. It compares maps on
   every test scheme, using the families of global units that describe points
   of a coordinate split torus, the published pullback point equivalences,
   and their naturality. `baseChangeIso_inv_comp` takes inverses, and
   `baseChangeTorusHom_comp` then applies pullback naturality to the given
   ambient group map.
2. The maximality proof specializes to each residue-field point, uses
   `IsFibrewiseMaximalTorus.fieldPoint` for its composite with the base map,
   and applies `isMaximalTorus_baseChange_comp`. Source isomorphisms preserve
   maximality by the published `IsMaximalTorus.iso_comp`.
3. A private ambient transport lemma preserves an actual root datum under a
   group-scheme isomorphism. The torus and its lattices remain fixed. The proof
   transports the root image by `roots_image_of_transport` and sends each
   normalizing point through the ambient isomorphism, using
   `innerIso_hom_comp` to preserve its action on the torus.
4. For a field algebra over `A`, the proof equips that field with the composite
   `R`-algebra structure. The scalar-tower identity identifies the composite
   map of spectra with `algebraBaseMap R k`. A private map-indexed predicate
   includes the corresponding affine pullback instance, so equality transport
   also transports this dependent instance. The original field-fibre datum
   then gives the datum on the composite pullback. The torus comparison from
   step 1 and the ambient comparison isomorphism give the required datum on
   the successive pullback. Its abstract finite reduced datum is unchanged.

This is an internal derived transport result, rather than a new transcription
of a literature statement. Its provenance is the Library's actual coordinate
root-datum predicate, split-torus point models, pullback coherence, root-image
transport, and field-point maximality results. It does not use an isomorphism
or classification theorem for reductive groups. It supplies base-change data
needed by such arguments; it does not itself construct an isomorphism between
two reductive groups or lift an isomorphism across a nil ideal.

Shared declarations `IsFibrewiseMaximalTorus.baseChange`, `IsFibrewiseMaximalTorus.iso_comp` are imported from `Langlands.GroupScheme.Torus.FibrewiseMaximalTransport`; their mathematical hypotheses, conclusions and data are unchanged.
