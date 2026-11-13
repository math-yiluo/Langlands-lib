# Descent to the norm-one group of a symplectic involution

Supply a quasi-split inner-form presentation `d` of `G` over an arbitrary
field `K`, an isomorphism `i` from its model to the symplectic matrix group
on a finite index type `n`, and assume `n` is nonempty. The construction
`normOneIso d i` is an isomorphism of group schemes from `G` to the
reduced-norm-one isometry group of `descendedInvolution d i` on the fixed
algebra of `twistedAction d i`.

The scalar-extension descent chart intertwines that involution with the
adjoint involution of the standard alternating matrix `J`. For every
relative test scheme `V` and every point `s : V → Spec L`, where
`L = d.carrier`, `normOneChartPoints` identifies the norm-one isometries
with symplectic matrices over the global sections of `V`. Composing its
inverse with the model's matrix coordinates defines `chartLocalIso`.
The naturality of both point comparisons proves its naturality on all
relative test schemes.

The identity `extendMatrix_chartAlong_galois` shows that these local
isomorphisms have the same adjoint discrepancy as `d` on each Galois
pair. The published finite Galois overlap theorem promotes these
identities to the full overlap discrepancy. Composing with the inverse
of `d.localIso` therefore gives `compareLocalIso`, independent of the
chosen point of `Spec L`. The finite field extension is fpqc, so the
published descent theorem for local group isomorphisms produces
`normOneIso`.

The final theorem `symplecticInnerFormInvolution` proves the published
proposition `SymplecticInnerFormInvolutionStatement` at every universe
parameter. Its assumption `2 ≤ n` supplies nonemptiness of `Fin n`.
The comparison between the standard and matrix symplectic models
supplies `i`; the twisted fixed algebra supplies the central simple
algebra, its reduced degree `2 * n`, the involution and its finite
Galois standard splitting chart. The isomorphism just constructed
provides the remaining group-scheme conclusion.

This is a derived adaptation of the published special-linear
inner-form descent proof, using the symplectic involution and chart
comparisons in the supporting modules. It uses actual group schemes
and every relative test scheme, in every field characteristic.
The division-algebra and antihermitian classification is a separate
input to the final classification theorem.
