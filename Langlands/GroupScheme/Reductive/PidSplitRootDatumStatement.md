# Statement: full split root data and free root spaces over a principal ideal domain

`Langlands.GroupScheme.PidSplitRootDatumStatement.{u}` is a statement-only,
`Prop`-valued definition. It supplies no proof or additional axiom.

For any commutative principal ideal domain `R : Type u`, any reductive group
scheme `G` over `Spec R`, and any finite coordinate torus with a homomorphism
`i : splitTorus (Spec R) I ⟶ G` maximal on every residue-field fibre, the
statement asserts the existence of a single root datum
`P : RootDatum J (I → ℤ) (I → ℤ)` such that:

- `IsFibrewiseRootDatumOf I G i P`: `J` is finite, `P` is reduced, and its
  realization on the actual entire character and cocharacter lattices is
  the root datum of `i` on every supplied field algebra over `R`;
- every actual exponent weight space for a root of `P` is isomorphic to
  `R` as an `R`-module.

`IsFibrewiseMaximalTorus` includes closedness and the torus property on the
residue-field fibres. The statement does not assume a separate global
closed-immersion hypothesis; the root-datum and Lie-module conclusions use
these fibrewise conditions. The affine structure used to define the Lie
weight spaces is supplied by `hG : IsReductive G`. No semisimplicity or
restriction on central torus directions is imposed. The root-index type
may be empty. All objects lie in the arbitrary universe `u`.

This is a derived statement from Brian Conrad, *Reductive group schemes*
(2014), Definition 5.1.1 and its following remark, p.136 (printed and
one-based PDF page), with the rank-one root-space assertion explained just
before the definition; see also Proposition 5.1.6, p.138. The source is
registered as `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The remark says that roots and coroots are constant when the base is
connected. `Spec R` is irreducible for a domain, so one full coordinate
datum serves every fibre. The actual root spaces are finite locally free
modules of rank one. Over a principal ideal domain these modules are
free, giving the displayed linear isomorphisms. The same argument for
`R = ℤ` is stated in the paragraph before Proposition 6.4.1, p.230.

The proposition generalizes the root-data and root-space part of the
first clause of `ChevalleyGroupClassificationStatement` from the lifted
integers to every principal ideal domain. It assumes the split torus has
already been supplied and does not prove that arbitrary tori split, or
assert an isomorphism theorem for reductive groups.
