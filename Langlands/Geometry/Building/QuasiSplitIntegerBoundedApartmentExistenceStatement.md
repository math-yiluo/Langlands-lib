# Bounded quasi-split apartment existence

Worker 312. This is a derived prerequisite for algebraic boundedness of the
depth-zero root filtrations over the actual maximal unramified field. It
strengthens the existing quasi-split apartment existence interface by asking
that the constructed apartment have bounded depth-zero root filtrations.
This file states the prerequisite and does not prove it.

`Langlands.Geometry.Building.QuasiSplitIntegerBoundedApartmentExistenceStatement`
quantifies over an arbitrary universe `u`, a field `k : Type u` with a valuative
relation, a surjective integer-valued valuation `v` compatible with that
relation, and henselianity of the valuation ring. For each affine quasi-split
group scheme `G/k` and each prescribed maximal split torus `i : S → G`, it asks
for an actual apartment class `D` and an actual centralizer representative `C`.
The class satisfies the existing full integer-valued V 6 condition for `C`.
At every point `x` and every relative root `a`, the subgroup
`D.filtration x a 0` is algebraically bounded in the actual affine group `G`.
Algebraic boundedness uses every global regular function and the supplied
valuative relation.

The existing `KPApartmentData` supplies V 0–V 5 and split-torus compatibility;
full V 6 and the boundedness clause are conclusions of this existence target.
No apartment, centralizer, root coordinates, boundedness witness, completeness,
topology, residue-field cardinality or residue-characteristic condition is
supplied as a premise. The centralizer representative may differ from a
consumer's representative. The companion centralizer-transfer and uniqueness
reduction handles that difference.

## Provenance

This interface is derived from the existing
`QuasiSplitIntegerApartmentExistenceStatement` and the boundedness half of
V 7 in Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Definition 6.1.2 (printed p.199 / PDF230), restricted to depth zero.
Its construction is intended to expose a bound in the quasi-split apartment
construction, rather than assume boundedness for the supplied class.
The new existence assertion remains a proof obligation. The conditional
reduction in `UnramifiedZeroRootFiltrationBoundedReduction.lean` establishes its
precise use for Task 6433; it does not discharge this obligation or the separate
henselian quasi-splitness theorem.

The registered book source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' 2024 corrections, source `kaletha-prasad-2024-corrections`,
SHA256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF32, replace the reductive construction's derived-group route by the
adjoint-group route. This existence target keeps the full connected reductive
scope of the existing quasi-split interface and does not prescribe a proof
route. It requests neither AS 5 nor any building-axiom package.
