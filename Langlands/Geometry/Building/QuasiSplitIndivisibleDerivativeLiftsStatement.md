# Indivisible lifts in actual quasi-split apartments

`Langlands.Geometry.Building.QuasiSplitIndivisibleDerivativeLiftsStatement`
is an unproved proposition. For every universe `u`, it quantifies over a
field `k : Type u`, a surjective valuation
`v : Valuation k (WithZero (Multiplicative ℤ))`, and henselianity of its
valuation ring. For each actual quasi-split group `G/k` with affine
structure and each prescribed actual maximal split torus `i : S → G`,
it quantifies over every apartment datum
`D : KPApartmentData i (IntegerValuation.order v)` and every actual
centralizer datum `C : CentralizerDatum i`. Full centralizer compatibility
`IntegerValuation.IsOmegaCompatible v D C` is the final premise.

The conclusion is `AffineRootSystem.HasIndivisibleDerivativeLifts
D.affineRoots`. Explicitly, every member `a` of the full derivative-root
subtype of the actual affine roots has an affine lift `ψ` with
`ψ.linear = a.val`, `ψ ∈ D.affineRoots`, and
`(1 / 2 : ℝ) • ψ ∉ D.affineRoots`. In particular, multipliable derivative
roots remain in the quantification. This asks for an indivisible affine
lift of each derivative; it does not assert that all affine roots are
indivisible.

The apartment datum is an actual normalizer-stable equipollence class of
root-datum valuations on the rational root groups of `(G,S)`.
`IsOmegaCompatible` imposes the full V6 identity on the actual
centralizer, using the negative character valuation as the apartment
translation. The monomorphism instance for `i` is deduced from its maximal
split torus hypothesis. `IsQuasiSplit G` includes connected reductivity
and an actual field-defined geometric Borel.

No topology, completeness, perfect residue field, residue cardinality or
characteristic restriction is assumed. There is no premise of
reducedness, symmetric root-coroot pairing, simple-root transitivity, or
an affine-root-system axiom package. In particular this formulation
applies to the henselian maximal unramified field used in the
anisotropic affine-diagram argument. It proves neither this lift
assertion nor the host `LocalAnisotropicAffineDiagramStatement`.

## Derived source correspondence

This is a derived target from Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Chapter 6. Its opening paragraphs (printed pp.195–196,
PDF pp.226–227) assume a henselian discretely valued field with value
group `ℤ` and explicitly permit imperfect residue fields. Surjectivity
of `v` expresses that normalization in the Library's multiplicative
notation. Definition 6.3.4 (printed p.218, PDF p.249) defines the actual
affine roots used here.

Proposition 6.4.8 and its proof (printed pp.225–226, PDF pp.256–257),
with Remark 6.4.9 and Table 6.4.1 (printed pp.226–227, PDF pp.257–258),
describe the quasi-split affine roots constructed from the Chevalley
valuation class. In the reduced affine-root-system cases, every affine
root is indivisible, so every derivative has an indivisible lift. In the
exceptional nonreduced case the proof gives, at its chosen origin,
`Ψ = {a + n | a ∈ Φ, n ∈ ℤ}`. For a derivative `a` whose half is also a
root, choosing an odd integer constant gives an indivisible lift:
its half has a nonintegral constant and is therefore absent from this
displayed set. The other derivatives have indivisible lifts directly.
The source's adjoint, simple-factor and restriction-of-scalars
reductions must be implemented with transport of this property. Thus
the conclusion retains the nonreduced exceptional case rather than
deleting its doubled derivatives.

The target concerns every compatible `D`, not just the canonical
construction in §6.4. Proposition 6.2.6 (printed p.216, PDF p.247)
identifies the compatible equipollence class. The Library already proves
its integer-valued uniqueness implication in
`IntegerValuation.IsOmegaCompatible.eq_of_isMaximalSplitTorus`
(`IntegerOmegaApartmentUniqueness`): two full-V6 classes for the same
actual maximal split torus and centralizer datum are equal.
To use it here, a proof must construct the source class, establish its
full compatibility, compare any chosen centralizer representations, and
transport the lift assertion to the arbitrary `D`. These are retained
proof obligations; they are not additional premises in the statement.
Changing the origin preserves linear parts and commutes with halving of
affine functions, so the lift property is independent of that choice.

The authors' *Corrections and additions* (2024), PDF p.32, replace the
derived-group reduction in §6.1(c) and Definition 6.1.27 by the adjoint
reduction, and correct the type notation in Remark 6.4.7. There is no
correction there to Proposition 6.4.8 or Table 6.4.1. The corrected
adjoint route is required for the reductive scope of this target.

The registered sources are
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
and `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
The desired implication is a derived consequence of these constructions
and comparisons, not a verbatim statement of Proposition 6.4.8.
