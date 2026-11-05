# Compact openness of the actual centralizer-zero subgroup

`ParahoricBuildingData.CentralizerZeroCompactOpenStatement P` states that the
actual subgroup `P.centralizerZero` is compact and open in the canonical
rational-point topology of the supplied centralizer `Z = Z_G(S)`. It is a
proposition definition and has no proof in this module.

The field `F : Type u` is an arbitrary nonarchimedean local field, with exactly
the existing `Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances. Both equal and mixed characteristic
and split rank zero are included. The input is an actual
`P : ParahoricBuildingData G`, with the existing affine structure morphism
of `G`. The statement imposes no additional apartment axioms.

## Actual subgroup and topology

The input already supplies a connected reductive group `G`, a maximal split
torus `i : S → G`, and a closed subgroup `j : Z → G` representing its actual
torus centralizer. It also supplies the data of `KPZeroSubgroups` and
`KPParahoric`: `K = UnramifiedClosure F` is the maximal unramified extension
inside the fixed separable closure, and

`P.centralizerZero = Z(K)^0.comap (rationalExtend F K Z)`.

Here `Z(K)^0` is the existing join of the actual simply connected derived
image and the image of the norm-defined torus Iwahori subgroup. The torus,
finite Galois splitting extension and derived cover are the choices supplied
by `P.zeroDatum.centralizerDatum`. The target concerns every such supplied
datum and retains this precise subgroup, including its joins and comap.

The statement derives `IsAffine G.X.left` from the existing affine structure
morphism. It then derives `IsAffine Z.X.left` from the supplied closed
immersion `j`. It explicitly installs `rationalPointTopology F Z.X`.
Both conclusions refer to `P.centralizerZero` as a subset of the full
`rationalPoints Z`, so openness is in `Z(F)` itself. No arbitrary topology
is a parameter. The conclusion does not assert openness of `j(Z(F)^0)` in
the ambient group `G(F)`.

## Source and derived provenance

This is a local-field consequence of the following passages of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Printed page numbers are PDF page numbers minus 31.

- Fact 2.2.3 and Remark 2.2.2, printed p.70 / PDF p.101, identify closed
  bounded subsets of an affine finite-type scheme over a locally compact
  field with compact subsets in the analytic point topology.
- Proposition 2.2.12, printed pp.73–74 / PDF pp.104–105, identifies the
  rational-character valuation kernel with the unique maximal bounded
  subgroup when the derived group is anisotropic.
- The proof of Fact 2.6.22, Definition 2.6.23 and Lemma 2.6.24, printed
  pp.104–105 / PDF pp.135–136, identify centralizers of maximal split tori
  as minimal Levi subgroups, define the zero subgroup, and establish its
  openness. Remark 2.6.25(3), on PDF p.136, explains the overlap of the
  minimal-Levi and anisotropic-modulo-center definitions.
- Lemma 2.6.29, printed p.106 / PDF p.137, places the zero subgroup inside
  the rational-character valuation kernel with finite index. Only its
  containment component is needed for the compactness route here.

For the minimal Levi `Z_G(S)`, its adjoint quotient, and hence its derived
group, is anisotropic. Thus Proposition 2.2.12 makes `Z(F)^1` bounded. The
zero subgroup lies in this rational-character valuation kernel; its openness
from Lemma 2.6.24 also makes it closed as a subgroup of a topological group.
Fact 2.2.3 then gives compactness. This explains the derived source
provenance of the combined target. These algebraic and topological steps
are proof obligations, not hypotheses or theorems implemented here.

The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
were read at PDF pp.24–25. They impose the Henselian hypothesis in §2.2,
correct the character-valuation signs, and impose the Henselian and perfect
residue-field hypotheses before Definition 2.6.20. A nonarchimedean local
field satisfies these field conditions. The sign changes preserve the
valuation kernels. The corrected torus example shows that `T(F)^0` can be
a proper finite-index subgroup of `T(F)^1`; the target asserts no equality
of these subgroups.

## Consumer obligations

This target supplies the central factor needed for the actual chamber
Iwahori compact-openness proof. It asserts neither a finite root-product
decomposition nor openness of a full parahoric in `G(F)`. The main published
`ChamberIwahoriCompactOpenStatement` and its hypotheses remain unchanged.
No choice independence, model existence or existence of `P` is claimed.
