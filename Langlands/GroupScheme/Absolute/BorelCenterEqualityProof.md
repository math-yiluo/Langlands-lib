# Proof: the centre of a connected group variety is the centre of a Borel subgroup

Worker 384.

This module proves `Langlands.GroupScheme.BorelCenterEqualityStatement.{u}`
([`BorelCenterEqualityStatement`](BorelCenterEqualityStatement.md); Milne, *Algebraic
Groups* (2017), Proposition 17.45, p.365) as `Langlands.GroupScheme.borelCenterEquality`, in
every universe and with no hypotheses beyond the statement's. For a field `k`, a smooth,
affine, connected group scheme `G` over `Spec k` and a geometric Borel subgroup `i : B ⟶ G`,
a point of `G` over a test scheme `T` is central in `G` exactly when it is the image under `i`
of a point of `B` over `T` that is central in `B`.

The proof follows Milne's route: reduce to an algebraic closure `k̄`, and there use
Proposition 17.22 (`Z(B) ⊆ C_G(B) = Z(G)`) and the containment `Z(G) ⊆ C_G(T) ⊆ B` for a
maximal torus `T ⊆ B`. In the Library the second containment is supplied by Milne's
Corollary 17.29 applied to a Cartan subgroup representing `C_G(T)`.

## Inputs

- `BorelCentralizerCenterStatement.{u}` (Milne 17.22,
  [`BorelCentralizerCenterStatement`](BorelCentralizerCenterStatement.md)): over an
  algebraically closed field, central points of a Borel subgroup `B` centralize `B` inside `G`,
  and the centralizer of `B` in `G` is `center G`. It is obtained as
  `borelCentralizerCenter_of_homomorphismRigidity borelHomomorphismRigidity`, combining the
  reduction 17.21 ⇒ 17.22
  ([`BorelCentralizerCenterReduction`](BorelCentralizerCenterReduction.md)) with the proof of
  Milne 17.21 ([`BorelHomomorphismRigidityProof`](BorelHomomorphismRigidityProof.md)).
- `torusCentralizerBorelContainment : TorusCentralizerBorelContainmentStatement.{u}` (Milne
  17.29, [`TorusCentralizerBorelContainmentProof`](TorusCentralizerBorelContainmentProof.md)):
  over an algebraically closed field, a connected closed subgroup inside the centralizer of a
  maximal torus `T` lies in every Borel subgroup containing `T`.
- `borelMaximalTorus` ([`BorelMaximalTorusProof`](BorelMaximalTorusProof.md)): over an
  algebraically closed field every Borel subgroup contains a maximal torus (a Borel pair).
- `exists_isCartanSubgroup_of_isMaximalTorus` ([`Cartan.Basic`](../Cartan/Basic.md)): for an
  affine group over a field, the all-test centralizer `torusCentralizer j` of a maximal torus
  `j` is represented by a Cartan subgroup `c : H ⟶ G`, which is a closed subgroup.
- `cartanStructure` ([`Cartan.StructureProof`](../Cartan/StructureProof.md), Milne 17.44):
  Cartan subgroups are smooth, connected and nilpotent; only connectedness is used.
- `center_le_torusCentralizer` ([`Rational.LeviFactorization`](../Rational/LeviFactorization.md)):
  the centre lies in every torus centralizer.
- Descent along `Spec k̄ → Spec k`: `fieldExtension_fpqc`
  ([`BaseChangeReflection`](../BaseChangeReflection.md)) makes it faithfully flat and
  quasi-compact; `SubgroupFunctor.le_range_of_baseChange_le`
  ([`SubgroupFunctor.FpqcDescent`](../SubgroupFunctor/FpqcDescent.md)) descends containment in
  the image of a monomorphism; `center_le_comap_of_baseChange_le`
  ([`Reductive.NormalCenterDescent`](../Reductive/NormalCenterDescent.md)) descends
  `center H ≤ (center G).comap i` when `G` has a scheme-theoretic centre, which
  `schemeTheoreticCenterExistence_of_isAffineHom`
  ([`Reductive.FiniteCenterReflection`](../Reductive/FiniteCenterReflection.md)) supplies for
  affine `G`; `center_baseChange` ([`Reductive.CenterBaseChangeProof`](../Reductive/CenterBaseChangeProof.md))
  and `SubgroupFunctor.range_baseChangeHom` ([`SubgroupBaseChange`](../SubgroupBaseChange.md))
  identify the base-changed centre and image.
- `GroupScheme.connectedSpace_baseChange_of_smooth_affine`
  ([`GeometricConnectedness`](../GeometricConnectedness.md)): `G_{k̄}` is connected.
- `center_comap_le_of_mono` ([`Derived.CenterReduction`](../Derived/CenterReduction.md)): a
  point of a subgroup whose image is central in `G` is central in the subgroup.

## Declarations

All auxiliary declarations are in the namespace `Langlands.GroupScheme.BorelCenterEquality`.

- `range_le_range_of_comp_eq`: if `f ≫ i = j` then `SubgroupFunctor.range j ≤
  SubgroupFunctor.range i`. Proof: a point `y ≫ j` equals `(y ≫ f) ≫ i`.
- `center_le_range_of_isAlgClosed (hT : TorusCentralizerBorelContainmentStatement)`: over an
  algebraically closed `k`, for smooth affine connected `G` and a Borel subgroup `i`,
  `center G ≤ SubgroupFunctor.range i`. Proof: `borelMaximalTorus` gives a maximal torus
  `j` with `j = f ≫ i`; `exists_isCartanSubgroup_of_isMaximalTorus` gives a Cartan subgroup
  `c` representing `torusCentralizer j`, connected by `cartanStructure`; then
  `center G ≤ torusCentralizer j = range c ≤ range i`, the last step by `hT` applied to `c`
  (closed, connected, contained in `torusCentralizer j`) and to the Borel subgroup `i`
  containing `j` (by `range_le_range_of_comp_eq`).
- `center_le_comap_of_isAlgClosed (hC : BorelCentralizerCenterStatement)`: over an
  algebraically closed `k`, `center B ≤ (center G).comap i`. Proof: part (1) of `hC` puts
  `x ≫ i` in the centralizer of `range i` for central `x`, and part (2) identifies that
  centralizer with `center G`.
- `center_le_range_and_comap hT hC`: over an arbitrary field `k` and a geometric Borel
  subgroup `i`, both `center G ≤ SubgroupFunctor.range i` and
  `center B ≤ (center G).comap i`. Proof: let `b : Spec k̄ → Spec k` be the base change to
  the algebraic closure (`toAlgebraicClosure k`), faithfully flat and quasi-compact by
  `fieldExtension_fpqc`. The base change `G_{k̄}` is smooth and affine (stable under base
  change) and connected (`connectedSpace_baseChange_of_smooth_affine`), and the base change
  of `i` is a Borel subgroup of `G_{k̄}` (the second component of
  `IsGeometricBorelSubgroup`); `i` is a closed immersion, hence a monomorphism.
  - First containment: by `le_range_of_baseChange_le` it suffices that
    `(center G).baseChange b ≤ (range i).baseChange b`; rewriting with `center_baseChange` and
    `range_baseChangeHom`, this is `center G_{k̄} ≤ range i_{k̄}`, given by
    `center_le_range_of_isAlgClosed`.
  - Second containment: `schemeTheoreticCenterExistence_of_isAffineHom` gives a
    scheme-theoretic centre of `G`, and `center_le_comap_of_baseChange_le` reduces to the same
    containment over `k̄`, given by `center_le_comap_of_isAlgClosed`.

In the namespace `Langlands.GroupScheme`:

- `borelCenterEquality_of_borelCentralizerCenter_of_torusCentralizerBorelContainment
  (hC : BorelCentralizerCenterStatement.{u}) (hT : TorusCentralizerBorelContainmentStatement.{u}) :
  BorelCenterEqualityStatement.{u}`. Proof: given `x : T ⟶ G.X`,
  - if `x` is central, the first containment writes `x = y ≫ i.hom.hom`, and `y` is central in
    `B` by `center_comap_le_of_mono` (as `i` is a monomorphism);
  - if `x = y ≫ i.hom.hom` with `y` central in `B`, the second containment makes `x` central.
- `borelCenterEquality : BorelCenterEqualityStatement.{u}`: the previous theorem applied to
  `borelCentralizerCenter_of_homomorphismRigidity borelHomomorphismRigidity` and
  `torusCentralizerBorelContainment`.

## Relation to the source

Milne first reduces to `k` algebraically closed and then proves `Z(G) = Z(B)` from
`Z(G) = C_G(B)` (17.22), `Z(B) = C_G(B) ∩ B` and `Z(G) ⊆ C_G(T) ⊆ B` (17.39(b)). Here the containment
`C_G(T) ⊆ B` is obtained from 17.29 (`C_G(T)°` lies in every Borel subgroup containing `T`)
applied to a Cartan subgroup representing `C_G(T)`, which is connected (17.44), so no identity
component is needed. The reduction to `k̄` is made explicit by fpqc descent of the two
containments of subgroup functors. The statement's all-test centres (on all schemes over
`Spec k`, with commutation after every base change) are used throughout; no comparison with
centres on `k`-algebras is needed.
