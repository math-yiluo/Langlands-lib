# Proof: the affine diagram of an anisotropic group over a local field

`Langlands.GroupScheme.localAnisotropicAffineDiagram` proves the published
proposition `Langlands.GroupScheme.LocalAnisotropicAffineDiagramStatement.{u}`
at every universe `u`. The statement module
`Langlands.GroupScheme.SimplyConnected.LocalAnisotropicAffineDiagramStatement`
and its Markdown are imported unchanged. The theorem has no premise.

## The proved statement

Let `K : Type u` be a nonarchimedean local field of any characteristic, with
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`.
Let `G` be a group scheme over `Spec K` with `[IsAffineHom G.X.hom]` and
`[LocallyOfFiniteType G.X.hom]`, and let `d : TitsIndexData G` be an arbitrary
actual index datum. If `G` is absolutely almost simple and anisotropic, then
there is a matrix `A : Matrix (Option d.Vertex) (Option d.Vertex) ℤ` such that

1. `A (some a) (some b) = d.cartan a b` for all simple vertices `a b`;
2. `A i i = 2` for every index `i`;
3. `A i j ≤ 0` whenever `i ≠ j`;
4. `A i j = 0 ↔ A j i = 0` for all `i j`;
5. some `m` with `0 < m i` for every `i` satisfies `m ᵥ* A = 0`;
6. for all `i j` there is a permutation `σ` of `Option d.Vertex` with
   `A (σ k) (σ l) = A k l` for all `k l` and `σ i = j`.

Every field and residue characteristic is allowed, including 2. This is the
building part of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), proof of Theorem 10.3.1, printed pp. 391–392 / PDF pp. 422–423,
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`. The statement
Markdown explains how the source argument produces each condition.

## The implemented proof

The proof is the single application

```text
localAnisotropicAffineDiagram_of_remaining_building_inputs
  specialTorusExistence
  quasiSplitIndivisibleDerivativeLifts
  unramifiedSpecialApartmentChamber
```

All four terms are published Library theorems in the namespace
`Langlands.Geometry.Building`, at the same universe `u`.

- `localAnisotropicAffineDiagram_of_remaining_building_inputs` (module
  `Langlands.Geometry.Building.LocalAnisotropicAffineDiagramRemainingInputs`)
  has type
  `SpecialTorusExistenceStatement.{u} →
  QuasiSplitIndivisibleDerivativeLiftsStatement.{u} →
  UnramifiedSpecialApartmentChamberStatement.{u} →
  LocalAnisotropicAffineDiagramStatement.{u}`.
  It specializes the five-input reduction
  `localAnisotropicAffineDiagram_of_building_inputs` (module
  `LocalAnisotropicAffineDiagramReduction`) by the published proofs
  `quasiSplitDerivativeAffineRoots` and
  `Langlands.GroupScheme.relativeRootSystemIrreducible`.
- `specialTorusExistence : SpecialTorusExistenceStatement.{u}` (module
  `Langlands.Geometry.Building.SpecialTorusExistenceProof`) is KP
  Proposition 9.3.4: a maximal split torus lies in an `F`-torus whose base
  change to the maximal unramified extension is maximal split.
- `quasiSplitIndivisibleDerivativeLifts :
  QuasiSplitIndivisibleDerivativeLiftsStatement.{u}` (module
  `Langlands.Geometry.Building.QuasiSplitIndivisibleDerivativeLiftsProof`)
  gives, in every full-V6-compatible apartment of an actual quasi-split group
  over a henselian discretely valued field, an indivisible affine lift of each
  member of the full derivative set.
- `unramifiedSpecialApartmentChamber :
  UnramifiedSpecialApartmentChamberStatement.{u}` (module
  `Langlands.Geometry.Building.UnramifiedSpecialApartmentChamberProof`) gives,
  for a special torus as above and each fully compatible,
  coefficient-stable actual apartment of its scalar extension to the maximal
  unramified extension, a point regular for the ordinary affine roots whose
  sign facet is preserved by every actual affine coefficient automorphism
  (the `Γ`-stable chamber of KP Proposition 9.3.6). It is published as
  `unramifiedSpecialApartmentChamber_of_connectedGeneration` applied to
  `Langlands.GroupScheme.connectedGeneration`.

The resulting theorem retains no hypothesis beyond those of the target.

## How the reduction uses the inputs

The five-input reduction, explained in
[LocalAnisotropicAffineDiagramReduction](../../Geometry/Building/LocalAnisotropicAffineDiagramReduction.md),
follows the source. Write `K'` for the maximal unramified extension. The
special torus contains a maximal split torus of `G`, and its scalar extension
to `K'` is maximal split; apartment and centralizer data exist on it. The
full-derivative theorem identifies the ordinary affine derivatives of this
apartment with all actual relative-root forms, and relative-root
irreducibility makes its ordinary affine roots nonempty and irreducible. The
chamber theorem gives a regular point whose sign facet is stable under the
coefficient automorphisms. The Cartan matrix of the simple affine roots of
this chamber, with its positive marks, satisfies conditions 2–5. Anisotropy
makes the Galois action transitive on these simple affine roots, preserving
their Cartan matrix, which gives condition 6. With the indivisible lifts, the
transitivity
yields a reduced simply-laced relative root system, so the chosen split torus
is maximal over `K'` and the group splits there. Only then is the relative
Cartan block compared with the absolute Cartan matrix `d.cartan`
(condition 1).

No local type-A classification, local rank-one classification or local
Kneser–Tits result is used.
