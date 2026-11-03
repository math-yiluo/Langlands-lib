import Langlands.Geometry.Building.KPParahoric

/-!
# The Iwahori–Weyl group `W̃^0 = N(F)/Z(F)^0`

Let `F` be a nonarchimedean local field, `G` a connected reductive `F`-group and
`P : ParahoricBuildingData G` building data for a maximal split torus `S` with normalizer
`N = N_G(S)` and centralizer `Z = Z_G(S)`. This module defines

* `Z(F)^0` as a subgroup of `N(F)` (`normalizerZero`) and the Iwahori–Weyl group
  `W̃^0 = N(F)/Z(F)^0` of KP Definition 6.6.1 (`IwahoriWeylGroup`), the type of cosets;
* `N(F) ∩ G(F)^0` (`normalizerZeroComponent`) and its image in `W̃^0` (`affinePart`), the
  subgroup that KP Theorem 7.8.1(1) identifies with the affine Weyl group `W_aff`;
* the homomorphism `W̃^0 → G(F)/G(F)^0` induced by `N(F) ⊆ G(F)` (`toComponents`);
* the images in `W̃^0` of the stabilizer in `N(F)` of a chamber (`chamberStabilizer`, the
  group `W̃^0_C` of KP 7.8.2) and of the stabilizer in `N(F) ∩ G(F)^0` of a facet
  (`affineFacetStabilizer`, the group `W^aff_F` of KP Proposition 7.5.5 and Theorem 7.8.1(3)).

`W̃^0` is only a type of cosets here. Normality of `Z(F)^0` in `N(F)` and of `G(F)^0` in `G(F)`
is not proved in the Library; the group structures are used only under the corresponding
instance arguments. The affine Weyl group `W(Ψ)` of the affine roots of the apartment is the
separate published `AffineRootSystem.affineWeylGroup`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

namespace ParahoricBuildingData

variable (P : ParahoricBuildingData G)

/-! ### `Z(F)^0 ⊆ N(F)` and `W̃^0 = N(F)/Z(F)^0` -/

/-- `Z(F)^0` as a subgroup of `N(F)`: the image of `Z(F)^0` under `Z(F) → N(F)`. -/
def normalizerZero : Subgroup (normalizerPoints P.i) :=
  P.centralizerZero.map P.centralizer.toNormalizer

theorem mem_normalizerZero_iff {n : normalizerPoints P.i} :
    n ∈ P.normalizerZero ↔
      (n : rationalPoints G) ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, hn⟩
    exact ⟨z, hz, Subtype.ext hn⟩

/-- The Iwahori–Weyl group `W̃^0 = N(F)/Z(F)^0` (KP Definition 6.6.1), as the type of left
cosets of `Z(F)^0` in `N(F)`. It is a group under `[P.normalizerZero.Normal]`. -/
abbrev IwahoriWeylGroup : Type u :=
  normalizerPoints P.i ⧸ P.normalizerZero

/-! ### The affine part and the components -/

/-- `N(F) ∩ G(F)^0`, as a subgroup of `N(F)`. -/
def normalizerZeroComponent : Subgroup (normalizerPoints P.i) :=
  P.zeroSubgroup.subgroupOf (normalizerPoints P.i)

theorem normalizerZero_le_normalizerZeroComponent :
    P.normalizerZero ≤ P.normalizerZeroComponent := by
  intro n hn
  exact P.zeroDatum.map_centralizerZero_le_zeroSubgroup ((P.mem_normalizerZero_iff).1 hn)

/-- The image `(N(F) ∩ G(F)^0)/Z(F)^0` of `N(F) ∩ G(F)^0` in `W̃^0`, the kernel of
`W̃^0 → G(F)/G(F)^0` that KP Theorem 7.8.1(1) identifies with `W_aff`. -/
def affinePart [P.normalizerZero.Normal] : Subgroup P.IwahoriWeylGroup :=
  P.normalizerZeroComponent.map (QuotientGroup.mk' P.normalizerZero)

/-- The projection `N(F) ∩ G(F)^0 → (N(F) ∩ G(F)^0)/Z(F)^0`. -/
def affinePartMk [P.normalizerZero.Normal] : P.normalizerZeroComponent →* P.affinePart :=
  (QuotientGroup.mk' P.normalizerZero).subgroupMap P.normalizerZeroComponent

theorem normalizerZero_le_ker_toComponents [P.zeroSubgroup.Normal] :
    P.normalizerZero ≤
      ((QuotientGroup.mk' P.zeroSubgroup).comp (normalizerPoints P.i).subtype).ker := by
  intro n hn
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact P.normalizerZero_le_normalizerZeroComponent hn

/-- The homomorphism `W̃^0 → G(F)/G(F)^0` induced by the inclusion `N(F) ⊆ G(F)`
(KP Theorem 7.8.1(1)). -/
def toComponents [P.normalizerZero.Normal] [P.zeroSubgroup.Normal] :
    P.IwahoriWeylGroup →* rationalPoints G ⧸ P.zeroSubgroup :=
  QuotientGroup.lift P.normalizerZero
    ((QuotientGroup.mk' P.zeroSubgroup).comp (normalizerPoints P.i).subtype)
    P.normalizerZero_le_ker_toComponents

theorem toComponents_mk [P.normalizerZero.Normal] [P.zeroSubgroup.Normal]
    (n : normalizerPoints P.i) :
    P.toComponents (QuotientGroup.mk n) = QuotientGroup.mk (n : rationalPoints G) :=
  rfl

/-! ### Stabilizers of chambers and facets -/

/-- The stabilizer `{n ∈ N(F) | n · Ω = Ω}` of a subset `Ω` of the apartment. -/
def normalizerStabilizer (Ω : Set P.Apartment) : Subgroup (normalizerPoints P.i) :=
  MulAction.stabilizer (normalizerPoints P.i) Ω

theorem mem_normalizerStabilizer {Ω : Set P.Apartment} {n : normalizerPoints P.i} :
    n ∈ P.normalizerStabilizer Ω ↔ n • Ω = Ω :=
  MulAction.mem_stabilizer_iff

/-- `W̃^0_C`, the stabilizer of `C` in `W̃^0` (KP 7.8.2): the image of the stabilizer of `C`
in `N(F)`. -/
def chamberStabilizer [P.normalizerZero.Normal] (C : Set P.Apartment) :
    Subgroup P.IwahoriWeylGroup :=
  (P.normalizerStabilizer C).map (QuotientGroup.mk' P.normalizerZero)

/-- `W^aff_F`, the stabilizer of `F` in `W_aff = (N(F) ∩ G(F)^0)/Z(F)^0` (KP Proposition 7.5.5,
Theorem 7.8.1(3)): the image of the stabilizer of `F` in `N(F) ∩ G(F)^0`. -/
def affineFacetStabilizer [P.normalizerZero.Normal] (Fa : Set P.Apartment) :
    Subgroup P.IwahoriWeylGroup :=
  (P.normalizerZeroComponent ⊓ P.normalizerStabilizer Fa).map
    (QuotientGroup.mk' P.normalizerZero)

theorem affineFacetStabilizer_le_affinePart [P.normalizerZero.Normal] (Fa : Set P.Apartment) :
    P.affineFacetStabilizer Fa ≤ P.affinePart :=
  Subgroup.map_mono inf_le_left

end ParahoricBuildingData

end Langlands.Geometry.Building
