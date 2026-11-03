import Langlands.Geometry.Building.KPCentralizerCompatibility
import Langlands.Geometry.Building.RankZeroAffineRootSystem
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.QuasiSplit

/-!
# The Kaletha–Prasad axioms on a single apartment class

For a nonarchimedean local field `F`, `D : KPApartmentData i (localFieldOrder F)` and the actual
centralizer `C : CentralizerDatum i`, the predicate `D.SatisfiesApartmentAxioms C` collects the
conditions of Kaletha–Prasad on the equipollence class `A(S)` that can be stated on `D` alone:

* V 6 on all of `Z(F)` (KP Definition 6.1.2), as the published `D.IsOmegaCompatible C`;
* V 7 (KP Definition 6.1.2): the `U_{a,φ,r}` are bounded open subgroups of `U_a(F)` forming a
  neighbourhood base of `1`, with KP's algebraic boundedness (KP Definition 2.2.1);
* AS 2, AS 3 and AS 4 (KP Axiom 4.1.6) for the sets `Ψ′` and `Ψ` of `D`;
* AS 5 (KP Axiom 4.1.6) for the action of `N(F)` on the apartment, with its simply connected and
  quasi-split adjoint sentences.

This is only part of the corrected KP Definition 4.1.26. It is not the full validity predicate:
AS 1, the `m(u)`-form of AS 2, AS 6 and the building-level axioms are not included.

Without relative roots the apartment is a point, `Ψ′ = Ψ = ∅` is the rank-zero affine root
system, and the predicate reduces to V 6
(`satisfiesApartmentAxioms_iff_of_relativeRoots_eq_empty`).

Separately, `D.HasBoundedOpenStabilizers` is KP Axiom 4.1.2 for the reduced building of `D`:
every `G(F)^1_y` is a bounded open subgroup of `G(F)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}

/-! ### Axiom V 7 -/

section Topology

variable (i : S.toGrp ⟶ G) [IsAffineHom G.X.hom]

/-- KP axiom V 7 (Definition 6.1.2) for a family `φ`, for the published topology
`rationalPointTopology F G.X` of `G(F)`: for every root `a`, the sets `U_{a,φ,r}` (`r ∈ ℝ`) are
open in `U_a(F)`, bounded as subsets of `G(F)` in the sense of KP Definition 2.2.1, and form a
neighbourhood base of `1` in `U_a(F)`. -/
def IsTopologyCompatible (φ : RootFunctionFamily S G) : Prop :=
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  ∀ a ∈ relativeRoots i,
    (nhds (1 : rootGroupPoints i a)).HasBasis (fun _ : ℝ => True)
        (fun r => ((↑) : rootGroupPoints i a → rationalPoints G) ⁻¹' rootFiltration i φ a r) ∧
      ∀ r : ℝ,
        IsOpen (((↑) : rootGroupPoints i a → rationalPoints G) ⁻¹' rootFiltration i φ a r) ∧
          IsAlgebraicallyBounded F G.X (rootFiltration i φ a r)

variable {i}

/-- Translates of a V 7-compatible family are V 7-compatible. -/
theorem IsTopologyCompatible.vadd {φ : RootFunctionFamily S G}
    (hφ : IsTopologyCompatible i φ) (v : V S) : IsTopologyCompatible i (v +ᵥ φ) := by
  unfold IsTopologyCompatible at hφ ⊢
  intro a ha
  obtain ⟨hb, hr⟩ := hφ a ha
  refine ⟨hb.to_hasBasis (fun r _ => ⟨r + eval S a v, trivial, ?_⟩)
    (fun r _ => ⟨r - eval S a v, trivial, ?_⟩), fun r => ?_⟩
  · rw [rootFiltration_vadd]
  · rw [rootFiltration_vadd']
  · rw [rootFiltration_vadd']
    exact hr _

end Topology

namespace KPApartmentData

variable {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : Fˣ → ℝ}
  (D : KPApartmentData i ω)

/-- KP axiom V 7 for every valuation of the class `A`. -/
def IsTopologyCompatible : Prop :=
  ∀ φ ∈ D.carrier, Building.IsTopologyCompatible i φ

variable {D}

/-- V 7 holds for the whole class `A` as soon as it holds for one of its valuations. -/
theorem isTopologyCompatible_iff_of_mem {φ : RootFunctionFamily S G} (hφ : φ ∈ D.carrier) :
    D.IsTopologyCompatible ↔ Building.IsTopologyCompatible i φ := by
  refine ⟨fun hD => hD φ hφ, fun hc ψ hψ => ?_⟩
  obtain ⟨v, rfl⟩ := D.equipollent_of_mem hφ hψ
  exact hc.vadd v

end KPApartmentData

/-! ### The axioms on one apartment class -/

namespace KPApartmentData

variable [IsNonarchimedeanLocalField F] {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  [IsAffineHom G.X.hom] {D : KPApartmentData i (localFieldOrder F)} {C : CentralizerDatum i}

/-- Under V 6, `z ∈ Z(F)` acts on the apartment as the translation by the class of `ν(z)`
(KP Axiom 4.1.4 (A 1)). -/
theorem IsOmegaCompatible.normalizerAffineEquiv_eq (hD : D.IsOmegaCompatible C)
    (z : rationalPoints C.Z) :
    D.normalizerAffineEquiv (C.toNormalizer z) =
      AffineEquiv.constVAdd ℝ D.Apartment
        (Submodule.Quotient.mk (C.translation z).toAdd : TranslationSpace i) :=
  AffineEquiv.ext fun x => hD.smul_eq_vadd z x

variable (D C) in
/-- The conditions of Kaletha–Prasad on the single class `A(S)` (V 6 and V 7 of Definition 6.1.2,
AS 2–AS 5 of Axiom 4.1.6) beyond those built into `KPApartmentData`, for the actual centralizer
`C`. This is only part of the corrected Definition 4.1.26: AS 1, the `m(u)`-form of AS 2, AS 6
and the axioms on the building are not included. -/
structure SatisfiesApartmentAxioms : Prop where
  /-- V 6 on `Z(F)`. -/
  omegaCompatible : D.IsOmegaCompatible C
  /-- V 7. -/
  topologyCompatible : D.IsTopologyCompatible
  /-- AS 2: `Ψ′` is an affine root system. -/
  isAffineRootSystem_extendedAffineRoots :
    AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots
  /-- AS 2: the derivative of `Ψ′` is `Φ`. -/
  derivativeRoots_extendedAffineRoots :
    AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i)
  /-- AS 3: `Ψ` is an affine root system. -/
  isAffineRootSystem_affineRoots : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots
  /-- AS 3: the derivative of `Ψ` is `Φ`. -/
  derivativeRoots_affineRoots :
    AffineRootSystem.derivativeRoots D.affineRoots = Set.range (rootForm i)
  /-- AS 4: for `ψ ∈ Ψ′`, at least one of `ψ`, `2ψ` lies in `Ψ`. -/
  mem_or_two_smul_mem :
    ∀ ψ ∈ D.extendedAffineRoots, ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots
  /-- AS 5, first sentence: the image of `N(F)` contains `W(Ψ)`. -/
  affineWeylGroup_le_range :
    AffineRootSystem.affineWeylGroup D.affineRoots ≤ D.normalizerAffineEquiv.range
  /-- AS 5, first sentence: the image of `N(F)` is contained in `W(Ψ)ᵉˣᵗ`. -/
  range_le_extendedAffineWeylGroup :
    D.normalizerAffineEquiv.range ≤ AffineRootSystem.extendedAffineWeylGroup D.affineRoots
  /-- AS 5, second sentence: if `G` is simply connected, the image of `N(F)` is `W(Ψ)`. -/
  range_eq_affineWeylGroup_of_isSimplyConnected :
    IsSimplyConnected G →
      D.normalizerAffineEquiv.range = AffineRootSystem.affineWeylGroup D.affineRoots
  /-- AS 5, third sentence: if `G` is quasi-split and adjoint, the image of `N(F)` is
  `W(Ψ)ᵉˣᵗ`. -/
  range_eq_extendedAffineWeylGroup_of_isQuasiSplit_of_isAdjoint :
    IsQuasiSplit G → IsAdjoint G →
      D.normalizerAffineEquiv.range = AffineRootSystem.extendedAffineWeylGroup D.affineRoots

/-- The translations of the apartment by `ν(Z(F))` lie in `W(Ψ)ᵉˣᵗ`. -/
theorem SatisfiesApartmentAxioms.constVAdd_mem_extendedAffineWeylGroup
    (hD : D.SatisfiesApartmentAxioms C) (z : rationalPoints C.Z) :
    AffineEquiv.constVAdd ℝ D.Apartment
        (Submodule.Quotient.mk (C.translation z).toAdd : TranslationSpace i) ∈
      AffineRootSystem.extendedAffineWeylGroup D.affineRoots := by
  rw [← hD.omegaCompatible.normalizerAffineEquiv_eq z]
  exact hD.range_le_extendedAffineWeylGroup ⟨C.toNormalizer z, rfl⟩

/-! ### Rank zero -/

/-- Without relative roots the apartment is a point and `Ψ′ = Ψ = ∅` is the affine root system of
rank zero on it (KP, after Definition 1.3.1). Then V 7, AS 2–AS 4 and AS 5 hold automatically, so
the axioms reduce to V 6. -/
theorem satisfiesApartmentAxioms_iff_of_relativeRoots_eq_empty (h : relativeRoots i = ∅) :
    D.SatisfiesApartmentAxioms C ↔ D.IsOmegaCompatible C := by
  have hempty : IsEmpty (relativeRoots i) := Set.isEmpty_coe_sort.2 h
  have hV : Subsingleton (TranslationSpace i) :=
    Submodule.Quotient.subsingleton_iff.2 <| eq_top_iff.2 fun v _ =>
      mem_rootAnnihilator.2 fun a ha => absurd ha (h ▸ Set.notMem_empty a)
  have hA : Subsingleton D.Apartment :=
    ⟨fun x y => by rw [← vsub_vadd x y, Subsingleton.elim (x -ᵥ y) 0, zero_vadd]⟩
  have hE : Subsingleton (D.Apartment ≃ᵃ[ℝ] D.Apartment) :=
    ⟨fun e e' => AffineEquiv.ext fun _ => Subsingleton.elim _ _⟩
  have hle : ∀ H K : Subgroup (D.Apartment ≃ᵃ[ℝ] D.Apartment), H ≤ K :=
    fun _ K x _ => Subsingleton.elim x 1 ▸ K.one_mem
  have hext : D.extendedAffineRoots = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun _ ⟨α, _⟩ => hempty.elim α
  have hroots : D.affineRoots = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun _ ⟨α, _⟩ => hempty.elim α
  have hrange : Set.range (rootForm i) = ∅ := Set.range_eq_empty_iff.2 hempty
  have hsys : AffineRootSystem.IsAffineRootSystemWithRankZero (∅ : Set (D.Apartment →ᵃ[ℝ] ℝ)) :=
    AffineRootSystem.isAffineRootSystemWithRankZero_empty_iff.2 hV
  refine ⟨fun hD => hD.omegaCompatible, fun hD => ⟨hD, fun _ _ a ha => hempty.elim ⟨a, ha⟩,
    ?_, ?_, ?_, ?_, ?_, hle _ _, hle _ _, fun _ => le_antisymm (hle _ _) (hle _ _),
    fun _ _ => le_antisymm (hle _ _) (hle _ _)⟩⟩
  · rw [hext]; exact hsys
  · rw [hext, hrange]; exact Set.image_empty _
  · rw [hroots]; exact hsys
  · rw [hroots, hrange]; exact Set.image_empty _
  · rw [hext]; exact fun _ h => h.elim

/-! ### Axiom 4.1.2 on the reduced building -/

variable (D) in
/-- KP Axiom 4.1.2 for the reduced building `B(G)` of `D`: for every point `y`, the stabilizer
`G(F)^1_y = D.compactStabilizer y` of `y` in `G(F)^1` is an open subgroup of `G(F)` for the
published topology `rationalPointTopology F G.X`, and bounded in the sense of KP
Definition 2.2.1. -/
def HasBoundedOpenStabilizers : Prop :=
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  ∀ y : D.ReducedBuilding,
    IsOpen (D.compactStabilizer y : Set (rationalPoints G)) ∧
      IsAlgebraicallyBounded F G.X (D.compactStabilizer y : Set (rationalPoints G))

end KPApartmentData

end Langlands.Geometry.Building
