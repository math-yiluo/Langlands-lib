import Langlands.BruhatTits.Parabolic.QuotientCompactStatement
import Langlands.GroupScheme.Dynamic.FlagQuotientStatement
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.AlgebraicGeometry.PointTopology.SchemeLocalSections
import Langlands.Group.LeftQuotientInversion

/-! # Actual dynamic-parabolic quotient comparison with a flag model -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits

section FlagComparison

variable (k : Type u) [Field k] [TopologicalSpace k] [ContinuousMul k] [IsOpenUnits k]
variable (G : Langlands.GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
variable (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
variable (Q : Over (Spec (CommRingCat.of k))) (π : G.X ⟶ Q)
variable
  (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
    g ≫ π = h ≫ π ↔
      g⁻¹ * h ∈ (Langlands.GroupScheme.Dynamic.parabolic χ).carrier T)
  (hs : HasOpenSectionsAtPoints k k π)

/-- Exact algebraic fibers and algebraic local sections identify the existing
dynamic coset quotient topology with the canonical flag-point topology. -/
def dynamicParabolicFlagHomeomorph :
    letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
    letI : TopologicalSpace (RingPoint k Q k) := schemePointTopology k Q k
    (RationalPoint k G.X ⧸
      (Langlands.GroupScheme.Dynamic.parabolic χ).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k))))) ≃ₜ RingPoint k Q k := by
  letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
  letI : TopologicalSpace (RingPoint k Q k) := schemePointTopology k Q k
  let e := rationalPointHomeomorph k G.X
  let f : RationalPoint k G.X → RingPoint k Q k := fun g => e g ≫ π
  have hc := schemePointContinuity_proof k k G.X Q π
  have hsec := hasContinuousLocalSections_schemePointMap k k π hs
  rw [schemePointTopology_eq_affine k G.X k] at hc hsec
  have hf : Continuous f := hc.comp e.continuous
  have hsf : Langlands.Topology.HasContinuousLocalSections f := by
    intro y
    obtain ⟨U, hU, hy, s, hcont, hright⟩ := hsec y
    refine ⟨U, hU, hy, (fun z => e.symm (s z)), e.symm.continuous.comp hcont, ?_⟩
    intro z
    change e (e.symm (s z)) ≫ π = z.val
    rw [e.apply_symm_apply]
    exact hright z
  apply Langlands.Topology.quotientHomeomorphOfLocalSections _ f hf _ hsf
  intro g h
  rw [QuotientGroup.leftRel_apply]
  constructor
  · intro hp
    change rationalPointEquiv k G.X g ≫ π = rationalPointEquiv k G.X h ≫ π
    rw [← rationalPointEquiv_natural k π g, ← rationalPointEquiv_natural k π h]
    exact congrArg (rationalPointEquiv k Q) ((hfib _ g h).mpr hp)
  · intro hh
    apply (hfib _ g h).mp
    apply (rationalPointEquiv k Q).injective
    rw [rationalPointEquiv_natural k π g, rationalPointEquiv_natural k π h]
    exact hh

@[simp] theorem dynamicParabolicFlagHomeomorph_mk (g : RationalPoint k G.X) :
    dynamicParabolicFlagHomeomorph k G χ Q π hfib hs (QuotientGroup.mk g) =
      rationalPointEquiv k G.X g ≫ π := rfl

end FlagComparison

section Inversion

variable (k : Type u) [Field k] [TopologicalSpace k] [IsTopologicalRing k]
variable (G : Langlands.GroupScheme (Spec (CommRingCat.of k)))
variable (hG : Langlands.GroupScheme.IsConnectedReductive G)
variable (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

/-- Inversion on the actual rational-point group descends between its two
canonical dynamic-parabolic quotient conventions. -/
def dynamicParabolicQuotientInversion :
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
    let P := (Langlands.GroupScheme.Dynamic.parabolic χ).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    Langlands.Induction.LeftQuotient P ≃ₜ (RationalPoint k G.X ⧸ P) := by
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
  letI : IsTopologicalGroup (RationalPoint k G.X) := rationalPoint_isTopologicalGroup k G
  exact Langlands.Induction.quotientInversion _

end Inversion

/-- The remaining algebraic existence and proper-point compactness theorems
imply the unchanged full compactness target. -/
theorem dynamicParabolicQuotientCompact_of_flag_and_proper_points
    (hflag : Langlands.GroupScheme.DynamicFlagQuotientExistenceStatement.{u})
    (hproper : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (Q : Over (Spec (CommRingCat.of F))),
      IsProper Q.hom →
        @CompactSpace (RingPoint F Q F) (schemePointTopology F Q F)) :
    DynamicParabolicQuotientCompactStatement.{u} := by
  intro F _ _ _ _ G hG χ
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : IsOpenUnits F := inferInstance
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  obtain ⟨Q, π, hQ, hfib, hs⟩ := hflag F G hG χ
  have hsections : HasOpenSectionsAtPoints F F π := by
    intro p
    obtain ⟨U, s, hp, hsec⟩ := hs p
    exact ⟨U, hp, s, hsec⟩
  let : TopologicalSpace (RingPoint F Q F) := schemePointTopology F Q F
  let : CompactSpace (RingPoint F Q F) := hproper F Q hQ
  have hright := (dynamicParabolicFlagHomeomorph F G χ Q π hfib hsections).symm.compactSpace
  refine ⟨hright, ?_⟩
  let := hright
  exact (dynamicParabolicQuotientInversion F G hG χ).symm.compactSpace

end Langlands.BruhatTits
