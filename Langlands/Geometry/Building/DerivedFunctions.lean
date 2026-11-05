import Langlands.Geometry.Building.DerivedTranslation
import Langlands.Geometry.Building.CentralIsogenyFunctions

/-! # Normalized root-function pullback through an actual derived inclusion -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G) (hd : IsDerivedSubgroup d)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (hA : IsSplitTorus A.toGrp)
    [Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))

/-- On rational root points the original derived inclusion is a multiplicative
equivalence for corresponding actual roots. -/
def derivedRootGroupPointsEquiv (a : relativeRoots i) :
    rootGroupPoints j (e ≫ a.val) ≃* rootGroupPoints i a.val :=
  RelativeRoot.derivedRelativeRootPointsEquiv e c j i d hd h hT hS hA hc a.val
    a.property (Over.mk (𝟙 _))

omit [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom] in
@[simp]
theorem derivedRootGroupPointsEquiv_coe (a : relativeRoots i)
    (g : rootGroupPoints j (e ≫ a.val)) :
    (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a g : rationalPoints G) =
      rationalPoints.map d g.val := rfl

namespace RootFunctionFamily

/-- Restrict to actual derived root groups, then compose with the original
derived inclusion and the inverse of the actual root bijection. -/
def derivedPullback (φ : RootFunctionFamily S G) : RootFunctionFamily T D := by
  classical
  exact ⟨fun a g => if ha : a ∈ relativeRoots j then
      if g ∈ rootGroupPoints j a then
        φ ((RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc).symm
          ⟨a, ha⟩).val (rationalPoints.map d g)
      else ⊤
    else ⊤⟩

/-- Every derived pullback satisfies the original normalization conventions. -/
theorem derivedPullback_isNormalized (φ : RootFunctionFamily S G) :
    IsNormalized j (derivedPullback e c j i d hd h hT hS hA hc φ) := by
  constructor
  · intro a ha g
    simp only [derivedPullback, coe_mk, dite_eq_right ha]
  · intro a ha g hg
    simp only [derivedPullback, coe_mk, dite_eq_left ha, ite_eq_right hg]

/-- Evaluation on an actual source root subgroup uses its corresponding
original ambient root. -/
theorem derivedPullback_apply (φ : RootFunctionFamily S G) (a : relativeRoots j)
    (g : rationalPoints D) (hg : g ∈ rootGroupPoints j a.val) :
    derivedPullback e c j i d hd h hT hS hA hc φ a.val g =
      φ ((RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc).symm a).val
        (rationalPoints.map d g) := by
  simp only [derivedPullback, coe_mk, dite_eq_left a.property, ite_eq_left hg]

/-- Pullback preserves each value on corresponding actual root points. -/
theorem derivedPullback_apply_root (φ : RootFunctionFamily S G) (a : relativeRoots i)
    (g : rationalPoints D) (hg : g ∈ rootGroupPoints j (e ≫ a.val)) :
    derivedPullback e c j i d hd h hT hS hA hc φ (e ≫ a.val) g =
      φ a.val (rationalPoints.map d g) := by
  exact (derivedPullback_apply e c j i d hd h hT hS hA hc φ
    (RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc a) g hg).trans
    (congrArg (fun b : relativeRoots i => φ b.val (rationalPoints.map d g))
      (Equiv.symm_apply_apply _ a))

/-- Original real translations commute with the normalized derived pullback. -/
theorem derivedPullback_vadd (φ : RootFunctionFamily S G) (v : V T) :
    derivedPullback e c j i d hd h hT hS hA hc (cocharacterMapReal e v +ᵥ φ) =
      v +ᵥ derivedPullback e c j i d hd h hT hS hA hc φ := by
  ext a g
  by_cases ha : a ∈ relativeRoots j
  · by_cases hg : g ∈ rootGroupPoints j a
    · let a' := (RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc).symm
        ⟨a, ha⟩
      have he : e ≫ a'.val = a := congrArg Subtype.val
        ((RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc).apply_symm_apply
          ⟨a, ha⟩)
      simp only [derivedPullback, coe_mk, dite_eq_left ha, ite_eq_left hg, vadd_apply,
        eval_cocharacterMapReal]
      rw [he]
    · simp only [vadd_apply, derivedPullback, coe_mk, dite_eq_left ha, ite_eq_right hg,
        WithTop.top_add]
  · simp only [vadd_apply, derivedPullback, coe_mk, dite_eq_right ha, WithTop.top_add]

include hA hc in
/-- The image of the central complement acts trivially on normalized ambient
families. -/
theorem IsNormalized.centralComplement_vadd {φ : RootFunctionFamily S G}
    (hφ : IsNormalized i φ) (z : V A) : cocharacterMapReal c z +ᵥ φ = φ := by
  ext a g
  rw [vadd_apply, eval_cocharacterMapReal]
  by_cases ha : a ∈ relativeRoots i
  · rw [root_restrict_eq_zero_of_isCentral i c hA hc ha, eval_zero_char,
      WithTop.coe_zero, add_zero]
  · rw [hφ.1 a ha g, WithTop.top_add]

omit [LocallyOfFiniteType D.X.hom] [Smooth G.X.hom] in
/-- The common root kernel acts trivially on every normalized family. -/
theorem IsNormalized.vadd_eq_self_of_mem_rootAnnihilator
    {φ : RootFunctionFamily S G} (hφ : IsNormalized i φ)
    {v : V S} (hv : v ∈ rootAnnihilator i) : v +ᵥ φ = φ := by
  ext a g
  by_cases ha : a ∈ relativeRoots i
  · rw [vadd_apply, (mem_rootAnnihilator.mp hv) a ha, WithTop.coe_zero, add_zero]
  · rw [vadd_apply, hφ.1 a ha g, WithTop.top_add]

/-- A normalized ambient family is determined by its derived pullback. -/
theorem derivedPullback_injective {φ ψ : RootFunctionFamily S G}
    (hφ : IsNormalized i φ) (hψ : IsNormalized i ψ)
    (heq : derivedPullback e c j i d hd h hT hS hA hc φ =
      derivedPullback e c j i d hd h hT hS hA hc ψ) : φ = ψ := by
  ext a g
  by_cases ha : a ∈ relativeRoots i
  · by_cases hg : g ∈ rootGroupPoints i a
    · obtain ⟨u, hu⟩ :=
        (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc ⟨a, ha⟩).surjective
          ⟨g, hg⟩
      have hu' : rationalPoints.map d u.val = g := congrArg Subtype.val hu
      have hp := congrArg (fun Φ : RootFunctionFamily T D => Φ (e ≫ a) u.val) heq
      rw [derivedPullback_apply_root e c j i d hd h hT hS hA hc φ ⟨a, ha⟩ u.val u.property,
        derivedPullback_apply_root e c j i d hd h hT hS hA hc ψ ⟨a, ha⟩ u.val u.property,
        hu'] at hp
      exact hp
    · rw [hφ.2 a ha g hg, hψ.2 a ha g hg]
  · rw [hφ.1 a ha g, hψ.1 a ha g]

/-- The actual derived pullback preserves and reflects equipollence of
normalized families, including ambient central translation directions. -/
theorem equipollent_derivedPullback_iff {φ ψ : RootFunctionFamily S G}
    (hφ : IsNormalized i φ) (hψ : IsNormalized i ψ) :
    Equipollent (derivedPullback e c j i d hd h hT hS hA hc φ)
        (derivedPullback e c j i d hd h hT hS hA hc ψ) ↔ Equipollent φ ψ := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨cocharacterMapReal e v,
      derivedPullback_injective e c j i d hd h hT hS hA hc hψ (hφ.vadd _) ?_⟩
    rw [derivedPullback_vadd]
    exact hv
  · rintro ⟨w, rfl⟩
    obtain ⟨v, z, hw⟩ :=
      exists_eq_cocharacterMapReal_add_of_centralComplement e c hT hA hS w
    refine ⟨v, ?_⟩
    rw [hw, add_vadd, hφ.centralComplement_vadd c i hA hc z, derivedPullback_vadd]

end RootFunctionFamily

open RootFunctionFamily

/-- Filtration membership compares the original derived point and its
literal image in the original ambient root group. -/
theorem rootFiltration_derivedPullback_iff (φ : RootFunctionFamily S G)
    (a : relativeRoots i) (r : ℝ) (g : rationalPoints D) :
    g ∈ rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ) (e ≫ a.val) r ↔
      g ∈ rootGroupPoints j (e ≫ a.val) ∧
        rationalPoints.map d g ∈ rootFiltration i φ a.val r := by
  constructor
  · rintro ⟨hg, hv⟩
    rw [derivedPullback_apply_root e c j i d hd h hT hS hA hc φ a g hg] at hv
    exact ⟨hg, (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a ⟨g, hg⟩).property,
      hv⟩
  · rintro ⟨hg, _, hv⟩
    exact ⟨hg, by rw [derivedPullback_apply_root e c j i d hd h hT hS hA hc φ a g hg]; exact hv⟩

/-- Every original ambient root filtration is the exact image of the
corresponding pulled-back derived filtration. -/
theorem image_rootFiltration_derivedPullback (φ : RootFunctionFamily S G)
    (a : relativeRoots i) (r : ℝ) :
    rationalPoints.map d ''
        rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ) (e ≫ a.val) r =
      rootFiltration i φ a.val r := by
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ((rootFiltration_derivedPullback_iff e c j i d hd h hT hS hA hc φ a r u).mp hu).2
  · intro hg
    obtain ⟨u, hu⟩ :=
      (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a).surjective ⟨g, hg.1⟩
    have hu' : rationalPoints.map d u.val = g := congrArg Subtype.val hu
    refine ⟨u.val, ?_, hu'⟩
    exact (rootFiltration_derivedPullback_iff e c j i d hd h hT hS hA hc φ a r u.val).mpr
      ⟨u.property, by rw [hu']; exact hg⟩

end Langlands.Geometry.Building
