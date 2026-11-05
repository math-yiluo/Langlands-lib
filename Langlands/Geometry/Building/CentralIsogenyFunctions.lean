import Langlands.Geometry.Building.CentralIsogenyTranslation
import Langlands.GroupScheme.Rational.CentralIsogenyRootTransport

/-! # Normalized root-function pullback through a central isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {C G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  (q : C ⟶ G) (hq : IsCentralIsogeny q)
  (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
  (t : S ⟶ T) (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)
  (ht : IsIsogeny (CommGroupScheme.groupHom t))

/-- The actual rational root-point equivalence for corresponding actual roots. -/
def centralIsogenyRootGroupPointsEquiv (a : relativeRoots j) :
    rootGroupPoints i (t ≫ a.val) ≃* rootGroupPoints j a.val := by
  letI : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Flat (CommGroupScheme.groupHom t).hom.hom.left := ht.2.1
  letI : Surjective (CommGroupScheme.groupHom t).hom.hom.left := ht.2.2
  exact RelativeRoot.centralIsogenyRootTransportEquiv q i j t h a.val hq hS a.property.1

@[simp] theorem centralIsogenyRootGroupPointsEquiv_coe (a : relativeRoots j)
    (g : rootGroupPoints i (t ≫ a.val)) :
    (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a g : rationalPoints G) =
      rationalPoints.map q g.val := rfl

variable [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom]

namespace RootFunctionFamily

/-- The two normalization conventions of the published full family model. -/
def IsNormalized (i : S.toGrp ⟶ C) (φ : RootFunctionFamily S C) : Prop :=
  (∀ a ∉ relativeRoots i, ∀ g, φ a g = ⊤) ∧
  (∀ a ∈ relativeRoots i, ∀ g ∉ rootGroupPoints i a, φ a g = ⊤)

/-- Restrict to actual source root groups before composing with the central isogeny. -/
def centralIsogenyPullback (φ : RootFunctionFamily T G) : RootFunctionFamily S C := by
  classical
  exact ⟨fun a g => if ha : a ∈ relativeRoots i then
      if g ∈ rootGroupPoints i a then
        φ ((centralIsogenyRootPullbackEquiv q hq hS hT t h ht).symm ⟨a, ha⟩).val
          (rationalPoints.map q g)
      else ⊤
    else ⊤⟩

/-- Every pulled-back family satisfies the source normalization conventions. -/
theorem centralIsogenyPullback_isNormalized (φ : RootFunctionFamily T G) :
    IsNormalized i (centralIsogenyPullback q hq hS hT t h ht φ) := by
  constructor
  · intro a ha g
    simp only [centralIsogenyPullback, coe_mk, dite_eq_right ha]
  · intro a ha g hg
    simp only [centralIsogenyPullback, coe_mk, dite_eq_left ha, ite_eq_right hg]

/-- On an actual source root group, pullback uses the corresponding target root. -/
theorem centralIsogenyPullback_apply (φ : RootFunctionFamily T G)
    (a : relativeRoots i) (g : rationalPoints C) (hg : g ∈ rootGroupPoints i a.val) :
    centralIsogenyPullback q hq hS hT t h ht φ a.val g =
      φ ((centralIsogenyRootPullbackEquiv q hq hS hT t h ht).symm a).val
        (rationalPoints.map q g) := by
  simp only [centralIsogenyPullback, coe_mk, dite_eq_left a.property, ite_eq_left hg]

/-- Evaluation is unchanged on corresponding roots and actual source root points. -/
theorem centralIsogenyPullback_apply_root (φ : RootFunctionFamily T G)
    (a : relativeRoots j) (g : rationalPoints C) (hg : g ∈ rootGroupPoints i (t ≫ a.val)) :
    centralIsogenyPullback q hq hS hT t h ht φ (t ≫ a.val) g =
      φ a.val (rationalPoints.map q g) := by
  exact (centralIsogenyPullback_apply q hq hS hT t h ht φ
    (centralIsogenyRootPullbackEquiv q hq hS hT t h ht a) g hg).trans
    (congrArg (fun b : relativeRoots j => φ b.val (rationalPoints.map q g))
      (Equiv.symm_apply_apply _ a))

/-- The original real translations commute with normalized pullback. -/
theorem centralIsogenyPullback_vadd (φ : RootFunctionFamily T G) (v : V S) :
    centralIsogenyPullback q hq hS hT t h ht (cocharacterMapReal t v +ᵥ φ) =
      v +ᵥ centralIsogenyPullback q hq hS hT t h ht φ := by
  ext a g
  by_cases ha : a ∈ relativeRoots i
  · by_cases hg : g ∈ rootGroupPoints i a
    · let a' := (centralIsogenyRootPullbackEquiv q hq hS hT t h ht).symm ⟨a, ha⟩
      have he : t ≫ a'.val = a := congrArg Subtype.val
        ((centralIsogenyRootPullbackEquiv q hq hS hT t h ht).apply_symm_apply ⟨a, ha⟩)
      simp only [centralIsogenyPullback, coe_mk, dite_eq_left ha, ite_eq_left hg, vadd_apply,
        eval_cocharacterMapReal]
      rw [he]
    · simp only [vadd_apply, centralIsogenyPullback, coe_mk, dite_eq_left ha, ite_eq_right hg,
        WithTop.top_add]
  · simp only [vadd_apply, centralIsogenyPullback, coe_mk, dite_eq_right ha, WithTop.top_add]

omit [LocallyOfFiniteType G.X.hom] in
/-- Translating a normalized family preserves its normalization. -/
theorem IsNormalized.vadd {φ : RootFunctionFamily T G} (hφ : IsNormalized j φ) (v : V T) :
    IsNormalized j (v +ᵥ φ) := by
  constructor
  · intro a ha g
    rw [vadd_apply, hφ.1 a ha g, WithTop.top_add]
  · intro a ha g hg
    rw [vadd_apply, hφ.2 a ha g hg, WithTop.top_add]

/-- A normalized target family is determined by its normalized pullback. -/
theorem centralIsogenyPullback_injective {φ ψ : RootFunctionFamily T G}
    (hφ : IsNormalized j φ) (hψ : IsNormalized j ψ)
    (heq : centralIsogenyPullback q hq hS hT t h ht φ =
      centralIsogenyPullback q hq hS hT t h ht ψ) : φ = ψ := by
  ext a g
  by_cases ha : a ∈ relativeRoots j
  · by_cases hg : g ∈ rootGroupPoints j a
    · obtain ⟨u, hu⟩ :=
        (centralIsogenyRootGroupPointsEquiv q hq hS t h ht ⟨a, ha⟩).surjective ⟨g, hg⟩
      have hu' : rationalPoints.map q u.val = g := congrArg Subtype.val hu
      have hp := congrArg (fun Φ : RootFunctionFamily S C => Φ (t ≫ a) u.val) heq
      rw [centralIsogenyPullback_apply_root q hq hS hT t h ht φ ⟨a, ha⟩ u.val u.property,
        centralIsogenyPullback_apply_root q hq hS hT t h ht ψ ⟨a, ha⟩ u.val u.property,
        hu'] at hp
      exact hp
    · rw [hφ.2 a ha g hg, hψ.2 a ha g hg]
  · rw [hφ.1 a ha g, hψ.1 a ha g]

/-- Pullback preserves and reflects equipollence of normalized families. -/
theorem equipollent_centralIsogenyPullback_iff {φ ψ : RootFunctionFamily T G}
    (hφ : IsNormalized j φ) (hψ : IsNormalized j ψ) :
    Equipollent (centralIsogenyPullback q hq hS hT t h ht φ)
        (centralIsogenyPullback q hq hS hT t h ht ψ) ↔ Equipollent φ ψ := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨cocharacterMapReal t v,
      centralIsogenyPullback_injective q hq hS hT t h ht hψ (hφ.vadd _) ?_⟩
    rw [centralIsogenyPullback_vadd]
    exact hv
  · rintro ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ :=
      (splitTorusIsogenyCocharacter k S T t hS hT ht).2.2.2.surjective w
    exact ⟨v, centralIsogenyPullback_vadd q hq hS hT t h ht φ v⟩

end RootFunctionFamily

open RootFunctionFamily

omit [LocallyOfFiniteType G.X.hom] in
/-- The published valuation predicate includes exactly these normalizations. -/
theorem IsRootDatumValuation.isNormalized [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation j φ) : IsNormalized j φ :=
  ⟨hφ.eq_top_of_not_mem_roots, hφ.eq_top_of_not_mem⟩

/-- Filtration membership compares only points in the actual source root subgroup. -/
theorem rootFiltration_centralIsogenyPullback_iff (φ : RootFunctionFamily T G)
    (a : relativeRoots j) (r : ℝ) (g : rationalPoints C) :
    g ∈ rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ) (t ≫ a.val) r ↔
      g ∈ rootGroupPoints i (t ≫ a.val) ∧
        rationalPoints.map q g ∈ rootFiltration j φ a.val r := by
  constructor
  · rintro ⟨hg, hv⟩
    rw [centralIsogenyPullback_apply_root q hq hS hT t h ht φ a g hg] at hv
    exact ⟨hg, (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a ⟨g, hg⟩).property, hv⟩
  · rintro ⟨hg, _, hv⟩
    exact ⟨hg, by rw [centralIsogenyPullback_apply_root q hq hS hT t h ht φ a g hg]; exact hv⟩

/-- Every target root filtration is exactly the image of its source filtration. -/
theorem image_rootFiltration_centralIsogenyPullback (φ : RootFunctionFamily T G)
    (a : relativeRoots j) (r : ℝ) :
    rationalPoints.map q ''
        rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ) (t ≫ a.val) r =
      rootFiltration j φ a.val r := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ((rootFiltration_centralIsogenyPullback_iff q hq hS hT t h ht φ a r g).mp hg).2
  · intro hg
    obtain ⟨u, hu⟩ :=
      (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a).surjective ⟨g, hg.1⟩
    have hu' : rationalPoints.map q u.val = g := congrArg Subtype.val hu
    refine ⟨u.val, ?_, hu'⟩
    exact (rootFiltration_centralIsogenyPullback_iff q hq hS hT t h ht φ a r u.val).mpr
      ⟨u.property, by rw [hu']; exact hg⟩

end Langlands.Geometry.Building
