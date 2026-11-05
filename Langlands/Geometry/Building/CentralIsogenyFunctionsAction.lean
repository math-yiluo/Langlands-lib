import Langlands.Geometry.Building.CentralIsogenyFunctions
import Langlands.Geometry.Building.CentralIsogenyNormalizerAction
import Langlands.GroupScheme.Rational.RootSubgroupConjugation

/-! # Normalizer equivariance of central-isogeny root-function pullback -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {C G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  (q : C ⟶ G) (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
  (t : S ⟶ T) (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)
  (ht : IsIsogeny (CommGroupScheme.groupHom t))

/-- Actual character restriction intertwines the two original Weyl actions. -/
theorem weylAction_splitTorusIsogenyNormalizerMap
    (n : normalizerPoints i) (a : characterLattice T) :
    t ≫ weylAction j (splitTorusIsogenyNormalizerMap q hS hT t h ht n) a =
      weylAction i n (t ≫ a) := by
  rw [weylAction_apply, weylAction_apply, ← Category.assoc]
  have he := congrArg
    (fun f => (normalizingAut i n).inv ≫ f ≫
      (normalizingAut j (splitTorusIsogenyNormalizerMap q hS hT t h ht n)).inv)
    (normalizingAut_splitTorusIsogenyNormalizerMap q hS hT t h ht n)
  have he' : t ≫
      (normalizingAut j (splitTorusIsogenyNormalizerMap q hS hT t h ht n)).inv =
        (normalizingAut i n).inv ≫ t := by
    simpa [Category.assoc] using he
  exact congrArg (fun f : S ⟶ T => f ≫ a) he'

/-- Reflection realization is equivalent for corresponding characters and normalizers. -/
theorem realizesReflection_splitTorusIsogenyNormalizerMap_iff
    (n : normalizerPoints i) (a : characterLattice T) :
    RealizesReflection j a (splitTorusIsogenyNormalizerMap q hS hT t h ht n) ↔
      RealizesReflection i (t ≫ a) n := by
  let : Flat (CommGroupScheme.groupHom t).hom.hom.left := ht.2.1
  let : Surjective (CommGroupScheme.groupHom t).hom.hom.left := ht.2.2
  let : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  have hc : Function.Injective (fun a : characterLattice T => t ≫ a) :=
    characterRestrict_injective_of_epi t
  have hb := (splitTorusIsogenyCocharacter k S T t hS hT ht).2.2.2
  constructor
  · rintro ⟨ha, hv⟩
    refine ⟨?_, fun v hv0 => hb.injective ?_⟩
    · rw [← weylAction_splitTorusIsogenyNormalizerMap q hS hT t h ht,
        ha, Preadditive.comp_neg]
    · change cocharacterMapReal t (normalizerAction i n v) = cocharacterMapReal t v
      rw [cocharacterMapReal_splitTorusIsogenyNormalizerMap q hS hT t h ht]
      exact hv _ ((eval_cocharacterMapReal t a v).trans hv0)
  · rintro ⟨ha, hv⟩
    refine ⟨hc ?_, fun v hv0 => ?_⟩
    · change t ≫ weylAction j (splitTorusIsogenyNormalizerMap q hS hT t h ht n) a =
        t ≫ (-a)
      rw [weylAction_splitTorusIsogenyNormalizerMap q hS hT t h ht,
        ha, Preadditive.comp_neg]
    · obtain ⟨v, rfl⟩ := hb.surjective v
      rw [eval_cocharacterMapReal] at hv0
      change normalizerAction j (splitTorusIsogenyNormalizerMap q hS hT t h ht n)
        (cocharacterMapReal t v) = _
      rw [← cocharacterMapReal_splitTorusIsogenyNormalizerMap q hS hT t h ht]
      exact congrArg (cocharacterMapReal t) (hv v hv0)

private theorem rootGroupPoints_conj_iff (n : normalizerPoints i)
    (a : characterLattice S) (g : rationalPoints C) :
    (n : rationalPoints C) * g * (n : rationalPoints C)⁻¹ ∈
      rootGroupPoints i (weylAction i n a) ↔ g ∈ rootGroupPoints i a := by
  simpa only [rootGroupPoints, GroupScheme.constantPoint_self] using
    RelativeRoot.normalizer_conj_mem_iff i a n g

variable [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]

namespace RootFunctionFamily

omit [Mono j.hom.hom.left] [IsAffineHom G.X.hom] in
/-- The actual normalizer action preserves the two normalization conventions. -/
theorem IsNormalized.smul {φ : RootFunctionFamily S C}
    (hφ : IsNormalized i φ) (n : normalizerPoints i) :
    IsNormalized i (n • φ) := by
  constructor
  · intro a ha g
    rw [smul_apply]
    exact hφ.1 _ (fun hw => ha ((weylAction_mem_roots_iff n⁻¹ a).mp hw)) _
  · intro a ha g hg
    rw [smul_apply]
    apply hφ.2 _ ((weylAction_mem_roots_iff n⁻¹ a).mpr ha) _
    intro hc
    apply hg
    exact (rootGroupPoints_conj_iff n⁻¹ a g).mp (by simpa only [Subgroup.coe_inv, inv_inv] using hc)

variable [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom]
  (hq : IsCentralIsogeny q)

/-- The actual pullback as a map between the types of normalized families. -/
def centralIsogenyNormalizedPullback :
    {φ : RootFunctionFamily T G // IsNormalized j φ} →
      {ψ : RootFunctionFamily S C // IsNormalized i ψ} :=
  fun φ => ⟨centralIsogenyPullback q hq hS hT t h ht φ.val,
    centralIsogenyPullback_isNormalized q hq hS hT t h ht φ.val⟩

omit [Mono i.hom.hom.left] [Mono j.hom.hom.left] in
/-- The normalized-family map is injective, by the actual root-point equivalences. -/
theorem centralIsogenyNormalizedPullback_injective :
    Function.Injective (centralIsogenyNormalizedPullback q hS hT t h ht hq) := by
  intro φ ψ he
  apply Subtype.ext
  exact centralIsogenyPullback_injective q hq hS hT t h ht φ.property ψ.property
    (congrArg Subtype.val he)

/-- Normalized pullback intertwines the original actual normalizer actions. -/
theorem centralIsogenyPullback_smul (n : normalizerPoints i) (φ : RootFunctionFamily T G) :
    centralIsogenyPullback q hq hS hT t h ht
        (splitTorusIsogenyNormalizerMap q hS hT t h ht n • φ) =
      n • centralIsogenyPullback q hq hS hT t h ht φ := by
  ext a g
  by_cases ha : a ∈ relativeRoots i
  · by_cases hg : g ∈ rootGroupPoints i a
    · let a' := (centralIsogenyRootPullbackEquiv q hq hS hT t h ht).symm ⟨a, ha⟩
      have he : t ≫ a'.val = a := congrArg Subtype.val
        ((centralIsogenyRootPullbackEquiv q hq hS hT t h ht).apply_symm_apply ⟨a, ha⟩)
      rw [← he] at hg ⊢
      let n' := splitTorusIsogenyNormalizerMap q hS hT t h ht n
      have hw : weylAction i n⁻¹ (t ≫ a'.val) = t ≫ weylAction j n'⁻¹ a'.val := by
        simpa only [map_inv] using
          (weylAction_splitTorusIsogenyNormalizerMap q hS hT t h ht n⁻¹ a'.val).symm
      have hc : (n : rationalPoints C)⁻¹ * g * (n : rationalPoints C) ∈
          rootGroupPoints i (t ≫ weylAction j n'⁻¹ a'.val) := by
        rw [← hw]
        simpa only [Subgroup.coe_inv, inv_inv] using
          (rootGroupPoints_conj_iff n⁻¹ (t ≫ a'.val) g).mpr hg
      rw [centralIsogenyPullback_apply_root q hq hS hT t h ht _ a' g hg,
        smul_apply, smul_apply, hw,
        centralIsogenyPullback_apply_root q hq hS hT t h ht φ
          ⟨weylAction j n'⁻¹ a'.val, weylAction_mapsTo_relativeRoots j n'⁻¹ a'.property⟩ _ hc]
      change φ (weylAction j n'⁻¹ a'.val)
          ((n' : rationalPoints G)⁻¹ * rationalPoints.map q g * (n' : rationalPoints G)) =
        φ (weylAction j n'⁻¹ a'.val)
          (rationalPoints.map q ((n : rationalPoints C)⁻¹ * g * (n : rationalPoints C)))
      simp only [map_mul, map_inv, n', splitTorusIsogenyNormalizerMap_coe]
    · have hc : (n : rationalPoints C)⁻¹ * g * (n : rationalPoints C) ∉
          rootGroupPoints i (weylAction i n⁻¹ a) := by
        intro hc
        apply hg
        exact (rootGroupPoints_conj_iff n⁻¹ a g).mp
          (by simpa only [Subgroup.coe_inv, inv_inv] using hc)
      rw [(centralIsogenyPullback_isNormalized q hq hS hT t h ht _).2 a ha g hg, smul_apply,
        (centralIsogenyPullback_isNormalized q hq hS hT t h ht φ).2 _
          (weylAction_mapsTo_relativeRoots i n⁻¹ ha) _ hc]
  · have hw : weylAction i n⁻¹ a ∉ relativeRoots i :=
      fun hw => ha ((weylAction_mem_roots_iff n⁻¹ a).mp hw)
    rw [(centralIsogenyPullback_isNormalized q hq hS hT t h ht _).1 a ha g, smul_apply,
      (centralIsogenyPullback_isNormalized q hq hS hT t h ht φ).1 _ hw]

/-- Normalizer preservation of an equipollence class is detected after pullback. -/
theorem equipollent_smul_centralIsogenyPullback_iff {φ : RootFunctionFamily T G}
    (hφ : IsNormalized j φ) (n : normalizerPoints i) :
    Equipollent (centralIsogenyPullback q hq hS hT t h ht φ)
        (n • centralIsogenyPullback q hq hS hT t h ht φ) ↔
      Equipollent φ (splitTorusIsogenyNormalizerMap q hS hT t h ht n • φ) := by
  rw [← centralIsogenyPullback_smul q hS hT t h ht hq n φ]
  exact equipollent_centralIsogenyPullback_iff q hq hS hT t h ht hφ (hφ.smul _)

end RootFunctionFamily

end Langlands.Geometry.Building
