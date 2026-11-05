import Langlands.Geometry.Building.DerivedFunctions
import Langlands.Geometry.Building.CentralIsogenyFunctionsAction
import Langlands.GroupScheme.Rational.CentralComplementNormalizer

/-! # Actual normalizer equivariance of derived root-function pullback -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

section Normalizers

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    {j : T.toGrp ⟶ D} {i : S.toGrp ⟶ G}
    [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (q : D ⟶ G) (hi : IsMaximalSplitTorus i) (e : T ⟶ S) (c : A ⟶ S)
    (h : j ≫ q = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hA : IsSplitTorus A.toGrp)
    [Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))

/-- The actual source and image Weyl actions commute with character restriction. -/
theorem weylAction_centralComplementNormalizerMap
    (n : normalizerPoints j) (a : characterLattice S) :
    e ≫ weylAction i
        (CentralComplementNormalizer.normalizerPointsMap q j i hi e c h hT hA hc n) a =
      weylAction j n (e ≫ a) := by
  rw [weylAction_apply, weylAction_apply, ← Category.assoc]
  have he := congrArg
    (fun f => (normalizingAut j n).inv ≫ f ≫
      (normalizingAut i
        (CentralComplementNormalizer.normalizerPointsMap q j i hi e c h hT hA hc n)).inv)
    (CentralComplementNormalizer.normalizingAut_comp q j i hi e c h hT hA hc n)
  have he' : e ≫
      (normalizingAut i
        (CentralComplementNormalizer.normalizerPointsMap q j i hi e c h hT hA hc n)).inv =
        (normalizingAut j n).inv ≫ e := by
    simpa [Category.assoc] using he
  exact congrArg (fun f : T ⟶ S => f ≫ a) he'

/-- The original real cocharacter map intertwines the two actual normalizer actions. -/
theorem cocharacterMapReal_centralComplementNormalizerMap
    (n : normalizerPoints j) (v : V T) :
    cocharacterMapReal e (normalizerAction j n v) =
      normalizerAction i
        (CentralComplementNormalizer.normalizerPointsMap q j i hi e c h hT hA hc n)
        (cocharacterMapReal e v) := by
  induction v using TensorProduct.inductionOn with
  | tmul r ν =>
    simp only [normalizerAction_tmul, cocharacterMapReal_tmul, Category.assoc,
      CentralComplementNormalizer.normalizingAut_comp q j i hi e c h hT hA hc n]
  | add v w hv hw => simp only [map_add, hv, hw]

variable [LocallyOfFiniteType G.X.hom]

/-- A source reflection along a restricted actual root maps to the ambient
reflection. The central factor supplies the missing full-space directions. -/
theorem realizesReflection_centralComplementNormalizerMap
    (a : relativeRoots i) (n : normalizerPoints j)
    (hn : RealizesReflection j (e ≫ a.val) n) :
    RealizesReflection i a.val
      (CentralComplementNormalizer.normalizerPointsMap q j i hi e c h hT hA hc n) := by
  let n' := CentralComplementNormalizer.normalizerPointsMap q j i hi e c h hT hA hc n
  have hz : c ≫ a.val = 0 := root_restrict_eq_zero_of_isCentral i c hA hc a.property
  constructor
  · by_contra hne
    have hzw : c ≫ weylAction i n' a.val = 0 :=
      root_restrict_eq_zero_of_isCentral i c hA hc
        (weylAction_mapsTo_relativeRoots i n' a.property)
    have hzδ : c ≫ (weylAction i n' a.val - (-a.val)) = 0 := by
      rw [Preadditive.comp_sub, hzw, Preadditive.comp_neg, hz, neg_zero, sub_self]
    apply RelativeRoot.precomp_ne_zero_of_centralComplement e c
      (weylAction i n' a.val - (-a.val)) hzδ (sub_ne_zero.mpr hne)
    rw [Preadditive.comp_sub, weylAction_centralComplementNormalizerMap,
      hn.1, Preadditive.comp_neg, sub_self]
  · intro v hv
    have hvspan : v ∈ (cocharacterMapReal e).range ⊔ (cocharacterMapReal c).range := by
      rw [cocharacterRange_sup_eq_top_of_centralComplement e c hT hA hi.1.1]
      trivial
    obtain ⟨x, ⟨xT, rfl⟩, z, ⟨zA, rfl⟩, hvspan⟩ := Submodule.mem_sup.mp hvspan
    have hz0 : eval S a.val (cocharacterMapReal c zA) = 0 := by
      rw [eval_cocharacterMapReal, hz]
      simp only [eval_eq_pair, TensorProduct.tmul_zero, map_zero, LinearMap.zero_apply]
    rw [← hvspan, map_add, hz0, add_zero, eval_cocharacterMapReal] at hv
    have hfix : normalizerAction j n xT = xT := hn.2 xT hv
    change normalizerAction i n' v = v
    rw [← hvspan, map_add, normalizerAction_cocharacterMapReal_of_central i c hc n',
      ← cocharacterMapReal_centralComplementNormalizerMap q hi e c h hT hA hc n xT, hfix]

end Normalizers

section Derived

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    [Mono j.hom.hom.left] [Mono i.hom.hom.left]
    (d : D ⟶ G) (hd : IsDerivedSubgroup d)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (hA : IsSplitTorus A.toGrp)
    [Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))
    (hi : IsMaximalSplitTorus i)

/-- The actual reduced translation equivalence intertwines the original
normalizer derivatives. -/
theorem derivedTranslationEquiv_translationAction
    (n : normalizerPoints j) (v : TranslationSpace j) :
    derivedTranslationEquiv e c j i d hd h hT hS hA hc (translationAction j n v) =
      translationAction i
        (CentralComplementNormalizer.normalizerPointsMap d j i hi e c h hT hA hc n)
        (derivedTranslationEquiv e c j i d hd h hT hS hA hc v) := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  rw [translationAction_mk, derivedTranslationEquiv_mk,
    derivedTranslationEquiv_mk, translationAction_mk]
  exact congrArg Submodule.Quotient.mk
    (cocharacterMapReal_centralComplementNormalizerMap d hi e c h hT hA hc n w)

omit [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom] in
private theorem rootGroupPoints_conj_iff (n : normalizerPoints j)
    (b : characterLattice T) (g : rationalPoints D) :
    (n : rationalPoints D) * g * (n : rationalPoints D)⁻¹ ∈
      rootGroupPoints j (weylAction j n b) ↔ g ∈ rootGroupPoints j b := by
  simpa only [rootGroupPoints, GroupScheme.constantPoint_self] using
    RelativeRoot.normalizer_conj_mem_iff j b n g

namespace RootFunctionFamily

/-- Derived pullback as a map of the actual types of normalized families. -/
def derivedNormalizedPullback :
    {φ : RootFunctionFamily S G // IsNormalized i φ} →
      {ψ : RootFunctionFamily T D // IsNormalized j ψ} :=
  fun φ => ⟨derivedPullback e c j i d hd h hT hS hA hc φ.val,
    derivedPullback_isNormalized e c j i d hd h hT hS hA hc φ.val⟩

omit [Mono j.hom.hom.left] [Mono i.hom.hom.left] in
/-- The map on normalized families is injective. -/
theorem derivedNormalizedPullback_injective :
    Function.Injective (derivedNormalizedPullback e c j i d hd h hT hS hA hc) := by
  intro φ ψ he
  apply Subtype.ext
  exact derivedPullback_injective e c j i d hd h hT hS hA hc φ.property ψ.property
    (congrArg Subtype.val he)

/-- Normalized derived pullback commutes with the original normalizer actions. -/
theorem derivedPullback_smul (n : normalizerPoints j) (φ : RootFunctionFamily S G) :
    derivedPullback e c j i d hd h hT hS hA hc
        (CentralComplementNormalizer.normalizerPointsMap d j i hi e c h hT hA hc n • φ) =
      n • derivedPullback e c j i d hd h hT hS hA hc φ := by
  ext b g
  by_cases hb : b ∈ relativeRoots j
  · by_cases hg : g ∈ rootGroupPoints j b
    · let a := (RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc).symm
        ⟨b, hb⟩
      have he : e ≫ a.val = b := congrArg Subtype.val
        ((RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc).apply_symm_apply
          ⟨b, hb⟩)
      rw [← he] at hg ⊢
      let n' := CentralComplementNormalizer.normalizerPointsMap d j i hi e c h hT hA hc n
      have hw : weylAction j n⁻¹ (e ≫ a.val) = e ≫ weylAction i n'⁻¹ a.val := by
        simpa only [map_inv] using
          (weylAction_centralComplementNormalizerMap d hi e c h hT hA hc n⁻¹ a.val).symm
      have hcg : (n : rationalPoints D)⁻¹ * g * (n : rationalPoints D) ∈
          rootGroupPoints j (e ≫ weylAction i n'⁻¹ a.val) := by
        rw [← hw]
        simpa only [Subgroup.coe_inv, inv_inv] using
          (rootGroupPoints_conj_iff j n⁻¹ (e ≫ a.val) g).mpr hg
      rw [derivedPullback_apply_root e c j i d hd h hT hS hA hc _ a g hg,
        smul_apply, smul_apply, hw,
        derivedPullback_apply_root e c j i d hd h hT hS hA hc φ
          ⟨weylAction i n'⁻¹ a.val, weylAction_mapsTo_relativeRoots i n'⁻¹ a.property⟩ _ hcg]
      change φ (weylAction i n'⁻¹ a.val)
          ((n' : rationalPoints G)⁻¹ * rationalPoints.map d g * (n' : rationalPoints G)) =
        φ (weylAction i n'⁻¹ a.val)
          (rationalPoints.map d ((n : rationalPoints D)⁻¹ * g * (n : rationalPoints D)))
      simp only [map_mul, map_inv, n', CentralComplementNormalizer.normalizerPointsMap_coe]
    · have hcg : (n : rationalPoints D)⁻¹ * g * (n : rationalPoints D) ∉
          rootGroupPoints j (weylAction j n⁻¹ b) := by
        intro hcg
        exact hg ((rootGroupPoints_conj_iff j n⁻¹ b g).mp
          (by simpa only [Subgroup.coe_inv, inv_inv] using hcg))
      rw [(derivedPullback_isNormalized e c j i d hd h hT hS hA hc _).2 b hb g hg,
        smul_apply, (derivedPullback_isNormalized e c j i d hd h hT hS hA hc φ).2 _
          (weylAction_mapsTo_relativeRoots j n⁻¹ hb) _ hcg]
  · have hw : weylAction j n⁻¹ b ∉ relativeRoots j :=
      fun hw => hb ((weylAction_mem_roots_iff n⁻¹ b).mp hw)
    rw [(derivedPullback_isNormalized e c j i d hd h hT hS hA hc _).1 b hb g, smul_apply,
      (derivedPullback_isNormalized e c j i d hd h hT hS hA hc φ).1 _ hw]

/-- Preservation of an equipollence class by a normalizer is detected
after normalized derived pullback. -/
theorem equipollent_smul_derivedPullback_iff {φ : RootFunctionFamily S G}
    (hφ : IsNormalized i φ) (n : normalizerPoints j) :
    Equipollent (derivedPullback e c j i d hd h hT hS hA hc φ)
        (n • derivedPullback e c j i d hd h hT hS hA hc φ) ↔
      Equipollent φ
        (CentralComplementNormalizer.normalizerPointsMap d j i hi e c h hT hA hc n • φ) := by
  rw [← derivedPullback_smul e c j i d hd h hT hS hA hc hi n φ]
  exact equipollent_derivedPullback_iff e c j i d hd h hT hS hA hc hφ (hφ.smul _)

end RootFunctionFamily

end Derived

end Langlands.Geometry.Building
