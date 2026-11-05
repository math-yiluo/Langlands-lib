import Langlands.Geometry.Building.DerivedFunctions
import Langlands.GroupScheme.Rational.DerivedNormalizerMap
import Langlands.GroupScheme.Rational.RootSubgroupMultipleInclusion

/-! # Valuation axioms under actual derived pullback -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
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
    [hpflat : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [hpsurj : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))

open RootFunctionFamily

include hpflat hpsurj in
private theorem precomp_eq_of_central_vanishing {a b : characterLattice S}
    (ha : c ≫ a = 0) (hb : c ≫ b = 0) (he : e ≫ a = e ≫ b) : a = b := by
  by_contra hne
  apply RelativeRoot.precomp_ne_zero_of_centralComplement e c (a - b)
    (by rw [Preadditive.comp_sub, ha, hb, sub_self]) (sub_ne_zero.mpr hne)
  rw [Preadditive.comp_sub, he, sub_self]

include hpflat hpsurj hd h hT hS hA hc in
/-- Actual root membership is preserved and reflected on characters trivial
on the supplied central complement. -/
theorem derivedRoot_mem_iff_of_central_vanishing (a : characterLattice S)
    (ha : c ≫ a = 0) :
    e ≫ a ∈ relativeRoots j ↔ a ∈ relativeRoots i := by
  constructor
  · intro hea
    obtain ⟨b, hb, hba⟩ :=
      RelativeRoot.exists_relativeRoot_precomp_eq_derived e j i d hd h hT hS hea
    have hab : a = b := precomp_eq_of_central_vanishing e c ha
      (root_restrict_eq_zero_of_isCentral i c hA hc hb) hba.symm
    exact hab.symm ▸ hb
  · exact RelativeRoot.mem_relativeRoots_precomp_derived e c j i d hd h hT hS hA hc

/-- On any centrally trivial ambient character, normalized pullback evaluates
by the literal derived map, including outside the root support. -/
theorem RootFunctionFamily.derivedPullback_apply_character
    {φ : RootFunctionFamily S G} (hφ : IsNormalized i φ)
    (a : characterLattice S) (ha : c ≫ a = 0)
    (g : rationalPoints D) (hg : g ∈ rootGroupPoints j (e ≫ a)) :
    derivedPullback e c j i d hd h hT hS hA hc φ (e ≫ a) g =
      φ a (rationalPoints.map d g) := by
  by_cases har : a ∈ relativeRoots i
  · exact derivedPullback_apply_root e c j i d hd h hT hS hA hc φ ⟨a, har⟩ g hg
  · rw [(derivedPullback_isNormalized e c j i d hd h hT hS hA hc φ).1 _
      (fun hr => har ((derivedRoot_mem_iff_of_central_vanishing
        e c j i d hd h hT hS hA hc a ha).mp hr)) g,
      hφ.1 a har]

/-- Actual corresponding root groups have exactly the same value image. -/
theorem image_derivedPullback_root (φ : RootFunctionFamily S G)
    (a : relativeRoots i) :
    derivedPullback e c j i d hd h hT hS hA hc φ (e ≫ a.val) ''
        (rootGroupPoints j (e ≫ a.val) : Set (rationalPoints D)) =
      φ a.val '' (rootGroupPoints i a.val : Set (rationalPoints G)) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨rationalPoints.map d g,
      (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a ⟨g, hg⟩).property,
      (derivedPullback_apply_root e c j i d hd h hT hS hA hc φ a g hg).symm⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨g', hg'⟩ :=
      (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a).surjective ⟨g, hg⟩
    refine ⟨g'.val, g'.property, ?_⟩
    rw [derivedPullback_apply_root e c j i d hd h hT hS hA hc φ a g'.val g'.property,
      ← derivedRootGroupPointsEquiv_coe e c j i d hd h hT hS hA hc a g', hg']

variable [Mono i.hom.hom.left]

namespace IsRootDatumValuation

variable {φ : RootFunctionFamily S G} (hφ : IsRootDatumValuation i φ)

include hφ

/-- V0 is preserved by the actual root-point bijection. -/
theorem derivedPullback_three_le_encard (a : relativeRoots i) :
    3 ≤ (derivedPullback e c j i d hd h hT hS hA hc φ (e ≫ a.val) ''
      (rootGroupPoints j (e ≫ a.val) : Set (rationalPoints D))).encard := by
  rw [image_derivedPullback_root]
  exact hφ.three_le_encard a.val a.property

/-- V1: the pulled-back filtration contains the identity. -/
theorem derivedPullback_one_mem (a : relativeRoots i) (r : ℝ) :
    (1 : rationalPoints D) ∈
      rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ) (e ≫ a.val) r := by
  apply (rootFiltration_derivedPullback_iff e c j i d hd h hT hS hA hc φ a r 1).mpr
  exact ⟨(rootGroupPoints j _).one_mem, by simpa only [map_one] using hφ.one_mem _ a.property r⟩

/-- V1: the pulled-back filtration is closed under products. -/
theorem derivedPullback_mul_mem (a : relativeRoots i) (r : ℝ)
    (g g' : rationalPoints D)
    (hg : g ∈ rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ) (e ≫ a.val) r)
    (hg' : g' ∈ rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ) (e ≫ a.val) r) :
    g * g' ∈ rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ) (e ≫ a.val) r := by
  have hgq := (rootFiltration_derivedPullback_iff e c j i d hd h hT hS hA hc φ a r g).mp hg
  have hgq' := (rootFiltration_derivedPullback_iff e c j i d hd h hT hS hA hc φ a r g').mp hg'
  apply (rootFiltration_derivedPullback_iff e c j i d hd h hT hS hA hc φ a r (g * g')).mpr
  exact ⟨(rootGroupPoints j _).mul_mem hg.1 hg'.1, by
    rw [map_mul]
    exact hφ.mul_mem _ a.property r _ _ hgq.2 hgq'.2⟩

/-- V1: the pulled-back filtration is closed under inverses. -/
theorem derivedPullback_inv_mem (a : relativeRoots i) (r : ℝ) (g : rationalPoints D)
    (hg : g ∈ rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ) (e ≫ a.val) r) :
    g⁻¹ ∈ rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ) (e ≫ a.val) r := by
  have hgq := (rootFiltration_derivedPullback_iff e c j i d hd h hT hS hA hc φ a r g).mp hg
  apply (rootFiltration_derivedPullback_iff e c j i d hd h hT hS hA hc φ a r g⁻¹).mpr
  exact ⟨(rootGroupPoints j _).inv_mem hg.1, by
    rw [map_inv]
    exact hφ.inv_mem _ a.property r _ hgq.2⟩

/-- The actual pulled-back root filtration, bundled using V1. -/
def derivedPullbackRootFiltration (a : relativeRoots i) (r : ℝ) :
    Subgroup (rationalPoints D) where
  carrier := rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ) (e ≫ a.val) r
  one_mem' := hφ.derivedPullback_one_mem e c j i d hd h hT hS hA hc a r
  mul_mem' := fun hg hg' =>
    hφ.derivedPullback_mul_mem e c j i d hd h hT hS hA hc a r _ _ hg hg'
  inv_mem' := fun hg =>
    hφ.derivedPullback_inv_mem e c j i d hd h hT hS hA hc a r _ hg

/-- V1 at infinity uses injectivity of the original derived point map. -/
theorem derivedPullback_eq_top_iff (a : relativeRoots i) (g : rationalPoints D)
    (hg : g ∈ rootGroupPoints j (e ≫ a.val)) :
    derivedPullback e c j i d hd h hT hS hA hc φ (e ≫ a.val) g = ⊤ ↔ g = 1 := by
  rw [derivedPullback_apply_root e c j i d hd h hT hS hA hc φ a g hg,
    hφ.eq_top_iff a.val a.property (rationalPoints.map d g)
      (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a ⟨g, hg⟩).property]
  have he := (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a).map_eq_one_iff
    (x := ⟨g, hg⟩)
  simpa only [← Subtype.val_inj, derivedRootGroupPointsEquiv_coe,
    OneMemClass.coe_one] using he

/-- V4 uses central character vanishing and exact actual root restriction. -/
theorem derivedPullback_double (a : relativeRoots i)
    (h2a : 2 • (e ≫ a.val) ∈ relativeRoots j)
    (g : rationalPoints D) (hg : g ∈ rootGroupPoints j (2 • (e ≫ a.val))) :
    derivedPullback e c j i d hd h hT hS hA hc φ (2 • (e ≫ a.val)) g =
      2 • derivedPullback e c j i d hd h hT hS hA hc φ (e ≫ a.val) g := by
  have hz : c ≫ (2 • a.val) = 0 := by
    rw [Preadditive.comp_nsmul, root_restrict_eq_zero_of_isCentral i c hA hc a.property,
      nsmul_zero]
  have h2a' : 2 • a.val ∈ relativeRoots i := by
    apply (derivedRoot_mem_iff_of_central_vanishing e c j i d hd h hT hS hA hc _ hz).mp
    simpa only [Preadditive.comp_nsmul] using h2a
  have hg' : g ∈ rootGroupPoints j (e ≫ a.val) :=
    RelativeRoot.subgroup_nsmul_le j (e ≫ a.val) (by omega) _ hg
  have hg2 : g ∈ rootGroupPoints j (e ≫ (2 • a.val)) := by
    simpa only [Preadditive.comp_nsmul] using hg
  rw [← Preadditive.comp_nsmul,
    derivedPullback_apply_root e c j i d hd h hT hS hA hc φ ⟨2 • a.val, h2a'⟩ g hg2,
    derivedPullback_apply_root e c j i d hd h hT hS hA hc φ a g hg']
  exact hφ.double a.val a.property h2a' _
    (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc ⟨2 • a.val, h2a'⟩ ⟨g, hg2⟩).property

end IsRootDatumValuation

section Normalizer

variable [Mono j.hom.hom.left] (hi : IsMaximalSplitTorus i)

omit [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
  [IsAffineHom G.X.hom] [Smooth G.X.hom] [Mono j.hom.hom.left] in
/-- The actual normalizing automorphisms intertwine the retained-torus map. -/
theorem normalizingAut_derivedNormalizerMap_comp (n : normalizerPoints j) :
    (normalizingAut j n).hom ≫ e =
      e ≫ (normalizingAut i
        (DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc n)).hom := by
  let n' := DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc n
  have hn := isNormalizingPoint_normalizingAut j n
  have hn' := isNormalizingPoint_normalizingAut i n'
  have heq :
      CommGroupScheme.groupHom ((normalizingAut j n).hom ≫ e) ≫ i =
        CommGroupScheme.groupHom (e ≫ (normalizingAut i n').hom) ≫ i := by
    calc
      _ = (CommGroupScheme.groupHom (normalizingAut j n).hom ≫ j) ≫ d := by
        change (CommGroupScheme.groupHom (normalizingAut j n).hom ≫
          CommGroupScheme.groupHom e) ≫ i = _
        rw [Category.assoc, ← h, ← Category.assoc]
      _ = (j ≫ (D.innerIso n.val).hom) ≫ d := by rw [hn]
      _ = j ≫ d ≫ (G.innerIso (rationalPoints.map d n.val)).hom := by
        rw [Category.assoc, innerIso_hom_comp]
        rfl
      _ = CommGroupScheme.groupHom e ≫ i ≫ (G.innerIso n'.val).hom := by
        rw [← Category.assoc, h, Category.assoc]
        rfl
      _ = _ := by rw [hn']; rfl
  have heq' := congrArg (fun f => f.hom.hom.left) heq
  simp only [Grp.comp_hom_hom, Over.comp_left] at heq'
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact Over.OverMorphism.ext ((cancel_mono i.hom.hom.left).mp heq')

omit [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
  [IsAffineHom G.X.hom] [Smooth G.X.hom] in
/-- Character Weyl actions commute with actual derived character restriction. -/
theorem weylAction_precomp_derivedNormalizerMap (n : normalizerPoints j)
    (a : characterLattice S) :
    weylAction j n (e ≫ a) =
      e ≫ weylAction i
        (DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc n) a := by
  let n' := DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc n
  have he := normalizingAut_derivedNormalizerMap_comp e c j i d h hT hA hc hi n
  have hei : (normalizingAut j n).inv ≫ e = e ≫ (normalizingAut i n').inv := by
    calc
      _ = (normalizingAut j n).inv ≫
          (e ≫ (normalizingAut i n').hom) ≫ (normalizingAut i n').inv := by simp
      _ = (normalizingAut j n).inv ≫
          ((normalizingAut j n).hom ≫ e) ≫ (normalizingAut i n').inv := by rw [he]
      _ = _ := by simp
  rw [weylAction_apply, weylAction_apply, ← Category.assoc, hei, Category.assoc]

omit [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
  [IsAffineHom G.X.hom] [Smooth G.X.hom] in
/-- The original full real cocharacter actions commute with the actual
retained-torus map. -/
theorem normalizerAction_cocharacterMapReal_derived
    (n : normalizerPoints j) (v : V T) :
    normalizerAction i
        (DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc n)
        (cocharacterMapReal e v) =
      cocharacterMapReal e (normalizerAction j n v) := by
  induction v using TensorProduct.inductionOn with
  | tmul r ν =>
    simp only [cocharacterMapReal_tmul, normalizerAction_tmul]
    congr 1
    rw [Category.assoc,
      ← normalizingAut_derivedNormalizerMap_comp e c j i d h hT hA hc hi n,
      ← Category.assoc]
  | add v w hv hw => simp only [map_add, hv, hw]

include hpflat hpsurj h hT hS hA hc in
omit [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom] in
/-- A source reflection maps to the ambient reflection, including the full
real fixed hyperplane and the central directions. -/
theorem realizesReflection_derivedNormalizerMap
    (a : relativeRoots i) (n : normalizerPoints j)
    (hn : RealizesReflection j (e ≫ a.val) n) :
    RealizesReflection i a.val
      (DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc n) := by
  let n' := DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc n
  have hz := root_restrict_eq_zero_of_isCentral i c hA hc a.property
  refine ⟨?_, ?_⟩
  · apply precomp_eq_of_central_vanishing e c
      (root_restrict_eq_zero_of_isCentral i c hA hc
        (weylAction_mapsTo_relativeRoots i n' a.property))
      (by rw [Preadditive.comp_neg, hz, neg_zero])
    rw [← weylAction_precomp_derivedNormalizerMap e c j i d h hT hA hc hi n a.val,
      hn.1, Preadditive.comp_neg]
  · intro v hv
    obtain ⟨w, z, rfl⟩ :=
      exists_eq_cocharacterMapReal_add_of_centralComplement e c hT hA hS v
    have hw : eval T (e ≫ a.val) w = 0 := by
      rw [map_add, eval_cocharacterMapReal, eval_cocharacterMapReal, hz,
        eval_zero_char, add_zero] at hv
      exact hv
    have hwfix : normalizerAction j n w = w := hn.2 w hw
    change normalizerAction i n' _ = _
    rw [map_add, normalizerAction_cocharacterMapReal_derived e c j i d h hT hA hc hi n w,
      hwfix, normalizerAction_cocharacterMapReal_of_central i c hc n' z]

end Normalizer

private theorem restrict_not_opposite_derived (a b : characterLattice S)
    (hab : ∀ r : ℝ, 0 < r →
      (1 : ℝ) ⊗ₜ[ℤ] (e ≫ b) ≠ -(r • (1 : ℝ) ⊗ₜ[ℤ] (e ≫ a))) :
    ∀ r : ℝ, 0 < r →
      (1 : ℝ) ⊗ₜ[ℤ] b ≠ -(r • (1 : ℝ) ⊗ₜ[ℤ] a) := by
  intro r hr he
  apply hab r hr
  let f : characterLattice S →ₗ[ℤ] characterLattice T :=
    { toFun := fun a => e ≫ a
      map_add' := fun a b => by simp only [Preadditive.comp_add]
      map_smul' := fun m a => by simp only [Preadditive.comp_zsmul, RingHom.id_apply] }
  have he' := congrArg (f.baseChange ℝ) he
  simpa only [map_neg, map_smul, LinearMap.baseChange_tmul, f,
    LinearMap.coe_mk, AddHom.coe_mk] using he'

omit [Mono i.hom.hom.left] in
private theorem image_derived_commutator_generators
    (φ : RootFunctionFamily S G) (a b : relativeRoots i) (r s : ℝ) :
    rationalPoints.map d ''
      (⋃ (p : ℕ) (m : ℕ) (_ : 0 < p) (_ : 0 < m)
        (_ : p • (e ≫ a.val) + m • (e ≫ b.val) ∈ relativeRoots j),
        rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ)
          (p • (e ≫ a.val) + m • (e ≫ b.val)) (p * r + m * s)) =
      ⋃ (p : ℕ) (m : ℕ) (_ : 0 < p) (_ : 0 < m)
        (_ : p • a.val + m • b.val ∈ relativeRoots i),
        rootFiltration i φ (p • a.val + m • b.val) (p * r + m * s) := by
  have he (p m : ℕ) :
      e ≫ (p • a.val + m • b.val) = p • (e ≫ a.val) + m • (e ≫ b.val) := by
    simp only [Preadditive.comp_add, Preadditive.comp_nsmul]
  have hz (p m : ℕ) : c ≫ (p • a.val + m • b.val) = 0 := by
    rw [Preadditive.comp_add, Preadditive.comp_nsmul, Preadditive.comp_nsmul,
      root_restrict_eq_zero_of_isCentral i c hA hc a.property,
      root_restrict_eq_zero_of_isCentral i c hA hc b.property,
      nsmul_zero, nsmul_zero, add_zero]
  ext g
  simp only [Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨x, ⟨p, m, hp, hm, hroot, hx⟩, rfl⟩
    have hroot' : p • a.val + m • b.val ∈ relativeRoots i :=
      (derivedRoot_mem_iff_of_central_vanishing e c j i d hd h hT hS hA hc _ (hz p m)).mp
        (he p m ▸ hroot)
    refine ⟨p, m, hp, hm, hroot', ?_⟩
    exact ((rootFiltration_derivedPullback_iff e c j i d hd h hT hS hA hc φ
      ⟨_, hroot'⟩ _ x).mp (he p m ▸ hx)).2
  · rintro ⟨p, m, hp, hm, hroot, hg⟩
    have hmem : g ∈ rationalPoints.map d ''
        rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ)
          (e ≫ (p • a.val + m • b.val)) (p * r + m * s) := by
      rw [image_rootFiltration_derivedPullback e c j i d hd h hT hS hA hc φ ⟨_, hroot⟩]
      exact hg
    obtain ⟨x, hx, rfl⟩ := hmem
    refine ⟨x, ⟨p, m, hp, hm, ?_, ?_⟩, rfl⟩
    · rw [← he]
      exact (derivedRoot_mem_iff_of_central_vanishing e c j i d hd h hT hS hA hc _
        (hz p m)).mpr hroot
    · simpa only [he] using hx

namespace IsRootDatumValuation

variable [Mono j.hom.hom.left] (hi : IsMaximalSplitTorus i)
    {φ : RootFunctionFamily S G} (hφ : IsRootDatumValuation i φ)

include hφ

include hi in
/-- V2 is transferred by the actual forward normalizer map and its reflection
and conjugation formulas. -/
theorem derivedPullback_reflection (a : relativeRoots i)
    (n : normalizerPoints j) (hn : RealizesReflection j (e ≫ a.val) n) :
    ∃ r : ℝ, ∀ g ∈ rootGroupPoints j (e ≫ a.val), g ≠ 1 →
      derivedPullback e c j i d hd h hT hS hA hc φ (e ≫ a.val) g =
        derivedPullback e c j i d hd h hT hS hA hc φ (-(e ≫ a.val))
          ((n : rationalPoints D) * g * (n : rationalPoints D)⁻¹) + (r : WithTop ℝ) := by
  let n' := DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc n
  obtain ⟨r, hr⟩ := hφ.reflection a.val a.property n'
    (realizesReflection_derivedNormalizerMap e c j i d h hT hS hA hc hi a n hn)
  have hza := root_restrict_eq_zero_of_isCentral i c hA hc a.property
  have hz : c ≫ (-a.val) = 0 := by rw [Preadditive.comp_neg, hza, neg_zero]
  refine ⟨r, fun g hg hg1 => ?_⟩
  have hcg : (n : rationalPoints D) * g * (n : rationalPoints D)⁻¹ ∈
      rootGroupPoints j (e ≫ (-a.val)) := by
    rw [Preadditive.comp_neg, ← hn.1]
    simpa only [rootGroupPoints, GroupScheme.constantPoint_self] using
      (RelativeRoot.normalizer_conj_mem_iff j (e ≫ a.val) n g).mpr hg
  rw [← Preadditive.comp_neg,
    derivedPullback_apply_root e c j i d hd h hT hS hA hc φ a g hg,
    derivedPullback_apply_character e c j i d hd h hT hS hA hc hφ.isNormalized _ hz _ hcg]
  have hgq := (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a ⟨g, hg⟩).property
  have hgq1 : rationalPoints.map d g ≠ 1 := by
    have he := (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a).map_eq_one_iff
      (x := ⟨g, hg⟩)
    simpa only [← Subtype.val_inj, derivedRootGroupPointsEquiv_coe, OneMemClass.coe_one]
      using (not_congr he).mpr (show (⟨g, hg⟩ : rootGroupPoints j (e ≫ a.val)) ≠ 1 by
        intro heq; exact hg1 (congrArg Subtype.val heq))
  simpa only [map_mul, map_inv, n', DerivedNormalizerMap.normalizerPointsHom_coe] using
    hr (rationalPoints.map d g) hgq hgq1

omit [Mono j.hom.hom.left] in
/-- V3 reflects through the injective actual derived point map. -/
theorem derivedPullback_commutator (a b : relativeRoots i)
    (hab : ∀ r : ℝ, 0 < r →
      (1 : ℝ) ⊗ₜ[ℤ] (e ≫ b.val) ≠ -(r • (1 : ℝ) ⊗ₜ[ℤ] (e ≫ a.val)))
    (r s : ℝ) :
    ⁅Subgroup.closure
        (rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ) (e ≫ a.val) r),
      Subgroup.closure
        (rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ) (e ≫ b.val) s)⁆ ≤
      Subgroup.closure (⋃ (p : ℕ) (m : ℕ) (_ : 0 < p) (_ : 0 < m)
        (_ : p • (e ≫ a.val) + m • (e ≫ b.val) ∈ relativeRoots j),
        rootFiltration j (derivedPullback e c j i d hd h hT hS hA hc φ)
          (p • (e ≫ a.val) + m • (e ≫ b.val)) (p * r + m * s)) := by
  let ψ := derivedPullback e c j i d hd h hT hS hA hc φ
  let U := Subgroup.closure (rootFiltration j ψ (e ≫ a.val) r)
  let V := Subgroup.closure (rootFiltration j ψ (e ≫ b.val) s)
  let Z := Subgroup.closure (⋃ (p : ℕ) (m : ℕ) (_ : 0 < p) (_ : 0 < m)
    (_ : p • (e ≫ a.val) + m • (e ≫ b.val) ∈ relativeRoots j),
    rootFiltration j ψ (p • (e ≫ a.val) + m • (e ≫ b.val)) (p * r + m * s))
  have hmap : (⁅U, V⁆).map (rationalPoints.map d) ≤ Z.map (rationalPoints.map d) := by
    change (⁅Subgroup.closure (rootFiltration j ψ (e ≫ a.val) r),
        Subgroup.closure (rootFiltration j ψ (e ≫ b.val) s)⁆).map _ ≤
      (Subgroup.closure _).map _
    rw [Subgroup.map_commutator, MonoidHom.map_closure, MonoidHom.map_closure,
      MonoidHom.map_closure,
      image_rootFiltration_derivedPullback e c j i d hd h hT hS hA hc φ a r,
      image_rootFiltration_derivedPullback e c j i d hd h hT hS hA hc φ b s,
      image_derived_commutator_generators e c j i d hd h hT hS hA hc φ a b r s]
    exact hφ.commutator a.val a.property b.val b.property
      (restrict_not_opposite_derived e a.val b.val hab) r s
  have hinj : Function.Injective (rationalPoints.map d) := by
    have : Mono d.hom.hom := hd.isRepresentedBy.1
    intro x y hxy
    exact (cancel_mono d.hom.hom).mp hxy
  intro x hx
  have hxq : rationalPoints.map d x ∈ Z.map (rationalPoints.map d) :=
    hmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  obtain ⟨y, hy, hyq⟩ := hxq
  exact (hinj hyq) ▸ hy

include hi in
omit [Mono j.hom.hom.left] in
/-- V5 maps the actual opposite-root factors and their normalizer element. -/
theorem derivedPullback_opposite (a : relativeRoots i)
    (g : rationalPoints D) (hg : g ∈ rootGroupPoints j (e ≫ a.val)) (hg1 : g ≠ 1)
    (g' : rationalPoints D) (hg' : g' ∈ rootGroupPoints j (-(e ≫ a.val)))
    (g'' : rationalPoints D) (hg'' : g'' ∈ rootGroupPoints j (-(e ≫ a.val)))
    (hn : g' * g * g'' ∈ normalizerPoints j) :
    derivedPullback e c j i d hd h hT hS hA hc φ (-(e ≫ a.val)) g' +
      derivedPullback e c j i d hd h hT hS hA hc φ (e ≫ a.val) g = 0 := by
  have hnq :=
    (DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc
      ⟨g' * g * g'', hn⟩).property
  have hza := root_restrict_eq_zero_of_isCentral i c hA hc a.property
  have hz : c ≫ (-a.val) = 0 := by rw [Preadditive.comp_neg, hza, neg_zero]
  have hneg (g0 : rationalPoints D) (hg0 : g0 ∈ rootGroupPoints j (-(e ≫ a.val))) :
      rationalPoints.map d g0 ∈ rootGroupPoints i (-a.val) := by
    let f := RelativeRoot.derivedRootPointsEquiv e c j i d hd h hT hc (-a.val)
      hz (neg_ne_zero.mpr a.property.1) hS (Over.mk (𝟙 _))
    exact (f ⟨g0, by simpa only [rootGroupPoints, Preadditive.comp_neg] using hg0⟩).property
  rw [← Preadditive.comp_neg,
    derivedPullback_apply_character e c j i d hd h hT hS hA hc hφ.isNormalized _ hz _
      (by simpa only [Preadditive.comp_neg] using hg'),
    derivedPullback_apply_root e c j i d hd h hT hS hA hc φ a g hg]
  have hgq1 : rationalPoints.map d g ≠ 1 := by
    have : Mono d.hom.hom := hd.isRepresentedBy.1
    intro heq
    apply hg1
    apply (cancel_mono d.hom.hom).mp
    simpa only [rationalPoints.map_apply, MonObj.one_comp] using heq
  exact hφ.opposite a.val a.property (rationalPoints.map d g)
    (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a ⟨g, hg⟩).property
    hgq1 _ (hneg g' hg') _ (hneg g'' hg'') (by
      simpa only [DerivedNormalizerMap.normalizerPointsHom_coe, map_mul] using hnq)

include hi in
/-- The normalized pullback through the actual derived inclusion satisfies
all axioms V0–V5 of the original valuation predicate. -/
theorem derivedPullback_isRootDatumValuation :
    IsRootDatumValuation j (derivedPullback e c j i d hd h hT hS hA hc φ) := by
  have hlift (b : characterLattice T) (hb : b ∈ relativeRoots j) :
      ∃ a : relativeRoots i, e ≫ a.val = b := by
    obtain ⟨a, ha, he⟩ :=
      RelativeRoot.exists_relativeRoot_precomp_eq_derived e j i d hd h hT hS hb
    exact ⟨⟨a, ha⟩, he⟩
  have hn := derivedPullback_isNormalized e c j i d hd h hT hS hA hc φ
  refine
    { eq_top_of_not_mem_roots := hn.1
      eq_top_of_not_mem := hn.2
      three_le_encard := ?_
      one_mem := ?_
      mul_mem := ?_
      inv_mem := ?_
      eq_top_iff := ?_
      reflection := ?_
      commutator := ?_
      double := ?_
      opposite := ?_ } <;> intros
  · rename_i b hb
    obtain ⟨a, rfl⟩ := hlift b hb
    exact hφ.derivedPullback_three_le_encard e c j i d hd h hT hS hA hc a
  · rename_i b hb r
    obtain ⟨a, rfl⟩ := hlift b hb
    exact hφ.derivedPullback_one_mem e c j i d hd h hT hS hA hc a r
  · rename_i b hb r g g' hg hg'
    obtain ⟨a, rfl⟩ := hlift b hb
    exact hφ.derivedPullback_mul_mem e c j i d hd h hT hS hA hc a r g g' hg hg'
  · rename_i b hb r g hg
    obtain ⟨a, rfl⟩ := hlift b hb
    exact hφ.derivedPullback_inv_mem e c j i d hd h hT hS hA hc a r g hg
  · rename_i b hb g hg
    obtain ⟨a, rfl⟩ := hlift b hb
    exact hφ.derivedPullback_eq_top_iff e c j i d hd h hT hS hA hc a g hg
  · rename_i b hb n hn
    obtain ⟨a, rfl⟩ := hlift b hb
    exact hφ.derivedPullback_reflection e c j i d hd h hT hS hA hc hi a n hn
  · rename_i b hb b' hb' hbb' r s
    obtain ⟨a, rfl⟩ := hlift b hb
    obtain ⟨a', rfl⟩ := hlift b' hb'
    exact hφ.derivedPullback_commutator e c j i d hd h hT hS hA hc a a' hbb' r s
  · rename_i b hb h2b g hg
    obtain ⟨a, rfl⟩ := hlift b hb
    exact hφ.derivedPullback_double e c j i d hd h hT hS hA hc a h2b g hg
  · rename_i b hb g hg hg1 g' hg' g'' hg'' hn
    obtain ⟨a, rfl⟩ := hlift b hb
    exact hφ.derivedPullback_opposite e c j i d hd h hT hS hA hc hi a
      g hg hg1 g' hg' g'' hg'' hn

end IsRootDatumValuation

variable [Mono j.hom.hom.left] (hi : IsMaximalSplitTorus i)

/-- Pull back an actual valuation through the original derived inclusion
under the supplied structural torus product. -/
def derivedValuationPullback
    (φ : {φ : RootFunctionFamily S G // IsRootDatumValuation i φ}) :
    {ψ : RootFunctionFamily T D // IsRootDatumValuation j ψ} :=
  ⟨derivedPullback e c j i d hd h hT hS hA hc φ.val,
    φ.property.derivedPullback_isRootDatumValuation e c j i d hd h hT hS hA hc hi⟩

@[simp]
theorem derivedValuationPullback_val
    (φ : {φ : RootFunctionFamily S G // IsRootDatumValuation i φ}) :
    (derivedValuationPullback e c j i d hd h hT hS hA hc hi φ).val =
      derivedPullback e c j i d hd h hT hS hA hc φ.val := rfl

end Langlands.Geometry.Building
