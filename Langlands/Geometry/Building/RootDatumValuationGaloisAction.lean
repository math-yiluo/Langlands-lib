import Langlands.Geometry.Building.RootFunctionGaloisAction
import Langlands.GroupScheme.Rational.NormalizerGaloisAction

/-! # Coefficient actions on actual root-datum valuations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme

section Descent

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
  (T : CommGroupScheme B)

/-- Postcomposition commutes with the explicit descended group homomorphism. -/
theorem transportCocharacter_descentPostcomp (H : GroupScheme B)
    (f : (GroupScheme.baseChange b).obj H ⟶ (GroupScheme.baseChange b).obj H)
    (ν : (Gm S).toGrp ⟶ (GroupScheme.baseChange b).obj H) :
    transportCocharacter b a ha H ν ≫
        (descentBaseChangeIso b a ha H).inv ≫
          (GroupScheme.baseChange a).map f ≫ (descentBaseChangeIso b a ha H).hom =
      transportCocharacter b a ha H (ν ≫ f) := by
  simp only [transportCocharacter, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Cocharacter transport intertwines the explicit descended automorphism. -/
theorem cocharacterLattice.transport_descentPostcomp
    (τ : (CommGroupScheme.baseChange b).obj T ≅ (CommGroupScheme.baseChange b).obj T)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) :
    cocharacterLattice.transport b a ha T ν ≫
        ((CommGroupScheme.descentBaseChangeIso b a ha T).symm ≪≫
          (CommGroupScheme.baseChange a).mapIso τ ≪≫
          CommGroupScheme.descentBaseChangeIso b a ha T).hom =
      cocharacterLattice.transport b a ha T (ν ≫ τ.hom) := by
  apply CommGroupScheme.hom_ext_points
  intro U x
  rw [comp_groupHom_comp, cocharacterLattice.groupHom_transport,
    cocharacterLattice.groupHom_transport]
  have h := transportCocharacter_descentPostcomp b a ha T.toGrp
    (CommGroupScheme.groupHom τ.hom) (CommGroupScheme.groupHom ν)
  exact congrArg (fun f => x ≫ f.hom.hom) h

end Descent

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

variable [Mono (CategoryTheory.Functor.map
  (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]

/-- Actual coefficient transport intertwines normalizer actions on real cocharacters. -/
theorem normalizerAction_galoisCocharacterAction (σ : K ≃ₐ[k] K)
    (n : normalizerPoints (T := T_K) i_K) (v : V T_K) :
    normalizerAction (T := T_K) i_K (normalizerGaloisAction k K i σ n)
        (galoisCocharacterAction k K T σ v) =
      galoisCocharacterAction k K T σ (normalizerAction (T := T_K) i_K n v) := by
  have hn : normalizingAut (T := T_K) i_K (normalizerGaloisAction k K i σ n) =
      torusAutGaloisTransport k K σ (normalizingAut (T := T_K) i_K n) :=
    (isNormalizingPoint_normalizingAut (T := T_K) i_K _).unique (T := T_K) i_K
      ((isNormalizingPoint_normalizingAut (T := T_K) i_K n).rationalConjugate k K i σ)
  induction v using TensorProduct.inductionOn with
  | tmul r ν =>
    rw [galoisCocharacterAction_tmul, normalizerAction_tmul, normalizerAction_tmul,
      galoisCocharacterAction_tmul, hn]
    exact congrArg (fun z => r ⊗ₜ[ℤ] z)
      (cocharacterLattice.transport_descentPostcomp b (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) T (normalizingAut (T := T_K) i_K n) ν)
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The actual conjugate normalizer point realizes the conjugate reflection. -/
theorem RealizesReflection.galoisTransport (σ : K ≃ₐ[k] K)
    {a : characterLattice T_K} {n : normalizerPoints (T := T_K) i_K}
    (hn : RealizesReflection (S := T_K) i_K a n) :
    RealizesReflection (S := T_K) i_K
      (characterLattice.galoisRepresentation k K T σ a)
      (normalizerGaloisAction k K i σ n) := by
  refine ⟨?_, ?_⟩
  · rw [weylAction_normalizerGaloisAction, hn.1, map_neg]
  · intro v hv
    obtain ⟨w, rfl⟩ := (galoisCocharacterAction k K T σ).surjective v
    have hw : eval T_K a w = 0 := by
      simpa only [eval_galoisCocharacterAction] using hv
    change normalizerAction (T := T_K) i_K _ _ = _
    rw [normalizerAction_galoisCocharacterAction]
    exact congrArg (galoisCocharacterAction k K T σ) (hn.2 w hw)

variable [IsAffineHom G.X.hom]

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

local notation "charAct" => characterLattice.galoisRepresentation k K T
local notation "pointAct" => rationalConjugate k K G

omit [Mono (CategoryTheory.Functor.map
  (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left] [IsAffineHom G.X.hom] in
/-- Coefficient conjugation maps each actual root group onto the conjugate root group. -/
theorem image_rootGroupPoints_galois (σ : K ≃ₐ[k] K) (a : characterLattice T_K) :
    pointAct σ '' (rootGroupPoints (S := T_K) i_K a : Set (rationalPoints G_K)) =
      rootGroupPoints (S := T_K) i_K (charAct σ a) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ a h).2 hh
  · intro hg
    refine ⟨pointAct σ⁻¹ g, ?_, ?_⟩
    · apply (RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ a
        (pointAct σ⁻¹ g)).1
      have h : pointAct σ (pointAct σ⁻¹ g) ∈
          rootGroupPoints (S := T_K) i_K (charAct σ a) := by
        rw [← rationalConjugate_mul, mul_inv_cancel, rationalConjugate_one]
        exact hg
      exact h
    · rw [← rationalConjugate_mul, mul_inv_cancel, rationalConjugate_one]

/-- All normalization conditions and axioms V0--V5 are preserved by actual
coefficient transport, including the full generated-subgroup commutator condition. -/
theorem IsRootDatumValuation.galoisTransport (σ : K ≃ₐ[k] K)
    {φ : RootFunctionFamily T_K G_K}
    (hφ : IsRootDatumValuation (S := T_K) i_K φ) :
    IsRootDatumValuation (S := T_K) i_K
      (RootFunctionFamily.galoisAction k K T G σ φ) where
  eq_top_of_not_mem_roots a ha g := by
    apply hφ.eq_top_of_not_mem_roots
    exact fun h => ha ((mem_roots_galois_iff k K i σ⁻¹ a).1 h)
  eq_top_of_not_mem a ha g hg := by
    apply hφ.eq_top_of_not_mem _ ((mem_roots_galois_iff k K i σ⁻¹ a).2 ha)
    exact fun h => hg ((RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ⁻¹ a g).1 h)
  three_le_encard a ha := by
    have himage :
        RootFunctionFamily.galoisAction k K T G σ φ a ''
            (rootGroupPoints (S := T_K) i_K a : Set (rationalPoints G_K)) =
          φ (charAct σ⁻¹ a) ''
            (rootGroupPoints (S := T_K) i_K (charAct σ⁻¹ a) :
              Set (rationalPoints G_K)) := by
      rw [← image_rootGroupPoints_galois k K i σ⁻¹ a, Set.image_image]
      rfl
    rw [himage]
    exact hφ.three_le_encard _ ((mem_roots_galois_iff k K i σ⁻¹ a).2 ha)
  one_mem a ha r := by
    have h := (rationalConjugate_mem_rootFiltration_iff k K i σ
      φ (charAct σ⁻¹ a) r 1).2
      (hφ.one_mem _ ((mem_roots_galois_iff k K i σ⁻¹ a).2 ha) r)
    simpa only [Representation.self_inv_apply, map_one] using h
  mul_mem a ha r g h hg hh := by
    have hg' : pointAct σ⁻¹ g ∈ rootFiltration (S := T_K) i_K φ (charAct σ⁻¹ a) r := by
      simpa only [Representation.self_inv_apply, ← rationalConjugate_mul,
        mul_inv_cancel, rationalConjugate_one] using
        (rationalConjugate_mem_rootFiltration_iff k K i σ φ (charAct σ⁻¹ a) r
          (pointAct σ⁻¹ g)).1 (by simpa only [Representation.self_inv_apply,
            ← rationalConjugate_mul, mul_inv_cancel, rationalConjugate_one] using hg)
    have hh' : pointAct σ⁻¹ h ∈ rootFiltration (S := T_K) i_K φ (charAct σ⁻¹ a) r := by
      exact ⟨(RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ⁻¹ a h).2 hh.1, hh.2⟩
    exact ⟨(RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ⁻¹ a (g * h)).1
      (by simpa only [map_mul, rootGroupPoints] using
        (hφ.mul_mem _ ((mem_roots_galois_iff k K i σ⁻¹ a).2 ha) r _ _ hg' hh').1),
      by simpa only [RootFunctionFamily.galoisAction_apply, map_mul] using
        (hφ.mul_mem _ ((mem_roots_galois_iff k K i σ⁻¹ a).2 ha) r _ _ hg' hh').2⟩
  inv_mem a ha r g hg := by
    have hg' : pointAct σ⁻¹ g ∈ rootFiltration (S := T_K) i_K φ (charAct σ⁻¹ a) r :=
      ⟨(RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ⁻¹ a g).2 hg.1, hg.2⟩
    have h := hφ.inv_mem _ ((mem_roots_galois_iff k K i σ⁻¹ a).2 ha) r _ hg'
    exact ⟨(RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ⁻¹ a g⁻¹).1
      (by simpa only [map_inv, rootGroupPoints] using h.1),
      by simpa only [RootFunctionFamily.galoisAction_apply, map_inv] using h.2⟩
  eq_top_iff a ha g hg := by
    change φ (charAct σ⁻¹ a) (pointAct σ⁻¹ g) = ⊤ ↔ g = 1
    rw [hφ.eq_top_iff _ ((mem_roots_galois_iff k K i σ⁻¹ a).2 ha) _
      ((RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ⁻¹ a g).2 hg)]
    exact (pointAct σ⁻¹).map_eq_one_iff
  reflection a ha n hn := by
    have hn' := hn.galoisTransport k K i σ⁻¹
    obtain ⟨c, hc⟩ := hφ.reflection _ ((mem_roots_galois_iff k K i σ⁻¹ a).2 ha)
      (normalizerGaloisAction k K i σ⁻¹ n) hn'
    refine ⟨c, fun g hg hg1 => ?_⟩
    have hg1' : pointAct σ⁻¹ g ≠ 1 :=
      fun h => hg1 ((pointAct σ⁻¹).map_eq_one_iff.1 h)
    have h := hc (pointAct σ⁻¹ g)
      ((RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ⁻¹ a g).2 hg) hg1'
    simp only [normalizerGaloisAction_coe] at h
    simpa only [RootFunctionFamily.galoisAction_apply, map_neg, map_mul, map_inv] using h
  commutator a ha a' ha' haa' r s := by
    have haa0 : ∀ t : ℝ, 0 < t →
        ((1 : ℝ) ⊗ₜ[ℤ] (charAct σ⁻¹ a') : Vstar T_K) ≠
          -(t • (1 : ℝ) ⊗ₜ[ℤ] (charAct σ⁻¹ a)) := by
      intro t ht heq
      apply haa' t ht
      have h := congrArg
        (LinearEquiv.baseChange ℤ ℝ _ _ (characterLattice.galoisEquiv k K T σ)) heq
      simp only [map_neg, map_smul, LinearEquiv.baseChange_tmul] at h
      change ((1 : ℝ) ⊗ₜ[ℤ] (charAct σ (charAct σ⁻¹ a')) : Vstar T_K) =
        -(t • (1 : ℝ) ⊗ₜ[ℤ] (charAct σ (charAct σ⁻¹ a))) at h
      simpa only [Representation.self_inv_apply] using h
    have h := Subgroup.map_mono (f := (pointAct σ).toMonoidHom)
      (hφ.commutator _ ((mem_roots_galois_iff k K i σ⁻¹ a).2 ha)
        _ ((mem_roots_galois_iff k K i σ⁻¹ a').2 ha') haa0 r s)
    have hclosure (χ : characterLattice T_K) (t : ℝ) :
        (Subgroup.closure (rootFiltration (S := T_K) i_K φ (charAct σ⁻¹ χ) t)).map
            (pointAct σ).toMonoidHom =
          Subgroup.closure (rootFiltration (S := T_K) i_K
            (RootFunctionFamily.galoisAction k K T G σ φ) χ t) := by
      rw [MonoidHom.map_closure]
      apply congrArg Subgroup.closure
      have h := image_rootFiltration_galoisAction k K i σ φ (charAct σ⁻¹ χ) t
      rw [Representation.self_inv_apply] at h
      exact h
    rw [Subgroup.map_commutator, hclosure, hclosure] at h
    refine h.trans ?_
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨g, hg, rfl⟩
    simp only [Set.mem_iUnion] at hg ⊢
    obtain ⟨p, q, hp, hq, hroot, hg⟩ := hg
    have hroot' : p • a + q • a' ∈ relativeRoots (T := T_K) i_K := by
      have h := (mem_roots_galois_iff k K i σ
        (p • charAct σ⁻¹ a + q • charAct σ⁻¹ a')).2 hroot
      simpa only [relativeRoots, map_add, map_nsmul, Representation.self_inv_apply] using h
    refine ⟨p, q, hp, hq, hroot', ?_⟩
    have h := (rationalConjugate_mem_rootFiltration_iff k K i σ φ
      (p • charAct σ⁻¹ a + q • charAct σ⁻¹ a') (p * r + q * s) g).2 hg
    simp only [map_add, map_nsmul, Representation.self_inv_apply] at h
    exact h
  double a ha h2a g hg := by
    have h2a' : 2 • charAct σ⁻¹ a ∈ relativeRoots (T := T_K) i_K := by
      simpa only [relativeRoots, map_nsmul] using
        (mem_roots_galois_iff k K i σ⁻¹ (2 • a)).2 h2a
    have hg' : pointAct σ⁻¹ g ∈ rootGroupPoints (S := T_K) i_K (2 • charAct σ⁻¹ a) := by
      simpa only [rootGroupPoints, map_nsmul] using
        (RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ⁻¹ (2 • a) g).2 hg
    simpa only [RootFunctionFamily.galoisAction_apply, map_nsmul] using
      hφ.double _ ((mem_roots_galois_iff k K i σ⁻¹ a).2 ha) h2a' _ hg'
  opposite a ha g hg hg1 g' hg' g'' hg'' hn := by
    have hg1' : pointAct σ⁻¹ g ≠ 1 :=
      fun h => hg1 ((pointAct σ⁻¹).map_eq_one_iff.1 h)
    have hneg (v : rationalPoints G_K)
        (hv : v ∈ rootGroupPoints (S := T_K) i_K (-a)) :
        pointAct σ⁻¹ v ∈ rootGroupPoints (S := T_K) i_K (-(charAct σ⁻¹ a)) := by
      simpa only [rootGroupPoints, map_neg] using
        (RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ⁻¹ (-a) v).2 hv
    have hn' : pointAct σ⁻¹ g' * pointAct σ⁻¹ g * pointAct σ⁻¹ g'' ∈
        normalizerPoints (T := T_K) i_K := by
      simpa only [map_mul] using rationalConjugate_mem_normalizerPoints k K i σ⁻¹ hn
    simpa only [RootFunctionFamily.galoisAction_apply, map_neg] using
      hφ.opposite _ ((mem_roots_galois_iff k K i σ⁻¹ a).2 ha)
        _ ((RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ⁻¹ a g).2 hg)
        hg1' _ (hneg g' hg') _ (hneg g'' hg'') hn'

/-- Coefficient transport also reflects the actual V0--V5 valuation predicate. -/
theorem isRootDatumValuation_galoisAction_iff (σ : K ≃ₐ[k] K)
    (φ : RootFunctionFamily T_K G_K) :
    IsRootDatumValuation (S := T_K) i_K
        (RootFunctionFamily.galoisAction k K T G σ φ) ↔
      IsRootDatumValuation (S := T_K) i_K φ := by
  constructor
  · intro h
    have h' := h.galoisTransport k K i σ⁻¹
    change IsRootDatumValuation (S := T_K) i_K
      ((RootFunctionFamily.galoisAction k K T G σ⁻¹ *
        RootFunctionFamily.galoisAction k K T G σ) φ) at h'
    rw [← map_mul, inv_mul_cancel, map_one] at h'
    exact h'
  · exact fun h => h.galoisTransport k K i σ

namespace IsRootDatumValuation

/-- The actual coefficient action on all V0--V5 valuations of the descended map.
No nonempty class or existence of a valuation is assumed. -/
def galoisAction : (K ≃ₐ[k] K) →*
    Equiv.Perm {φ : RootFunctionFamily T_K G_K //
      IsRootDatumValuation (S := T_K) i_K φ} where
  toFun σ :=
    { toFun φ := ⟨RootFunctionFamily.galoisAction k K T G σ φ.val,
        φ.property.galoisTransport k K i σ⟩
      invFun φ := ⟨RootFunctionFamily.galoisAction k K T G σ⁻¹ φ.val,
        φ.property.galoisTransport k K i σ⁻¹⟩
      left_inv φ := by
        apply Subtype.ext
        change (RootFunctionFamily.galoisAction k K T G σ⁻¹ *
          RootFunctionFamily.galoisAction k K T G σ) φ.val = φ.val
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv φ := by
        apply Subtype.ext
        change (RootFunctionFamily.galoisAction k K T G σ *
          RootFunctionFamily.galoisAction k K T G σ⁻¹) φ.val = φ.val
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by
    apply Equiv.ext
    intro φ
    apply Subtype.ext
    change RootFunctionFamily.galoisAction k K T G 1 φ.val = φ.val
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply Equiv.ext
    intro φ
    apply Subtype.ext
    change RootFunctionFamily.galoisAction k K T G (σ * τ) φ.val =
      (RootFunctionFamily.galoisAction k K T G σ *
        RootFunctionFamily.galoisAction k K T G τ) φ.val
    rw [map_mul]

@[simp] theorem galoisAction_val (σ : K ≃ₐ[k] K)
    (φ : {φ : RootFunctionFamily T_K G_K //
      IsRootDatumValuation (S := T_K) i_K φ}) :
    (galoisAction k K i σ φ).val = RootFunctionFamily.galoisAction k K T G σ φ.val := rfl

end IsRootDatumValuation

end Langlands.Geometry.Building
