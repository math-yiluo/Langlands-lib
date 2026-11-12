/-
The stalk argument in `ValuativeDescent.hasLift_of_specialization` is adapted
from Mathlib/AlgebraicGeometry/ValuativeCriterion.lean:
Copyright (c) 2024 Andrew Yang, Qi Ge, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE file.
Authors of the original argument: Andrew Yang, Qi Ge, Christian Merten.
-/
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeValuativeExistenceReductionStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof

/-! # Original-ring valuative existence from dominating-ring Picard-zero extension -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

noncomputable section

namespace Langlands.AbelianScheme

namespace ValuativeDescent

set_option backward.isDefEq.respectTransparency false in
/-- A specialization in the valuative fibre product above its closed point
gives a lift over the original valuation ring. This is the stalk argument of
Mathlib's `ValuativeCriterion.Existence.of_specializingMap`. -/
theorem hasLift_of_specialization {X Y : Scheme.{u}} {f : X ⟶ Y}
    (sq : ValuativeCommSq f)
    (x : (pullback sq.i₂ f : Scheme.{u}))
    (h₁ : (pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)))
      sq.i₁ sq.commSq.w.symm) (closedPoint sq.K) ⤳ x)
    (h₂ : pullback.fst sq.i₂ f x = closedPoint sq.R) :
    sq.commSq.HasLift := by
  rcases sq with ⟨R, K, i₁, i₂, ⟨w⟩⟩
  have : IsDomain (CommRingCat.of R) := ‹_›
  have : ValuationRing (CommRingCat.of R) := ‹_›
  let : Field (CommRingCat.of K) := ‹_›
  let lft := pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R K))) i₁ w.symm
  let e : CommRingCat.of R ≅ (Spec (CommRingCat.of R)).presheaf.stalk
      (pullback.fst i₂ f x) :=
    (stalkClosedPointIso (CommRingCat.of R)).symm ≪≫
      (Spec (CommRingCat.of R)).presheaf.stalkCongr (.of_eq h₂.symm)
  let α := e.hom ≫ (pullback.fst i₂ f).stalkMap x
  have : IsLocalHom e.hom.hom := isLocalHom_of_isIso e.hom
  have : IsLocalHom α.hom := inferInstanceAs
    (IsLocalHom (((pullback.fst i₂ f).stalkMap x).hom.comp e.hom.hom))
  let β := (pullback i₂ f).presheaf.stalkSpecializes h₁ ≫ Scheme.stalkClosedPointTo lft
  have hαβ : α ≫ β = CommRingCat.ofHom (algebraMap R K) := by
    simp only [CommRingCat.coe_of, Iso.trans_hom, Iso.symm_hom,
      TopCat.Presheaf.stalkCongr_hom, Category.assoc, α, e, β, stalkClosedPointIso_inv,
      StructureSheaf.toStalk]
    change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec (CommRingCat.of R)).presheaf.germ _ _ _ ≫ _ = _
    simp only [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap_assoc]
    simp only [TopologicalSpace.Opens.map_top]
    rw [Scheme.germ_stalkClosedPointTo lft ⊤ trivial]
    erw [← Scheme.Hom.comp_app_assoc lft (pullback.fst i₂ f)]
    rw [pullback.lift_fst]
    simp
  have hbij := bijective_rangeRestrict_comp_of_valuationRing (R := R) (K := K)
    α.hom β.hom (CommRingCat.hom_ext_iff.mp hαβ)
  let φ : (pullback i₂ f).presheaf.stalk x ⟶ CommRingCat.of R := CommRingCat.ofHom <|
    (RingEquiv.ofBijective _ hbij).symm.toRingHom.comp β.hom.rangeRestrict
  have hαφ : α ≫ φ = 𝟙 _ := by
    ext a
    exact (RingEquiv.ofBijective _ hbij).symm_apply_apply a
  have hαφ' : (pullback.fst i₂ f).stalkMap x ≫ φ = e.inv := by
    rw [← cancel_epi e.hom, ← Category.assoc, hαφ, e.hom_inv_id]
  have hφβ : φ ≫ CommRingCat.ofHom (algebraMap R K) = β :=
    hαβ ▸ CommRingCat.hom_ext (RingHom.ext fun a ↦ congr_arg Subtype.val
      ((RingEquiv.ofBijective _ hbij).apply_symm_apply (β.hom.rangeRestrict a)))
  refine ⟨⟨⟨Spec.map ((pullback.snd i₂ f).stalkMap x ≫ φ) ≫
    X.fromSpecStalk _, ?_, ?_⟩⟩⟩
  · simp only [← Spec.map_comp_assoc, Category.assoc, hφβ]
    simp only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, β]
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
    simp [lft]
  · simp only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← pullback.condition]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, ← Spec.map_comp_assoc, hαφ']
    simp only [Iso.trans_inv, TopCat.Presheaf.stalkCongr_inv, Iso.symm_inv, Spec.map_comp,
      Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, e]
    rw [← Spec_stalkClosedPointIso, ← Spec.map_comp_assoc,
      Iso.inv_hom_id, Spec.map_id, Category.id_comp]

/-- A lift after domination by a valuation ring produces the specialization
needed to construct a lift over the original ring. -/
theorem hasLift_of_dominatingLift {X Y : Scheme.{u}} {f : X ⟶ Y}
    (sq : ValuativeCommSq f)
    (R' : Type u) [CommRing R'] [IsDomain R'] [ValuationRing R']
    (K' : Type u) [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    (φ : sq.R →+* R') [IsLocalHom φ] (ψ : sq.K →+* K')
    (hφψ : (algebraMap R' K').comp φ = ψ.comp (algebraMap sq.R sq.K))
    (l : Spec (CommRingCat.of R') ⟶ X)
    (hl₁ : Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ l =
      Spec.map (CommRingCat.ofHom ψ) ≫ sq.i₁)
    (hl₂ : l ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ sq.i₂) :
    sq.commSq.HasLift := by
  let lft := pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)))
    sq.i₁ sq.commSq.w.symm
  let t := pullback.lift (Spec.map (CommRingCat.ofHom φ)) l hl₂.symm
  have ht : Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ t =
      Spec.map (CommRingCat.ofHom ψ) ≫ lft := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, t, lft]
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφψ]
    · simpa only [Category.assoc, pullback.lift_snd, t, lft] using hl₁
  apply hasLift_of_specialization sq (t (closedPoint R'))
  · have hη : Spec.map (CommRingCat.ofHom ψ) (closedPoint K') =
        closedPoint sq.K := Subsingleton.elim _ _
    have htop : t (Spec.map (CommRingCat.ofHom (algebraMap R' K')) (closedPoint K')) =
        lft (closedPoint sq.K) := by
      have h := congrArg (fun m ↦ m (closedPoint K')) ht
      change t (Spec.map (CommRingCat.ofHom (algebraMap R' K')) (closedPoint K')) =
        lft (Spec.map (CommRingCat.ofHom ψ) (closedPoint K')) at h
      rwa [hη] at h
    rw [← htop]
    exact (specializes_closedPoint _).map t.continuous
  · change (t ≫ pullback.fst sq.i₂ f) (closedPoint R') = closedPoint sq.R
    rw [pullback.lift_fst]
    exact comap_closedPoint φ

end ValuativeDescent

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Extending the actual rigidified Poincare class over a dominating valuation
ring, and then classifying it, proves valuative existence over the original ring. -/
theorem relativeDualSchemeValuativeExistence_of_picardZeroValuativeExtension
    (hExt : PicardZeroValuativeExtensionStatement.{u}) :
    RelativeDualSchemeValuativeExistenceStatement.{u} := by
  intro S _ A hA sq
  let coherence := RigidifiedModule.pullbackCoherence.{u}
  let stability := picardZeroPullback.{u}
  let TK : Over S := Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.i₂)
  let g : TK ⟶ dualScheme A hA := Over.homMk sq.i₁ sq.commSq.w
  let q₀ : PicardZeroClasses A (dualScheme A hA) :=
    ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
      (poincareFamily A hA), (poincareFamily_universal A hA).1⟩
  let q : PicardZeroClasses A TK := picardZeroClassesPullback stability A g q₀
  have hg : dualClassify A hA TK q = g := by
    rw [dualClassify_pullback A coherence stability hA,
      dualClassify_poincare A coherence hA, Category.comp_id]
  obtain ⟨R', _, _, _, K', _, _, _, φ, hφ, ψ, hφψ, q', hq'⟩ :=
    hExt S A sq.R sq.K sq.i₂ q
  have : IsLocalHom φ := hφ
  let TR' : Over S := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ sq.i₂)
  let TK' : Over S := Over.mk (Spec.map (CommRingCat.ofHom ψ) ≫
    Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.i₂)
  let h : TK' ⟶ TR' :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) (by
      simp only [TK', TR', Over.mk_hom, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hφψ])
  let k : TK' ⟶ TK := Over.homMk (Spec.map (CommRingCat.ofHom ψ)) rfl
  have he : picardZeroClassesPullback stability A h q' =
      picardZeroClassesPullback stability A k q := Subtype.ext hq'
  have heq : h ≫ dualClassify A hA TR' q' = k ≫ g := by
    rw [← dualClassify_pullback A coherence stability hA, he,
      dualClassify_pullback A coherence stability hA, hg]
  apply ValuativeDescent.hasLift_of_dominatingLift sq R' K' φ ψ hφψ
    (dualClassify A hA TR' q').left
  · exact congrArg (fun m ↦ m.left) heq
  · exact Over.w _

/-- The focused reduction proposition holds. It does not discharge its
Picard-zero extension antecedent. -/
theorem relativeDualSchemeValuativeExistenceReduction :
    RelativeDualSchemeValuativeExistenceReductionStatement.{u} :=
  relativeDualSchemeValuativeExistence_of_picardZeroValuativeExtension

end Langlands.AbelianScheme
