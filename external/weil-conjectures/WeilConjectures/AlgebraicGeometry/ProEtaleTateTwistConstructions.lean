/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistLevels
import all WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistLevels
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Filtered.Final

/-! # Coefficient extension maps, the field colimit and signed Tate twists

Source: blueprint `definition-tate-twists`. The finite levels and integral and
rational objects are re-exported from `ProEtaleTateTwistLevels`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance 20000] HasLimitsOfShape.has_limit HasColimitsOfShape.has_colimit
attribute [local instance 20000] Sheaf.instHasLimitsOfShape AddCommGrpCat.hasLimitsOfShape

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local irreducible] spEllPointReduction spEllPointTransition

set_option backward.isDefEq.respectTransparency false in
/-- The integral coefficient inclusion is the unique ring map over E_X -> F_X.
Source: blueprint field-extension transitions (blueprint: definition-tate-twists).
Proof: the inclusion E -> F preserves the extending valuation, so restrict it to
O_E -> O_F and apply continuous-function condensation and p_X^*. The square
commutes before pullback and hence afterwards. The inclusion O_F,X -> F_X is
monic: it is monic on profinite tests and p_X^* is left exact. Cancel it to obtain
uniqueness. This does not choose an arbitrary scalar map. -/
theorem spIntegersMap_existsUnique {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    ∃! φ : condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X ⟶
        condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ F.1) X,
      IsMonHom φ ∧
      φ ≫ padicIntegersToPadicSubfield X ℓ F =
        padicIntegersToPadicSubfield X ℓ E ≫
          coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let := PadicAlgCl.normedFieldOfAlgebra ℓ F.1
  let j : PadicAlgCl.integers ℓ E.1 →+* PadicAlgCl.integers ℓ F.1 :=
    ((IntermediateField.inclusion h).toRingHom.comp
      (PadicAlgCl.integers ℓ E.1).subtype).codRestrict _ (fun x ↦ x.2)
  have hj : Continuous j :=
    Continuous.subtype_mk
      ((continuous_induced_rng (f := algebraMap F.1 (PadicAlgCl ℓ))).mpr
        (show Continuous fun x : PadicAlgCl.integers ℓ E.1 ↦
          algebraMap E.1 (PadicAlgCl ℓ) (x : E.1) from
          continuous_induced_dom.comp continuous_subtype_val)) _
  let b := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap j hj)
  have hb : b ≫ padicIntegersRingObjToContinuousMapRingObj ℓ F =
      padicIntegersRingObjToContinuousMapRingObj ℓ E ≫
        Profinite.padicSubfieldRingObjMap ℓ h := rfl
  have hm : Mono (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ F) := by
    have hcomp (S : Profinite.{u}ᵒᵖ) :
        Mono ((padicIntegersRingObjToContinuousMapRingObj.{u} ℓ F).hom.app S) := by
      apply (AddCommGrpCat.mono_iff_injective _).mpr
      intro a b hab
      apply ULift.ext
      apply ContinuousMap.ext
      intro t
      apply Subtype.val_injective
      exact congrArg (fun z : ULift.{u + 1} C(S.unop, F.1) ↦ z.down t) hab
    let : Mono (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ F).hom :=
      @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ hcomp
    exact (sheafToPresheaf _ _).mono_of_mono_map
      (inferInstance : Mono (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ F).hom)
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  have : Mono (padicIntegersToPadicSubfield X ℓ F) :=
    (upperStarFromPoint X).map_mono _
  refine ⟨coefficientMap b X, ⟨inferInstance, ?_⟩, ?_⟩
  · exact ((upperStarFromPoint X).map_comp _ _).symm.trans
      ((congrArg (upperStarFromPoint X).map hb).trans
        ((upperStarFromPoint X).map_comp _ _))
  · intro g hg
    apply (cancel_mono (padicIntegersToPadicSubfield X ℓ F)).mp
    exact hg.2.trans (((upperStarFromPoint X).map_comp _ _).symm.trans
      ((congrArg (upperStarFromPoint X).map hb.symm).trans
        ((upperStarFromPoint X).map_comp _ _)))

/-- Pullback of the continuous inclusion O_E -> O_F, uniquely fixed by E -> F.
Source: blueprint field-extension transitions (blueprint: definition-tate-twists). -/
def spIntegersMap {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X ⟶
      condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ F.1) X :=
  (spIntegersMap_existsUnique X ℓ h).exists.choose

private theorem spIntegersMap_spec {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) : IsMonHom (spIntegersMap X ℓ h) ∧
      spIntegersMap X ℓ h ≫ padicIntegersToPadicSubfield X ℓ F =
        padicIntegersToPadicSubfield X ℓ E ≫
          coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X := by
  unfold spIntegersMap
  exact (spIntegersMap_existsUnique X ℓ h).exists.choose_spec

attribute [local irreducible] spIntegersMap

private theorem spEllReduction_isMonHom
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    IsMonHom (spEllReduction X ℓ E n) := by
  dsimp only [spEllReduction]
  infer_instance

attribute [local instance] spEllReduction_isMonHom

set_option backward.isDefEq.respectTransparency false in
private theorem spEllReduction_epi (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    Epi (spEllReduction X ℓ E n) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  let : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  have hq := Ideal.Quotient.mk_surjective (I := spTateEllIdeal ℓ E n)
  have hp : Epi (spEllPointReduction.{u} ℓ E n) := by
    apply (sheafToPresheaf _ _).epi_of_epi_map
    have hcomp (S : Profinite.{u}ᵒᵖ) :
        Epi ((spEllPointReduction.{u} ℓ E n).hom.app S) := by
      apply (AddCommGrpCat.epi_iff_surjective _).mpr
      intro b
      let a : C(S.unop, PadicAlgCl.integers ℓ E.1) :=
        ⟨fun t ↦ (hq (b.down t)).choose,
          (continuous_of_discreteTopology (f := fun x ↦ (hq x).choose)).comp
            b.down.continuous⟩
      refine ⟨ULift.up a, ?_⟩
      unfold spEllPointReduction
      apply ULift.ext
      apply ContinuousMap.ext
      intro t
      exact (hq (b.down t)).choose_spec
    exact @NatTrans.epi_of_epi_app _ _ _ _ _ _ _ hcomp
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) := inferInstance
  exact (upperStarFromPoint X).map_epi _

set_option backward.isDefEq.respectTransparency false in
/-- The induced quotient inclusion is characterized by the two integral reductions.
Source: blueprint field-extension transitions (blueprint: definition-tate-twists).
Proof: the integral ring inclusion sends ell^(n+1) to ell^(n+1), so descends to
the finite quotients. Condense and pull back that quotient map. The quotient
reduction is an epimorphism, so its commuting square determines the map uniquely. -/
theorem spEllMap_existsUnique {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (n : ℕ) :
    ∃! φ : condensedRingObj.{u} (spEllPointRingObj ℓ E n) X ⟶
        condensedRingObj.{u} (spEllPointRingObj ℓ F n) X,
      spEllReduction X ℓ E n ≫ φ =
        spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let := PadicAlgCl.normedFieldOfAlgebra ℓ F.1
  let : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  let : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  let : TopologicalSpace (spEllQuotient ℓ F n) := ⊥
  let : DiscreteTopology (spEllQuotient ℓ F n) := ⟨rfl⟩
  let j : PadicAlgCl.integers ℓ E.1 →+* PadicAlgCl.integers ℓ F.1 :=
    ((IntermediateField.inclusion h).toRingHom.comp
      (PadicAlgCl.integers ℓ E.1).subtype).codRestrict _ (fun x ↦ x.2)
  have hj : Continuous j :=
    Continuous.subtype_mk
      ((continuous_induced_rng (f := algebraMap F.1 (PadicAlgCl ℓ))).mpr
        (show Continuous fun x : PadicAlgCl.integers ℓ E.1 ↦
          algebraMap E.1 (PadicAlgCl ℓ) (x : E.1) from
          continuous_induced_dom.comp continuous_subtype_val)) _
  let b := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap j hj)
  have hb : b ≫ padicIntegersRingObjToContinuousMapRingObj ℓ F =
      padicIntegersRingObjToContinuousMapRingObj ℓ E ≫
        Profinite.padicSubfieldRingObjMap ℓ h := rfl
  have hi : coefficientMap b X = spIntegersMap X ℓ h := by
    apply (spIntegersMap_existsUnique X ℓ h).unique
    · refine ⟨inferInstance, ?_⟩
      exact ((upperStarFromPoint X).map_comp _ _).symm.trans
        ((congrArg (upperStarFromPoint X).map hb).trans
          ((upperStarFromPoint X).map_comp _ _))
    · exact spIntegersMap_spec X ℓ h
  have hI : spTateEllIdeal ℓ E n ≤ (spTateEllIdeal ℓ F n).comap j := by
    apply Ideal.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    change j ((ℓ : PadicAlgCl.integers ℓ E.1) ^ (n + 1)) ∈ spTateEllIdeal ℓ F n
    rw [map_pow, map_natCast]
    exact Ideal.subset_span (Set.mem_singleton _)
  let q := Ideal.quotientMap (spTateEllIdeal ℓ F n) j hI
  let c := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap q continuous_of_discreteTopology)
  have hc : spEllPointReduction ℓ E n ≫ c = b ≫ spEllPointReduction ℓ F n := by
    unfold spEllPointReduction
    ext S a
    rfl
  have he : spEllReduction X ℓ E n ≫ coefficientMap c X =
      spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n := by
    have he := ((upperStarFromPoint X).map_comp _ _).symm.trans
      ((congrArg (upperStarFromPoint X).map hc).trans
        ((upperStarFromPoint X).map_comp _ _))
    change spEllReduction X ℓ E n ≫ coefficientMap c X =
      coefficientMap b X ≫ spEllReduction X ℓ F n at he
    rw [hi] at he
    exact he
  have := spEllReduction_epi X ℓ E n
  refine ⟨coefficientMap c X, he, ?_⟩
  intro g hg
  exact (cancel_epi (spEllReduction X ℓ E n)).mp (hg.trans he.symm)

/-- The finite quotient inclusion along E -> F, fixed by the integral reductions.
Source: blueprint field-extension transitions (blueprint: definition-tate-twists). -/
def spEllMap {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (n : ℕ) :
    condensedRingObj.{u} (spEllPointRingObj ℓ E n) X ⟶
      condensedRingObj.{u} (spEllPointRingObj ℓ F n) X :=
  (spEllMap_existsUnique X ℓ h n).exists.choose

private theorem spEllMap_spec {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) (n : ℕ) : spEllReduction X ℓ E n ≫ spEllMap X ℓ h n =
      spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n := by
  unfold spEllMap
  exact (spEllMap_existsUnique X ℓ h n).exists.choose_spec

attribute [local irreducible] spEllMap

set_option backward.isDefEq.respectTransparency false in
/-- The integral transition is uniquely specified on every positive quotient twist.
Source: blueprint field-extension transitions (blueprint: definition-tate-twists).
Proof: tensor each finite quotient inclusion with the identity on the root sheaf.
These maps commute with reduction and Kummer transition. The forgetful functor
creates limits, so the compatible finite-level maps give a unique map of limits. -/
theorem spIntegralTwistMap_existsUnique {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    ∃! f : (spIntegralTwist X ℓ E).X ⟶ (spIntegralTwist X ℓ F).X,
      ∀ n : ℕ, f ≫ (limit.π (spIntegralTwistSystem X ℓ F) (op n)).hom =
        (limit.π (spIntegralTwistSystem X ℓ E) (op n)).hom ≫
          (spEllMap X ℓ h n ⊗ₘ
            𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))) := by
  let : HasLimit (spIntegralTwistSystem X ℓ E) := inferInstance
  let : HasLimit (spIntegralTwistSystem X ℓ F) := inferInstance
  have hred (K : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
      spEllReduction X ℓ K (n + 1) ≫
        coefficientMap.{u} (spEllPointTransition ℓ K n) X = spEllReduction X ℓ K n := by
    rw [← coefficientMap_comp]
    apply congrArg (fun f ↦ coefficientMap.{u} f X)
    unfold spEllPointReduction spEllPointTransition
    rw [← Functor.map_comp]
    rfl
  have he (n : ℕ) : spEllReduction X ℓ E n ≫ spEllMap X ℓ h n =
      spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n :=
    spEllMap_spec X ℓ h n
  have ht (n : ℕ) :
      spEllMap X ℓ h (n + 1) ≫ coefficientMap.{u} (spEllPointTransition ℓ F n) X =
        coefficientMap.{u} (spEllPointTransition ℓ E n) X ≫ spEllMap X ℓ h n := by
    have := spEllReduction_epi X ℓ E (n + 1)
    apply (cancel_epi (spEllReduction X ℓ E (n + 1))).mp
    rw [← Category.assoc, he (n + 1), Category.assoc, hred F n,
      ← Category.assoc, hred E n, he n]
  let τ : spIntegralTwistSystem X ℓ E ⋙ Mod.forget _ ⟶
      spIntegralTwistSystem X ℓ F ⋙ Mod.forget _ :=
    NatTrans.ofOpSequence
      (fun n ↦ spEllMap X ℓ h n ⊗ₘ
        𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))) (by
      intro n
      simp only [Functor.comp_map, spIntegralTwistSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      change (spIntegralLevelTransition X ℓ E n).hom ≫ _ =
        _ ≫ (spIntegralLevelTransition X ℓ F n).hom
      dsimp only [spIntegralLevelTransition]
      rw [(spIntegralLevelTransition_existsUnique X ℓ E n).exists.choose_spec,
        (spIntegralLevelTransition_existsUnique X ℓ F n).exists.choose_spec,
        tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id, ht n])
  let c := (Cone.postcompose τ).obj
    ((Mod.forget _).mapCone (limit.cone (spIntegralTwistSystem X ℓ E)))
  let hc := isLimitOfPreserves (Mod.forget _)
    (limit.isLimit (spIntegralTwistSystem X ℓ F))
  refine ⟨hc.lift c, ?_, ?_⟩
  · intro n
    exact hc.fac c (op n)
  · intro g hg
    apply hc.hom_ext
    intro n
    exact (hg n.unop).trans (hc.fac c n).symm

/-- Integral extension transition: the coefficient inclusion on every root level.
Source: blueprint field-extension transitions (blueprint: definition-tate-twists). -/
def spIntegralTwistMap {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    (spIntegralTwist X ℓ E).X ⟶ (spIntegralTwist X ℓ F).X :=
  (spIntegralTwistMap_existsUnique X ℓ h).exists.choose

private theorem spIntegralTwistMap_spec {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) : ∀ n : ℕ, spIntegralTwistMap X ℓ h ≫
      (limit.π (spIntegralTwistSystem X ℓ F) (op n)).hom =
        (limit.π (spIntegralTwistSystem X ℓ E) (op n)).hom ≫
          (spEllMap X ℓ h n ⊗ₘ
            𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))) := by
  unfold spIntegralTwistMap
  exact (spIntegralTwistMap_existsUnique X ℓ h).exists.choose_spec

attribute [local irreducible] spIntegralTwistMap

private theorem spMonHom_of_epi
    {C : Type*} [Category C] [MonoidalCategory C]
    [∀ Z : C, (tensorLeft Z).PreservesEpimorphisms]
    [∀ Z : C, (tensorRight Z).PreservesEpimorphisms]
    {R B D : C} [MonObj R] [MonObj B] [MonObj D]
    (p : R ⟶ B) [IsMonHom p] [Epi p]
    (q : R ⟶ D) [IsMonHom q] (r : B ⟶ D) (h : p ≫ r = q) :
    IsMonHom r := by
  have he : Epi (p ⊗ₘ p) := by
    have : Epi (p ▷ R) := (tensorRight R).map_epi p
    have : Epi (B ◁ p) := (tensorLeft B).map_epi p
    rw [MonoidalCategory.tensorHom_def]
    infer_instance
  constructor
  · rw [← IsMonHom.one_hom p, Category.assoc, h, IsMonHom.one_hom q]
  · apply (cancel_epi (p ⊗ₘ p)).mp
    rw [← Category.assoc, ← IsMonHom.mul_hom p, Category.assoc, h, IsMonHom.mul_hom q,
      tensorHom_comp_tensorHom_assoc p p r r MonObj.mul, h]

private theorem spIntegralTwistMap_semilinear
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    Mod.act (spIntegralTwist X ℓ E).X ≫ spIntegralTwistMap X ℓ h =
      (spIntegersMap X ℓ h ⊗ₘ spIntegralTwistMap X ℓ h) ≫
        Mod.act (spIntegralTwist X ℓ F).X  := by
  let : MonObj (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) :=
    inferInstance
  let : MonObj (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ F.1) X) :=
    inferInstance
  let : ModObj (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)
      (spIntegralTwist X ℓ E).X :=
    (spIntegralTwist X ℓ E).mod
  let : ∀ n : ℕ,
      ModObj (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)
      (spIntegralTwistLevel X ℓ E n).X := fun n ↦ (spIntegralTwistLevel X ℓ E n).mod
  let : ModObj (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ F.1) X)
      (spIntegralTwist X ℓ F).X :=
    (spIntegralTwist X ℓ F).mod
  let : ∀ n : ℕ,
      ModObj (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ F.1) X)
      (spIntegralTwistLevel X ℓ F n).X := fun n ↦ (spIntegralTwistLevel X ℓ F n).mod
  let : HasLimit (spIntegralTwistSystem X ℓ E) := inferInstance
  let : HasLimit (spIntegralTwistSystem X ℓ F) := inferInstance
  let pE (n : ℕᵒᵖ) : (spIntegralTwist X ℓ E).X ⟶
      (spIntegralTwistLevel X ℓ E n.unop).X :=
    (limit.π (spIntegralTwistSystem X ℓ E) n).hom
  let pF (n : ℕᵒᵖ) : (spIntegralTwist X ℓ F).X ⟶
      (spIntegralTwistLevel X ℓ F n.unop).X :=
    (limit.π (spIntegralTwistSystem X ℓ F) n).hom
  have hi : IsMonHom (spIntegersMap X ℓ h) :=
    (spIntegersMap_spec X ℓ h).1
  have he (n : ℕ) : spEllReduction X ℓ E n ≫ spEllMap X ℓ h n =
      spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n :=
    spEllMap_spec X ℓ h n
  have hp (n : ℕ) : spIntegralTwistMap X ℓ h ≫
      pF (op n) =
      pE (op n) ≫
        (spEllMap X ℓ h n ⊗ₘ
          𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))) :=
    spIntegralTwistMap_spec X ℓ h n
  have hlevel (n : ℕ) :
      Mod.act (spIntegralTwistLevel X ℓ E n).X ≫
          (spEllMap X ℓ h n ⊗ₘ
            𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))) =
        (spIntegersMap X ℓ h ⊗ₘ
          (spEllMap X ℓ h n ⊗ₘ
            𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))))) ≫
          Mod.act (spIntegralTwistLevel X ℓ F n).X := by
    let : MonObj (condensedRingObj.{u} (spEllPointRingObj.{u} ℓ E n) X) :=
      inferInstance
    let : MonObj (condensedRingObj.{u} (spEllPointRingObj.{u} ℓ F n) X) :=
      inferInstance
    have := spEllReduction_epi X ℓ E n
    have : IsMonHom (spEllMap X ℓ h n) :=
      spMonHom_of_epi (spEllReduction X ℓ E n)
        (spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n) _ (he n)
    obtain ⟨f, hf, _⟩ := spFreeTensor_linear (spEllReduction X ℓ E n)
      (spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n) (spEllMap X ℓ h n) (he n)
      (𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))))
    have hl := Mod.act_hom f
    rw [hf] at hl
    set_option backward.isDefEq.respectTransparency false in
    simpa only [spIntegralTwistLevel, Mod.comap_obj_smul,
      MonoidalCategory.tensorHom_def', comp_whiskerRight, Category.assoc] using hl
  apply (isLimitOfPreserves (Mod.forget _)
    (limit.isLimit (spIntegralTwistSystem X ℓ F))).hom_ext
  intro n
  change (Mod.act (spIntegralTwist X ℓ E).X ≫ spIntegralTwistMap X ℓ h) ≫
      pF n =
    ((spIntegersMap X ℓ h ⊗ₘ spIntegralTwistMap X ℓ h) ≫
      Mod.act (spIntegralTwist X ℓ F).X) ≫
        pF n
  have hpE := Mod.act_hom (limit.π (spIntegralTwistSystem X ℓ E) n)
  have hpF := Mod.act_hom (limit.π (spIntegralTwistSystem X ℓ F) n)
  change Mod.act (spIntegralTwist X ℓ E).X ≫ _ = _ at hpE
  change Mod.act (spIntegralTwist X ℓ F).X ≫ _ = _ at hpF
  set_option backward.isDefEq.respectTransparency false in
  rw [Category.assoc, hp n.unop, ← Category.assoc,
    hpE, Category.assoc, hlevel n.unop, Category.assoc, hpF]
  set_option backward.isDefEq.respectTransparency false in
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]
  set_option backward.isDefEq.respectTransparency false in
  rw [hp n.unop]

set_option backward.isDefEq.respectTransparency true in
private theorem spExtend_map_existsUnique
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    {R S A B : C} [MonObj R] [MonObj S] [MonObj A] [MonObj B]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj A] [IsCommMonObj B]
    (p : R ⟶ A) [IsMonHom p] (q : S ⟶ B) [IsMonHom q]
    (a : R ⟶ S) [IsMonHom a] (b : A ⟶ B) [IsMonHom b]
    (hab : p ≫ b = a ≫ q) (M : Mod C R) (N : Mod C S)
    (g : M.X ⟶ N.X)
    (hg : Mod.act M.X ≫ g = (a ⊗ₘ g) ≫ Mod.act N.X) :
    ∃! f : (Mod.extendScalarsObj p M).X ⟶ (Mod.extendScalarsObj q N).X,
      Mod.extendπ p M ≫ f = (b ⊗ₘ g) ≫ Mod.extendπ q N := by
  have hm : (A ◁ p ≫ MonObj.mul) ≫ b =
      (b ⊗ₘ a) ≫ (B ◁ q ≫ MonObj.mul) := by
    rw [Category.assoc, IsMonHom.mul_hom]
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp]
    rw [hab, Category.comp_id]
  have hbal : (A ◁ p ≫ MonObj.mul) ▷ M.X ≫
        (b ⊗ₘ g) ≫ Mod.extendπ q N =
      ((α_ A R M.X).hom ≫ A ◁ Mod.act M.X) ≫
        (b ⊗ₘ g) ≫ Mod.extendπ q N := by
    calc
      _ = (((b ⊗ₘ a) ≫ (B ◁ q ≫ MonObj.mul)) ⊗ₘ g) ≫ Mod.extendπ q N := by
        simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp]
        rw [hm]
      _ = ((b ⊗ₘ a) ⊗ₘ g) ≫ (B ◁ q ≫ MonObj.mul) ▷ N.X ≫
          Mod.extendπ q N := by
        simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id]
      _ = ((b ⊗ₘ a) ⊗ₘ g) ≫ (α_ B S N.X).hom ≫ B ◁ Mod.act N.X ≫
          Mod.extendπ q N := by
        rw [Mod.extendπ_condition]
        simp only [Category.assoc]
      _ = (α_ A R M.X).hom ≫ (b ⊗ₘ ((a ⊗ₘ g) ≫ Mod.act N.X)) ≫
          Mod.extendπ q N := by
        rw [associator_naturality_assoc]
        simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id]
      _ = _ := by
        rw [← hg]
        simp only [Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.id_comp]
  refine ⟨Mod.extendDescHom p ((b ⊗ₘ g) ≫ Mod.extendπ q N) hbal,
    Mod.extendπ_extendDescHom _ _ _, ?_⟩
  intro f hf
  apply (cancel_epi (Mod.extendπ p M)).mp
  rw [hf, Mod.extendπ_extendDescHom]

/-- Localization gives the unique rational transition with the prescribed tensor formula.
Source: blueprint rational field-extension transitions (blueprint: definition-tate-twists).
Proof: tensor the maps E_X -> F_X and O_E,X(1) -> O_F,X(1). The integral map is
semilinear because its projections are tensor maps linear in the scalar factor.
The coefficient square makes the tensor map balanced. Descend through the defining
coequalizer of extension of scalars. Its epimorphic projection gives uniqueness. -/
theorem spRationalTwistMap_existsUnique {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    ∃! f : (spRationalTwist X ℓ E).X ⟶ (spRationalTwist X ℓ F).X,
      Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E) ≫ f =
        (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X ⊗ₘ
          spIntegralTwistMap X ℓ h) ≫
            Mod.extendπ (padicIntegersToPadicSubfield X ℓ F) (spIntegralTwist X ℓ F) := by
  have hi := spIntegersMap_spec X ℓ h
  have : IsMonHom (spIntegersMap X ℓ h) := hi.1
  exact spExtend_map_existsUnique (padicIntegersToPadicSubfield X ℓ E)
    (padicIntegersToPadicSubfield X ℓ F) (spIntegersMap X ℓ h)
    (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X) hi.2.symm
    (spIntegralTwist X ℓ E) (spIntegralTwist X ℓ F)
    (spIntegralTwistMap X ℓ h) (spIntegralTwistMap_semilinear X ℓ h)

/-- The rational field-extension transition, with its specified localization normalization.
Source: blueprint field-extension transitions (blueprint: definition-tate-twists). -/
def spRationalTwistMap {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    (spRationalTwist X ℓ E).X ⟶ (spRationalTwist X ℓ F).X :=
  (spRationalTwistMap_existsUnique X ℓ h).exists.choose

attribute [local irreducible] spRationalTwistMap

attribute [local irreducible] spIntegralTwist spIntegralTwistSystem

end AlgebraicGeometry.ProEtale
