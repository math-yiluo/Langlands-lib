/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralCoefficientLimit
import WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatiblePrimitiveRoots
import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom

/-! # Compatible local bases of the native integral root tower -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonObj Limits Opposite
open scoped CategoryTheory.Obj
namespace AddCommGrpCat
private def intResidue (n : ℕ) : 𝟙_ Ab.{u + 1} ⟶ of (ULift.{u + 1} (ZMod n)) :=
  ofHom ((AddEquiv.ulift.symm.toAddMonoidHom).comp
    ((Int.castAddHom (ZMod n)).comp AddEquiv.ulift.toAddMonoidHom))
private theorem intResidue_condition (n : ℕ) : (n • 𝟙 (𝟙_ Ab.{u + 1})) ≫ intResidue n = 0 := by
  ext x
  change ((n • x.down : ℤ) : ZMod n) = 0
  simp
private noncomputable def intResidueCokernel (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (intResidue.{u} n) (intResidue_condition n)) := by
  have : Epi (intResidue.{u} n) := by
    rw [epi_iff_surjective]
    intro a
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective a.down
    exact ⟨ULift.up b, congrArg ULift.up hb⟩
  let S := ShortComplex.mk (n • 𝟙 (𝟙_ Ab.{u + 1})) (intResidue.{u} n)
    (intResidue_condition n)
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro a ha
    have h : (a.down : ZMod n) = 0 := congrArg ULift.down ha
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    refine ⟨ULift.up b, ?_⟩
    apply ULift.ext
    exact (show (n : ℤ) * b = a.down from hb.symm)
  exact hS.gIsCokernel
end AddCommGrpCat

namespace AlgebraicGeometry.ProEtale

private def freeUnitIso {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.freeFunctor R).obj (𝟙_ _) ≅ Mod.regular R :=
  Mod.isoMk (ρ_ R) (by
    change ((α_ R R (𝟙_ _)).inv ≫ μ[R] ▷ (𝟙_ _)) ≫ (ρ_ R).hom =
      R ◁ (ρ_ R).hom ≫ μ[R]
    rw [Category.assoc, rightUnitor_naturality]
    monoidal)

private instance freeFunctorAdditive {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.freeFunctor R).Additive :=
  { map_add := by
      intro A B f g
      apply Mod.hom_ext
      exact MonoidalPreadditive.whiskerLeft_add f g }

private def freeConstantResidueIso {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (n : ℕ) (hR : n • 𝟙 R = 0) :
    (Mod.freeFunctor R).obj ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) ≅ Mod.regular R := by
  let F := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ Mod.freeFunctor R
  let e : F.obj (𝟙_ Ab.{u + 1}) ≅ Mod.regular R :=
    (Mod.freeFunctor R).mapIso
      (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})).symm ≪≫
        freeUnitIso R
  have : (Mod.freeFunctor R).IsLeftAdjoint := ⟨_, ⟨Mod.freeForgetAdjunction R⟩⟩
  let c := CokernelCofork.ofπ (AddCommGrpCat.intResidue.{u} n)
    (AddCommGrpCat.intResidue_condition n)
  have hzero : F.map (n • 𝟙 (𝟙_ Ab.{u + 1})) = 0 := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    apply (cancel_mono e.hom).mp
    rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
    have hh : n • 𝟙 (Mod.regular R) = 0 := by
      apply (Mod.forget R).map_injective
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
      change n • 𝟙 R = 0
      exact hR
    calc
      n • e.hom = e.hom ≫ (n • 𝟙 _) := by
        rw [Preadditive.comp_nsmul, Category.comp_id]
      _ = 0 := by rw [hh, comp_zero]
  have : IsIso (F.map (AddCommGrpCat.intResidue n)) :=
    CokernelCofork.IsColimit.isIso_π (c.map F)
      (c.mapIsColimit (AddCommGrpCat.intResidueCokernel n) F) hzero
  exact (asIso (F.map (AddCommGrpCat.intResidue n))).symm ≪≫ e

private theorem finiteRing_nsmul (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ) :
    (l ^ (n + 1)) • 𝟙 (condensedRingObj (twistFiniteRing l E n) X) = 0 := by
  let : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  let : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  have hp : (l ^ (n + 1)) • 𝟙 (twistFiniteRing l E n) = 0 := by
    apply Sheaf.hom_ext
    ext V f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    change (l ^ (n + 1)) • _ = (0 : Padic.coefficientExtensionRing l E (n + 1))
    rw [nsmul_eq_mul, Nat.cast_pow, coefficientFiniteTwist_annihilator, zero_mul]
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint X).Additive := Functor.additive_of_preservesBinaryBiproducts _
  change (l ^ (n + 1)) • 𝟙 ((upperStarFromPoint X).obj (twistFiniteRing l E n)) = 0
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hp, Functor.map_zero]

private def cyclicGenerator (X : Scheme.{u}) (n : ℕ) :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) :=
  (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})).hom ≫
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (AddCommGrpCat.intResidue n)

private theorem freeConstantResidueIso_inv {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (n : ℕ) (hR : n • 𝟙 R = 0) :
    (freeConstantResidueIso R n hR).inv.hom =
      (ρ_ R).inv ≫ R ◁ cyclicGenerator X n := by
  change (ρ_ R).inv ≫ R ◁
    (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})).hom ≫
      R ◁ (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (AddCommGrpCat.intResidue n) = _
  simp only [cyclicGenerator, whiskerLeft_comp]

private def externalTensor {Y : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] :
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R ×
      Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1} ⥤
        Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R where
  obj P := (Mod.tensorRight R P.2).obj P.1
  map {P Q} f := (Mod.tensorRight R P.2).map f.1 ≫ (Mod.tensorRightMap R f.2).app Q.1
  map_id P := by
    apply Mod.hom_ext
    change 𝟙 P.1.X ▷ P.2 ≫ P.1.X ◁ 𝟙 P.2 = 𝟙 _
    simp
  map_comp {P Q S} f g := by
    apply Mod.hom_ext
    change (f.1.hom ≫ g.1.hom) ▷ P.2 ≫ S.1.X ◁ (f.2 ≫ g.2) =
      (f.1.hom ▷ P.2 ≫ Q.1.X ◁ f.2) ≫ (g.1.hom ▷ Q.2 ≫ S.1.X ◁ g.2)
    simpa only [MonoidalCategory.tensorHom_def] using
      (tensorHom_comp_tensorHom f.1.hom f.2 g.1.hom g.2).symm

private def tensorDiagram {Y : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R]
    (B : ℕᵒᵖ ⥤ Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R)
    (D : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :=
  B.prod' D ⋙ externalTensor R

private def positiveRoots (X : Scheme.{u}) (l : ℕ) :=
  (Order.gc_pred_succ (α := ℕ)).monotone_u.functor.op ⋙ tateRootsSystem X l

private def positiveConstants (X : Scheme.{u}) (l : ℕ) :=
  (Order.gc_pred_succ (α := ℕ)).monotone_u.functor.op ⋙ constantTateResidueSystem X l

private theorem positiveRoots_map (X : Scheme.{u}) (l n : ℕ) :
    (positiveRoots X l).map (homOfLE n.le_succ).op =
      eqToHom (by rw [pow_succ'] :
        rootsOfUnitySheaf X (l ^ (n + 2)) = rootsOfUnitySheaf X (l * l ^ (n + 1))) ≫
          rootsOfUnitySheafPow X (l ^ (n + 1)) l := by
  change (tateRootsSystem X l).map (homOfLE (n + 1).le_succ).op = _
  exact Functor.ofOpSequence_map_homOfLE_succ _ (n + 1)

private theorem positiveConstants_map (X : Scheme.{u}) (l n : ℕ) :
    (positiveConstants X l).map (homOfLE n.le_succ).op =
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (integralResidueAbTransition l (n + 1)) := by
  change (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
    ((Functor.ofOpSequence
      (X := fun n ↦ AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ n))))
      (integralResidueAbTransition.{u} l)).map
      (homOfLE (n + 1).le_succ).op) = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]

private theorem tensorGenerator_naturality {Y : Scheme.{u}}
    {A B M N : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}}
    (f : A ⟶ B) (a : 𝟙_ _ ⟶ M) (b : 𝟙_ _ ⟶ N) (g : M ⟶ N) (h : a ≫ g = b) :
    f ≫ ((ρ_ B).inv ≫ B ◁ b) =
      ((ρ_ A).inv ≫ A ◁ a) ≫ (f ▷ M ≫ B ◁ g) := by
  rw [rightUnitor_inv_naturality_assoc]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, ← whiskerLeft_comp, h]

private def freeRestrictionIso {Y : Scheme.{u}}
    {R B : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}}
    [MonObj R] [MonObj B] (q : R ⟶ B) [IsMonHom q]
    (M : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :
    (Mod.comap q).obj ((Mod.freeFunctor B).obj M) ≅
      (Mod.tensorRight R M).obj ((Mod.comap q).obj (Mod.regular B)) :=
  Mod.isoMk (Iso.refl _) (by
    change (q ▷ (B ⊗ M) ≫ (α_ B B M).inv ≫ μ[B] ▷ M) ≫ 𝟙 _ =
      R ◁ 𝟙 _ ≫ (α_ R B M).inv ≫ (q ▷ B ≫ μ[B]) ▷ M
    simp only [Category.comp_id, whiskerLeft_id, Category.id_comp, comp_whiskerRight]
    rw [associator_inv_naturality_left_assoc])

-- Elaborating the root-tower naturality comparison unfolds several module actions.
private def rootTensorIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    coefficientIntegralTwistSystem l E X ≅ tensorDiagram
      (condensedRingObj (twistIntegralRing l E) X) (nativeCoefficientSystem l E X)
        (positiveRoots X l) := by
  let t : coefficientIntegralTwistSystem l E X ⟶ tensorDiagram
      (condensedRingObj (twistIntegralRing l E) X) (nativeCoefficientSystem l E X)
        (positiveRoots X l) :=
    NatTrans.ofOpSequence (fun n ↦ (freeRestrictionIso
      (coefficientMap (twistReduction l E n) X) (rootsOfUnitySheaf X (l ^ (n + 1)))).hom)
      (fun n ↦ by
        apply Mod.hom_ext
        simp only [Functor.comp_map, coefficientIntegralTwistSystem,
          Functor.ofOpSequence_map_homOfLE_succ, tensorDiagram, Functor.prod'_map,
          nativeCoefficientSystem, Mod.comp_hom']
        dsimp only [freeRestrictionIso, Mod.isoMk, externalTensor, Mod.tensorRight,
          Mod.tensorRightMap]
        simp only [Mod.comp_hom']
        change (coefficientIntegralTwistTransition l E X n).hom ≫ 𝟙 _ =
          𝟙 _ ≫ (coefficientMap (twistFiniteReduction l E n) X ▷ _ ≫
            _ ◁ (positiveRoots X l).map (homOfLE n.le_succ).op)
        rw [Category.comp_id, Category.id_comp]
        have h := (coefficientFreeTensor_linear
          (coefficientMap (twistReduction l E (n + 1)) X)
          (coefficientMap (twistReduction l E n) X)
          (coefficientMap (twistFiniteReduction l E n) X) (twistReduction_comp l E X n)
          (eqToHom (by rw [pow_succ'] :
            rootsOfUnitySheaf X (l ^ (n + 2)) = rootsOfUnitySheaf X (l * l ^ (n + 1))) ≫
            rootsOfUnitySheafPow X (l ^ (n + 1)) l)).exists.choose_spec
        change (coefficientIntegralTwistTransition l E X n).hom = _ at h
        rw [positiveRoots_map]
        convert h using 1
        rfl)
  have (n : ℕᵒᵖ) : IsIso (t.app n) := inferInstanceAs
    (IsIso (freeRestrictionIso (coefficientMap (twistReduction l E n.unop) X)
      (rootsOfUnitySheaf X (l ^ (n.unop + 1)))).hom)
  exact NatIso.ofComponents (fun n ↦ asIso (t.app n)) (fun f ↦ t.naturality f)

private theorem generator_transition (X : Scheme.{u}) (l n : ℕ) :
    cyclicGenerator X (l ^ (n + 2)) ≫
      (positiveConstants X l).map (homOfLE n.le_succ).op =
        cyclicGenerator X (l ^ (n + 1)) := by
  have h : AddCommGrpCat.intResidue.{u} (l ^ (n + 2)) ≫
      integralResidueAbTransition l (n + 1) =
        AddCommGrpCat.intResidue (l ^ (n + 1)) := by
    ext x
    change ZMod.castHom (pow_dvd_pow l (Nat.le_add_right (n + 1) 1)) _
      (x.down : ZMod (l ^ (n + 2))) = (x.down : ZMod (l ^ (n + 1)))
    simp
  rw [positiveConstants_map]
  simp only [cyclicGenerator, Category.assoc, ← Functor.map_comp, h]

private def constantTensorIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    nativeCoefficientSystem l E X ≅ tensorDiagram
      (condensedRingObj (twistIntegralRing l E) X) (nativeCoefficientSystem l E X)
        (positiveConstants X l) := by
  let R := condensedRingObj (twistIntegralRing l E) X
  let c (n : ℕ) : nativeCoefficientLevel l E X n ≅
      (Mod.tensorRight R ((positiveConstants X l).obj (op n))).obj
        (nativeCoefficientLevel l E X n) :=
    ((Mod.comap (coefficientMap (twistReduction l E n) X)).mapIso
      (freeConstantResidueIso (condensedRingObj (twistFiniteRing l E n) X)
        (l ^ (n + 1)) (finiteRing_nsmul l E X n))).symm ≪≫
      freeRestrictionIso (coefficientMap (twistReduction l E n) X) _
  have hc (n : ℕ) : (c n).hom.hom =
      (ρ_ (condensedRingObj (twistFiniteRing l E n) X)).inv ≫
        _ ◁ cyclicGenerator X (l ^ (n + 1)) := by
    dsimp only [c, Iso.trans_hom, Iso.symm_hom, Functor.mapIso, freeRestrictionIso,
      Mod.isoMk, Mod.comap]
    simp only [Mod.comp_hom']
    exact freeConstantResidueIso_inv (condensedRingObj (twistFiniteRing l E n) X)
        (l ^ (n + 1)) (finiteRing_nsmul l E X n)
  let t : nativeCoefficientSystem l E X ⟶ tensorDiagram R (nativeCoefficientSystem l E X)
      (positiveConstants X l) := NatTrans.ofOpSequence (fun n ↦ (c n).hom) (fun n ↦ by
    apply Mod.hom_ext
    simp only [tensorDiagram, Functor.comp_map, nativeCoefficientSystem,
      Functor.prod'_map, Functor.ofOpSequence_map_homOfLE_succ, Mod.comp_hom']
    dsimp only [externalTensor, Mod.tensorRight, Mod.tensorRightMap]
    simp only [Mod.comp_hom']
    change coefficientMap (twistFiniteReduction l E n) X ≫ (c n).hom.hom =
      (c (n + 1)).hom.hom ≫ (coefficientMap (twistFiniteReduction l E n) X ▷ _ ≫
        _ ◁ (positiveConstants X l).map (homOfLE n.le_succ).op)
    rw [hc n, hc (n + 1)]
    exact tensorGenerator_naturality (coefficientMap (twistFiniteReduction l E n) X)
      (cyclicGenerator X (l ^ (n + 2))) (cyclicGenerator X (l ^ (n + 1)))
      ((positiveConstants X l).map (homOfLE n.le_succ).op)
      (generator_transition X l n))
  have (n : ℕᵒᵖ) : IsIso (t.app n) := inferInstanceAs (IsIso (c n.unop).hom)
  exact NatIso.ofComponents (fun n ↦ asIso (t.app n)) (fun f ↦ t.naturality f)

private def pullExternalIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (M : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    ((upperStar Ab.{u + 1} f).mapMod R).obj ((Mod.tensorRight R M).obj P) ≅
      (Mod.tensorRight ((upperStar Ab.{u + 1} f).obj R)
        ((upperStar Ab.{u + 1} f).obj M)).obj
          (((upperStar Ab.{u + 1} f).mapMod R).obj P) := by
  let F := upperStar Ab.{u + 1} f
  refine Mod.isoMk (asIso (Functor.LaxMonoidal.μ F P.X M)).symm ?_
  change (Functor.LaxMonoidal.μ F R (P.X ⊗ M) ≫
      F.map ((α_ R P.X M).inv ≫ Mod.act P.X ▷ M)) ≫ inv (Functor.LaxMonoidal.μ F P.X M) =
    F.obj R ◁ inv (Functor.LaxMonoidal.μ F P.X M) ≫
      (α_ (F.obj R) (F.obj P.X) (F.obj M)).inv ≫
        (Functor.LaxMonoidal.μ F R P.X ≫ F.map (Mod.act P.X)) ▷ F.obj M
  rw [← cancel_mono (Functor.LaxMonoidal.μ F P.X M)]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, comp_whiskerRight,
    Functor.LaxMonoidal.μ_natural_left, Functor.map_comp]
  rw [← Functor.LaxMonoidal.associativity_inv_assoc,
    ← whiskerLeft_comp_assoc, IsIso.inv_hom_id, whiskerLeft_id, Category.id_comp]

private def tensorPullIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (B : ℕᵒᵖ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (D : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    tensorDiagram R B D ⋙ (upperStar Ab.{u + 1} f).mapMod R ≅
      tensorDiagram ((upperStar Ab.{u + 1} f).obj R)
        (B ⋙ (upperStar Ab.{u + 1} f).mapMod R) (D ⋙ upperStar Ab.{u + 1} f) := by
  let F := upperStar Ab.{u + 1} f
  refine NatIso.ofComponents (fun n ↦ pullExternalIso f R (B.obj n) (D.obj n)) ?_
  intro n m g
  apply Mod.hom_ext
  dsimp only [tensorDiagram, Functor.comp_map, Functor.prod'_map, externalTensor,
    Mod.tensorRight, Mod.tensorRightMap, pullExternalIso, Mod.isoMk, Mod.homMk,
    Functor.mapMod, Functor.prod'_obj]
  simp only [Mod.comp_hom']
  change F.map ((B.map g).hom ▷ _ ≫ _ ◁ D.map g) ≫
      inv (Functor.LaxMonoidal.μ F _ _) =
    inv (Functor.LaxMonoidal.μ F _ _) ≫
      (F.map (B.map g).hom ▷ _ ≫ _ ◁ F.map (D.map g))
  rw [← cancel_mono (Functor.LaxMonoidal.μ F (B.obj m).X (D.obj m))]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← cancel_epi (Functor.LaxMonoidal.μ F (B.obj n).X (D.obj n)),
    ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  exact (Functor.LaxMonoidal.μ_natural F (B.map g).hom (D.map g)).symm

private theorem weaklyEtale_preservesLimits {X Y : Scheme.{u}} (f : Y ⟶ X)
    [WeaklyEtale f] (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    PreservesLimitsOfShape ℕᵒᵖ ((upperStar Ab.{u + 1} f).mapMod R) := by
  let F := upperStar Ab.{u + 1} f
  have : PreservesLimitsOfShape ℕᵒᵖ (localizationRestriction Ab.{u + 1} f
      (inferInstance : WeaklyEtale f)) := by
    unfold localizationRestriction
    infer_instance
  have : PreservesLimitsOfShape ℕᵒᵖ F :=
    preservesLimitsOfShape_of_natIso
      (upperStarIsoLocalizationRestriction Ab.{u + 1} f inferInstance).symm
  have : PreservesLimitsOfShape ℕᵒᵖ (F.mapMod R ⋙ Mod.forget (F.obj R)) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ (Mod.forget R ⋙ F))
  have : ReflectsLimitsOfShape ℕᵒᵖ (Mod.forget (F.obj R) :
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (F.obj R) ⥤ _) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves (F.mapMod R) (Mod.forget (F.obj R))

end AlgebraicGeometry.ProEtale
