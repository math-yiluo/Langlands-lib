/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientMaps
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistLevelsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowCokernel

/-! # Finite-level scalar comparison for the integral root tower

Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-integral-root-level-scalars).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

section TensorHelpers

variable {C : Type*} [Category C] [MonoidalCategory C]

private theorem freeUnit_tensorMap
    {R S : C} [MonObj R] [MonObj S] (a : R ⟶ S) [IsMonHom a]
    {M N : C} (f : M ⟶ N) :
    (Mod.freeForgetAdjunction R).unit.app M ≫ (a ⊗ₘ f) =
      f ≫ (Mod.freeForgetAdjunction S).unit.app N := by
  change ((λ_ M).inv ≫ MonObj.one ▷ M ≫ 𝟙 _) ≫ (a ⊗ₘ f) =
    f ≫ (λ_ N).inv ≫ MonObj.one ▷ N ≫ 𝟙 _
  simp only [Category.comp_id]
  rw [MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, IsMonHom.one_hom,
    ← MonoidalCategory.whisker_exchange]
  rw [← Category.assoc, ← MonoidalCategory.leftUnitor_inv_naturality]
  rw [Category.assoc]

private def freeScalarMap
    {R S : C} [MonObj R] [MonObj S] (a : R ⟶ S) [IsMonHom a] (M : C) :
    (Mod.free R).obj M ⟶ (Mod.comap a).obj ((Mod.free S).obj M) :=
  (Mod.comapId R).inv.app _ ≫
    (spFreeTensor_linear (𝟙 R) a a (Category.id_comp a) (𝟙 M)).choose

private theorem freeScalarMap_hom
    {R S : C} [MonObj R] [MonObj S] (a : R ⟶ S) [IsMonHom a] (M : C) :
    (freeScalarMap a M).hom = a ▷ M := by
  simp only [freeScalarMap, Mod.comp_hom', Mod.comapId_inv_app_hom, Category.id_comp]
  rw [(spFreeTensor_linear (𝟙 R) a a (Category.id_comp a) (𝟙 M)).choose_spec.1]
  exact tensorHom_id _ _

variable [BraidedCategory C] [HasCoequalizers C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]

private def extendFreeIso
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (a : R ⟶ S) [IsMonHom a] (M : C) :
    (Mod.extendScalars a).obj ((Mod.free R).obj M) ≅ (Mod.free S).obj M :=
  (((Mod.freeForgetAdjunction R).comp (Mod.extendRestrictAdjunction a)).leftAdjointUniq
    (Mod.freeForgetAdjunction S)).app M

private theorem extendFreeIso_unit
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (a : R ⟶ S) [IsMonHom a] (M : C) :
    Mod.extendUnitHom a ((Mod.free R).obj M) ≫ (extendFreeIso a M).hom.hom = a ▷ M := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((Mod.freeForgetAdjunction R).comp (Mod.extendRestrictAdjunction a))
    (Mod.freeForgetAdjunction S) M
  rw [Adjunction.comp_homEquiv] at h
  have he : (Mod.extendRestrictAdjunction a).homEquiv _ _ (extendFreeIso a M).hom =
      freeScalarMap a M := by
    apply ((Mod.freeForgetAdjunction R).homEquiv M _).injective
    rw [show (Mod.freeForgetAdjunction R).homEquiv M _
        ((Mod.extendRestrictAdjunction a).homEquiv _ _ (extendFreeIso a M).hom) =
        (Mod.freeForgetAdjunction S).unit.app M from h]
    rw [Adjunction.homEquiv_unit]
    change _ = (Mod.freeForgetAdjunction R).unit.app M ≫ (freeScalarMap a M).hom
    rw [freeScalarMap_hom]
    simpa only [tensorHom_id, Category.id_comp] using (freeUnit_tensorMap a (𝟙 M)).symm
  rw [Adjunction.homEquiv_unit] at he
  have he' := congrArg Mod.Hom.hom he
  simpa only [Mod.comp_hom', Mod.extendRestrictAdjunction_unit_app_hom,
    Mod.comap_map_hom, freeScalarMap_hom] using he'

end TensorHelpers

private theorem reduction_cokernel (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (n : ℕ) :
    ∃ h : (l ^ (n + 1) • 𝟙 _) ≫ spEllPointReduction.{u} l E n = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (spEllPointReduction.{u} l E n) h)) := by
  classical
  let := PadicAlgCl.normedFieldOfAlgebra l E.1
  let R := PadicAlgCl.integers l E.1
  let B := spEllQuotient l E n
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let : IsTopologicalRing B := DiscreteTopology.topologicalRing
  let q : R →+* B := Ideal.Quotient.mk (spTateEllIdeal l E n)
  have hN : (l ^ (n + 1) : B) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  let p := spEllPointReduction.{u} l E n
  have hz : (l ^ (n + 1) • 𝟙 _) ≫ p = 0 := by
    ext S f
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    change q (l ^ (n + 1) • f.down s) = 0
    rw [nsmul_eq_mul, map_mul, map_natCast, Nat.cast_pow, hN, zero_mul]
  refine ⟨hz, ⟨Sheaf.isColimitCokernelCoforkOfSurjective _ p hz ?_ ?_⟩⟩
  · intro S b
    let t : C(B, R) := ⟨Function.surjInv (Ideal.Quotient.mk_surjective),
      continuous_of_discreteTopology⟩
    refine ⟨ULift.up (t.comp b.down), ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    exact Function.rightInverse_surjInv (Ideal.Quotient.mk_surjective) (b.down s)
  · intro S b hb
    have hb' (s : S.unop) : q (b.down s) = 0 := by
      exact congrArg (fun z ↦ z.down s) hb
    choose c hc using fun s ↦ PadicAlgCl.exists_natCast_pow_mul_eq l E.1 (n + 1)
      (b.down s) (hb' s)
    have he := PadicAlgCl.isEmbedding_natCast_pow_mul l E.1 (n + 1)
    have hcont : Continuous c := he.isInducing.continuous_iff.mpr (by
      simpa only [Function.comp_def, hc] using b.down.continuous)
    refine ⟨ULift.up ⟨c, hcont⟩, ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    change (l ^ (n + 1) : ℕ) • c s = b.down s
    simpa only [nsmul_eq_mul, Nat.cast_pow] using hc s

private theorem reduction_tensor_isIso (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) (n : ℕ) :
    IsIso (spEllReduction X l E n ▷
      Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))) := by
  obtain ⟨hz, ⟨hc⟩⟩ := reduction_cokernel.{u} l E n
  let P := upperStarFromPoint X
  let M := Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))
  have : P.IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  have : P.Additive := rightExactFunctor_le_additiveFunctor _ _ _ (by
    rw [rightExactFunctor_iff]
    infer_instance)
  let c := CokernelCofork.ofπ (spEllPointReduction.{u} l E n) hz
  have hp := CokernelCofork.mapIsColimit c hc P
  have ht := CokernelCofork.mapIsColimit (c.map P) hp (tensorRight M)
  apply CokernelCofork.IsColimit.isIso_π _ ht
  have hm : l ^ (n + 1) • 𝟙 M = 0 := by
    ext U x
    exact Scheme.proEtaleRootsOfUnity_nsmul X (l ^ (n + 1)) U x
  change P.map (l ^ (n + 1) • 𝟙 _) ▷ M = 0
  rw [Functor.map_nsmul, P.map_id]
  calc
    _ = P.obj (Profinite.padicIntegersRingObj l E.1) ◁
        (l ^ (n + 1) • 𝟙 M) := by
      simp only [nsmul_whiskerRight, id_whiskerRight, whiskerLeft_nsmul, whiskerLeft_id]
    _ = 0 := by rw [hm, MonoidalPreadditive.whiskerLeft_zero]

private theorem bottomMap_isIso (l : ℕ) [Fact l.Prime] :
    IsIso (integralMap.{u} l (bottomField l)) := by
  obtain ⟨e, eInt, _, heInt, _, _, _, _, q, z, _, _, hz, _, _⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} l
  have h : integralMap.{u} l (bottomField l) = z.hom.hom := by
    ext S a
    apply ULift.ext
    apply ContinuousMap.ext
    intro t
    exact (congrArg (fun f : ℤ_[l] →+* _ ↦ f (a.down t)) heInt).symm.trans
      (hz S.unop a.down t).symm
  rw [h]
  infer_instance

private theorem integralMap_comp (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) :
    coefficientMap (integralMap l (bottomField l)) X ≫
        spIntegersMap X l (show (bottomField l).1 ≤ E.1 from bot_le) =
      coefficientMap (integralMap l E) X := by
  let h : (bottomField l).1 ≤ E.1 := bot_le
  let := PadicAlgCl.normedFieldOfAlgebra l E.1
  let := PadicAlgCl.normedFieldOfAlgebra l (bottomField l).1
  let j : PadicAlgCl.integers l (bottomField l).1 →+* PadicAlgCl.integers l E.1 :=
    ((IntermediateField.inclusion h).toRingHom.comp
      (PadicAlgCl.integers l (bottomField l).1).subtype).codRestrict _ (fun x ↦ x.2)
  have hj : Continuous j :=
    Continuous.subtype_mk
      ((continuous_induced_rng (f := algebraMap E.1 (PadicAlgCl l))).mpr
        (show Continuous fun x : PadicAlgCl.integers l (bottomField l).1 ↦
          algebraMap (bottomField l).1 (PadicAlgCl l) (x : (bottomField l).1) from
          continuous_induced_dom.comp continuous_subtype_val)) _
  let b := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap j hj)
  have hb : b ≫ padicIntegersRingObjToContinuousMapRingObj l E =
      padicIntegersRingObjToContinuousMapRingObj l (bottomField l) ≫
        Profinite.padicSubfieldRingObjMap l h := rfl
  have hi : coefficientMap b X = spIntegersMap X l h := by
    apply (spIntegersMap_existsUnique X l h).unique
    · refine ⟨inferInstance, ?_⟩
      simpa only [← coefficientMap_comp] using congrArg (fun f ↦ coefficientMap f X) hb
    · exact spIntegersMap_spec X l h
  rw [← hi, ← coefficientMap_comp]
  congr 1

private def levelFreeMap (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) (n : ℕ) :
    (Mod.free (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X)).obj
        (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))) ⟶
      spIntegralTwistLevel X l E n :=
  freeScalarMap (spEllReduction X l E n) _

private instance levelFreeMap_isIso (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) (n : ℕ) :
    IsIso (levelFreeMap l E X n) := by
  have : IsIso ((Mod.forget _).map (levelFreeMap l E X n)) := by
    change IsIso (levelFreeMap l E X n).hom
    rw [levelFreeMap, freeScalarMap_hom]
    exact reduction_tensor_isIso l E X n
  exact isIso_of_reflects_iso (levelFreeMap l E X n) (Mod.forget _)

private def bottomLevelFreeMap (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (n : ℕ) :
    (Mod.free (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X)).obj
        (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))) ⟶
      (Mod.comap (coefficientMap (integralMap l (bottomField l)) X)).obj
        (spIntegralTwistLevel X l (bottomField l) n) :=
  freeScalarMap (coefficientMap (integralMap l (bottomField l)) X) _ ≫
    (Mod.comap (coefficientMap (integralMap l (bottomField l)) X)).map
      (levelFreeMap l (bottomField l) X n)

private instance bottomLevelFreeMap_isIso (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (n : ℕ) : IsIso (bottomLevelFreeMap l X n) := by
  have : IsIso (integralMap.{u} l (bottomField l)) := bottomMap_isIso l
  have : IsIso (coefficientMap (integralMap l (bottomField l)) X) :=
    (upperStarFromPoint X).map_isIso _
  have : IsIso (freeScalarMap (coefficientMap (integralMap l (bottomField l)) X)
      (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)))) := by
    have : IsIso ((Mod.forget _).map
        (freeScalarMap (coefficientMap (integralMap l (bottomField l)) X)
          (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))))) := by
      change IsIso (freeScalarMap _ _).hom
      rw [freeScalarMap_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  let : IsIso (levelFreeMap l (bottomField l) X n) :=
    levelFreeMap_isIso l (bottomField l) X n
  unfold bottomLevelFreeMap
  refine IsIso.comp_isIso' inferInstance ?_
  exact (Mod.comap (coefficientMap (integralMap l (bottomField l)) X)).map_isIso
    (levelFreeMap l (bottomField l) X n)

private def levelIso (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) (n : ℕ) :
    (Mod.extendScalars (coefficientMap (integralMap l E) X)).obj
        ((Mod.comap (coefficientMap (integralMap l (bottomField l)) X)).obj
          (spIntegralTwistLevel X l (bottomField l) n)) ≅ spIntegralTwistLevel X l E n :=
  (Mod.extendScalars (coefficientMap (integralMap l E) X)).mapIso
      (asIso (bottomLevelFreeMap l X n)).symm ≪≫
    extendFreeIso (coefficientMap (integralMap l E) X) _ ≪≫
      asIso (levelFreeMap l E X n)

private theorem levelIso_unit (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) (n : ℕ) :
    Mod.extendUnitHom (coefficientMap (integralMap l E) X)
        ((Mod.comap (coefficientMap (integralMap l (bottomField l)) X)).obj
          (spIntegralTwistLevel X l (bottomField l) n)) ≫
      (levelIso l E X n).hom.hom =
    spEllMap X l (show (bottomField l).1 ≤ E.1 from bot_le) n ⊗ₘ
      𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))) := by
  let a := coefficientMap (integralMap l E) X
  let a₀ := coefficientMap (integralMap l (bottomField l)) X
  let M := Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))
  let c := bottomLevelFreeMap l X n
  apply (cancel_epi c.hom).mp
  change c.hom ≫ (Mod.extendUnitHom a _ ≫
      (Mod.extendScalarsMap a (inv c)).hom ≫ (extendFreeIso a M).hom.hom ≫
        (levelFreeMap l E X n).hom) = _
  rw [Mod.extendUnitHom_extendScalarsMap_assoc]
  rw [← Category.assoc c.hom, ← Mod.comp_hom', IsIso.hom_inv_id,
    Mod.id_hom', Category.id_comp, ← Category.assoc, extendFreeIso_unit]
  simp only [c, bottomLevelFreeMap, Mod.comp_hom', Mod.comap_map_hom,
    levelFreeMap, freeScalarMap_hom, ← comp_whiskerRight, tensorHom_id]
  rw [Category.assoc, spEllMap_spec, ← Category.assoc,
    integralMap_comp]

/-- Scalar extension identifies the finite root levels and their transition maps.
The comparison is fixed on the ordinary scalar unit, before taking any limit.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), applied at each
positive ell-power quotient; sec-proetale-coefficients/sk-def-sp-tate-twist/
_section.md, finite-level tensor formulas.
(blueprint: lem-diagonal-integral-root-level-scalars).

Proof: Put N = l^(n+1). The actual condensed reduction O_E -> O_E/N is the
cokernel of multiplication by N. On each profinite test, quotient-valued
continuous functions lift through a continuous choice of representatives in
the discrete quotient. A continuous function in the kernel divides by N
continuously, because multiplication by N is an embedding of O_E. The
sectionwise cokernel criterion supplies the condensed cokernel. Pullback to
X and tensoring with mu_N preserve it. The first map then vanishes because
N annihilates mu_N, so the tensor reduction is an isomorphism.
The bottom integral coefficient map is an isomorphism by the normalized
base coefficient identification. Hence the restricted bottom finite twist
is the free Z_l,X-module on mu_N. Uniqueness of left adjoints identifies its
extension to O_E,X with the free O_E,X-module on mu_N, and the tensor reduction
identifies that module with the actual finite twist for E. The adjunction
unit equation and the defining reduction square for spEllMap give exactly
the stated normalization. The successive reduction squares commute after
cancelling the epic integral reduction. Tensor these squares with the root
power maps; injectivity of the extension-unit Hom correspondence then gives
naturality of the level comparisons. They therefore assemble into the
required tower isomorphism. No inverse limit, flatness of the root-limit
line, or derived comparison is used. The same universal properties apply
to an empty scheme and to the bottom field itself. -/
theorem diagonalIntegral_rootLevelScalars (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) :
    ∃ i : (spIntegralTwistSystem X l (bottomField l) ⋙
        Mod.comap (coefficientMap (integralMap l (bottomField l)) X)) ⋙
          Mod.extendScalars (coefficientMap (integralMap l E) X) ≅
        spIntegralTwistSystem X l E,
      ∀ n : ℕ,
        Mod.extendUnitHom (coefficientMap (integralMap l E) X)
            ((Mod.comap (coefficientMap (integralMap l (bottomField l)) X)).obj
              (spIntegralTwistLevel X l (bottomField l) n)) ≫
          (i.hom.app (op n)).hom =
        spEllMap X l (show (bottomField l).1 ≤ E.1 from bot_le) n ⊗ₘ
          𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))) := by
  have hred (K : PadicAlgCl.FiniteIntermediateField l) (n : ℕ) :
      spEllReduction X l K (n + 1) ≫
          coefficientMap (spEllPointTransition l K n) X = spEllReduction X l K n := by
    rw [← coefficientMap_comp]
    apply congrArg (fun f ↦ coefficientMap f X)
    unfold spEllPointReduction spEllPointTransition
    rw [← Functor.map_comp]
    rfl
  have ht (n : ℕ) :
      spEllMap X l (show (bottomField l).1 ≤ E.1 from bot_le) (n + 1) ≫
          coefficientMap (spEllPointTransition l E n) X =
        coefficientMap (spEllPointTransition l (bottomField l) n) X ≫
          spEllMap X l (show (bottomField l).1 ≤ E.1 from bot_le) n := by
    have := spEllReduction_epi X l (bottomField l) (n + 1)
    apply (cancel_epi (spEllReduction X l (bottomField l) (n + 1))).mp
    rw [← Category.assoc, spEllMap_spec, Category.assoc, hred E n,
      ← Category.assoc, hred (bottomField l) n, spEllMap_spec]
  let τ : (spIntegralTwistSystem X l (bottomField l) ⋙
        Mod.comap (coefficientMap (integralMap l (bottomField l)) X)) ⋙
          Mod.extendScalars (coefficientMap (integralMap l E) X) ⟶
        spIntegralTwistSystem X l E :=
    NatTrans.ofOpSequence (fun n ↦ (levelIso l E X n).hom) (by
      intro n
      simp only [Functor.comp_map, spIntegralTwistSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply Mod.extendScalarsObj_hom_ext'
      change Mod.extendUnitHom (coefficientMap (integralMap l E) X) _ ≫
          ((Mod.extendScalarsMap (coefficientMap (integralMap l E) X)
            ((Mod.comap (coefficientMap (integralMap l (bottomField l)) X)).map
              (spIntegralLevelTransition X l (bottomField l) n))).hom ≫
                (levelIso l E X n).hom.hom) =
        Mod.extendUnitHom (coefficientMap (integralMap l E) X) _ ≫
          ((levelIso l E X (n + 1)).hom.hom ≫
            (spIntegralLevelTransition X l E n).hom)
      rw [Mod.extendUnitHom_extendScalarsMap_assoc, levelIso_unit,
        ← Category.assoc, levelIso_unit]
      change (spIntegralLevelTransition X l (bottomField l) n).hom ≫ _ =
        _ ≫ (spIntegralLevelTransition X l E n).hom
      dsimp only [spIntegralLevelTransition]
      rw [(spIntegralLevelTransition_existsUnique X l (bottomField l) n).exists.choose_spec,
        (spIntegralLevelTransition_existsUnique X l E n).exists.choose_spec,
        tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id, ht n])
  have : ∀ n, IsIso (τ.app n) := fun n ↦
    inferInstanceAs (IsIso (levelIso l E X n.unop).hom)
  have := NatIso.isIso_of_isIso_app τ
  refine ⟨asIso τ, fun n ↦ ?_⟩
  exact levelIso_unit l E X n

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
