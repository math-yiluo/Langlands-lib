/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import WeilConjectures.AlgebraicGeometry.Affine.AffineRootsRepresentability
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralBasis
import all WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreePowerIso
import WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeSectionBasis
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Sites.PreservesLimits

/-! # Finite étale representation of the native finite Tate diagram
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

private theorem globalPrimeUnit (Y : Scheme.{u}) (ℓ : ℕ)
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] : IsUnit (ℓ : Γ(Y, ⊤)) := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ
  intro y hy
  rw [map_natCast]
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  change (Y.residue y).hom (ℓ : Y.presheaf.stalk y) ≠ 0
  simpa only [map_natCast] using (isUnit_of_invertible (ℓ : Y.residueField y)).ne_zero

private theorem roots_representation (Y : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hunit : IsUnit (N : Γ(Y, ⊤))) :
    ∃ V : Y.ProEt, IsFinite V.hom ∧ Etale V.hom ∧
      Nonempty ((Scheme.ProEt.topology Y).uliftYoneda.{u + 1}.obj V ≅
        (sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})).obj
          (Scheme.proEtaleRootsOfUnitySheaf Y N)) := by
  classical
  let R := Γ(Y, ⊤)
  let P := affineRootsOver R N
  have hmonic : ((Polynomial.X : Polynomial R) ^ N - 1).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : R) hN.ne'
  have : IsFinite P.hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R _)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hmonic.finite_adjoinRoot
  have : Etale P.hom := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap R _)))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    apply RingHom.etale_algebraMap.mpr
    simpa only [Polynomial.C_1] using
      AdjoinRoot.etale_X_pow_sub_C hN.ne' hunit (isUnit_one : IsUnit (1 : R))
  let W := (Over.pullback Y.toSpecΓ).obj P
  let : IsFinite W.hom := inferInstanceAs (IsFinite (pullback.snd P.hom Y.toSpecΓ))
  let : Etale W.hom := inferInstanceAs (Etale (pullback.snd P.hom Y.toSpecΓ))
  let V : Y.ProEt := Scheme.ProEt.mk W.hom
  obtain ⟨_, _, _, _, _, _, _, hbase⟩ := affineRoots_representability R N hN
  obtain ⟨e, _, hnat, _⟩ := hbase Y Y.toSpecΓ
  let a (U : Y.ProEtᵒᵖ) :
      (U.unop ⟶ V) ≃ ((Scheme.ProEt.forget Y).obj U.unop ⟶ W) :=
    { toFun := fun f ↦ Over.homMk f.left f.w
      invFun := fun f ↦ MorphismProperty.Over.homMk f.left f.w
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let b (U : Y.ProEtᵒᵖ) :
      {z : Γ(U.unop.left, ⊤)ˣ // z ^ N = 1} ≃
        Additive (rootsOfUnity N Γ(U.unop.left, ⊤)) :=
    { toFun := fun z ↦ Additive.ofMul ⟨z.val, (mem_rootsOfUnity N _).mpr z.property⟩
      invFun := fun z ↦ ⟨z.toMul.val, (mem_rootsOfUnity N _).mp z.toMul.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let k (U : Y.ProEtᵒᵖ) :
      ULift.{u + 1} (U.unop ⟶ V) ≃
        (Scheme.proEtaleRootsOfUnitySheaf Y N).obj.obj U :=
    Equiv.ulift.trans ((a U).trans ((e _).trans
      ((b U).trans (Scheme.proEtaleRootsOfUnitySections Y N U).toEquiv.symm)))
  let j : ((Scheme.ProEt.topology Y).uliftYoneda.{u + 1}.obj V).obj ≅
      ((sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})).obj
        (Scheme.proEtaleRootsOfUnitySheaf Y N)).obj :=
    NatIso.ofComponents (fun U ↦ (k U).toIso) (by
      intro U U' f
      ext x
      apply (Scheme.proEtaleRootsOfUnitySections Y N U').injective
      apply Additive.toMul.injective
      apply Subtype.ext
      have hi := NatTrans.naturality_apply
        (Scheme.proEtaleRootsOfUnityInclusion Y N).hom f (k U x)
      have hu := (Scheme.existsUnique_proEtaleRootsOfUnitySections Y N U).exists.choose_spec
        (k U x)
      have hv := (Scheme.existsUnique_proEtaleRootsOfUnitySections Y N U').exists.choose_spec
        ((Scheme.proEtaleRootsOfUnitySheaf Y N).obj.map f (k U x))
      have hk (T : Y.ProEtᵒᵖ) (z : ULift.{u + 1} (T.unop ⟶ V)) :
          (Scheme.proEtaleRootsOfUnitySections Y N T (k T z)).toMul.val =
            (e _ (a T z.down)).val := by
        dsimp [k, b]
        exact congrArg (fun z ↦ z.toMul.val)
          ((Scheme.proEtaleRootsOfUnitySections Y N T).apply_symm_apply _)
      have hr : (Scheme.proEtaleRootsOfUnitySections Y N U'
          ((Scheme.proEtaleRootsOfUnitySheaf Y N).obj.map f (k U x))).toMul.val =
          Units.map f.unop.left.appTop.hom.toMonoidHom
            (Scheme.proEtaleRootsOfUnitySections Y N U (k U x)).toMul.val := by
        rw [← hu, ← hv] at hi
        exact congrArg (fun z ↦ z.down.toMul) hi
      change (Scheme.proEtaleRootsOfUnitySections Y N U'
          (k U' ⟨f.unop ≫ x.down⟩)).toMul.val =
        (Scheme.proEtaleRootsOfUnitySections Y N U'
          ((Scheme.proEtaleRootsOfUnitySheaf Y N).obj.map f (k U x))).toMul.val
      exact (hk U' _).trans ((hnat _ _ ((Scheme.ProEt.forget Y).map f.unop)
        (a U x.down)).trans ((congrArg
          (Units.map f.unop.left.appTop.hom.toMonoidHom) (hk U x).symm).trans hr.symm)))
  exact ⟨V, ‹IsFinite W.hom›, ‹Etale W.hom›,
    ⟨(sheafToPresheaf _ _).preimageIso j⟩⟩

private theorem finite_proEt_product {Y : Scheme.{u}} (V W : Y.ProEt)
    [IsFinite V.hom] [IsFinite W.hom] [Etale V.hom] [Etale W.hom] :
    IsFinite (V ⨯ W).hom ∧ Etale (V ⨯ W).hom := by
  let F := Scheme.ProEt.forget Y
  let c := BinaryFan.mk (F.map (prod.fst : V ⨯ W ⟶ V)) (F.map prod.snd)
  have hc : IsLimit c := isLimitOfHasBinaryProductOfPreservesLimit F V W
  have hp := Over.isPullback_of_binaryFan_isLimit c hc
  have he : (V ⨯ W).hom = hp.isoPullback.hom ≫ pullback.fst V.hom W.hom ≫ V.hom := by
    exact (MorphismProperty.Over.w (prod.fst : V ⨯ W ⟶ V)).symm.trans
      (hp.isoPullback_hom_fst_assoc V.hom).symm
  rw [he]
  exact ⟨inferInstance, inferInstance⟩

private theorem finite_proEt_power {Y : Scheme.{u}} (W : Y.ProEt) [IsFinite W.hom] [Etale W.hom]
    (n : ℕ) :
    ∃ c : Fan (fun _ : Fin n ↦ W), Nonempty (IsLimit c) ∧
      IsFinite c.pt.hom ∧ Etale c.pt.hom := by
  induction n with
  | zero =>
    let T : Y.ProEt := Scheme.ProEt.mk (𝟙 Y)
    let c : Fan (fun _ : Fin 0 ↦ W) := Fan.mk T (fun i ↦ Fin.elim0 i)
    have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
    exact ⟨c, ⟨(isLimitEquivIsTerminalOfIsEmpty Y.ProEt c).symm hT⟩,
      inferInstanceAs (IsFinite (𝟙 Y)), inferInstanceAs (Etale (𝟙 Y))⟩
  | succ n ih =>
    obtain ⟨c, ⟨hc⟩, hfin, het⟩ := ih
    let : IsFinite c.pt.hom := hfin
    let : Etale c.pt.hom := het
    let b := BinaryFan.mk (prod.fst : W ⨯ c.pt ⟶ W) prod.snd
    exact ⟨extendFan c b, ⟨extendFanIsLimit (fun _ : Fin (n + 1) ↦ W) hc
      (prodIsProd W c.pt)⟩, finite_proEt_product W c.pt⟩

private theorem roots_power_representation (Y : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hunit : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    ∃ V : Y.ProEt, IsFinite V.hom ∧ Etale V.hom ∧
      Nonempty ((Scheme.ProEt.topology Y).uliftYoneda.{u + 1}.obj V ≅
        ∏ᶜ fun _ : Fin d ↦
          (sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})).obj
            (Scheme.proEtaleRootsOfUnitySheaf Y N)) := by
  obtain ⟨W, hW, hWe, ⟨e⟩⟩ := roots_representation Y N hN hunit
  let : IsFinite W.hom := hW
  let : Etale W.hom := hWe
  obtain ⟨c, ⟨hc⟩, hfin, het⟩ := finite_proEt_power W d
  let F := (Scheme.ProEt.topology Y).uliftYoneda.{u + 1}
  have hFc : IsLimit (Fan.mk (F.obj c.pt) (fun i ↦ F.map (c.proj i))) :=
    isLimitFanMkObjOfIsLimit F _ _ hc
  exact ⟨c.pt, hfin, het,
    ⟨hFc.conePointUniqueUpToIso (productIsProduct _) ≪≫ Pi.mapIso (fun _ ↦ e)⟩⟩

-- The `Module A B` search in the statement explores the slow `ULift.module` branch first.
private theorem quotient_basis (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ)
    (a : ZMod (ℓ ^ (n + 1)) →+* ULift.{u + 1} (spEllQuotient ℓ E n)) :
    let A := ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))
    let B := ULift.{u + 1} (spEllQuotient ℓ E n)
    let : Algebra A B := (a.comp ULift.ringEquiv.toRingHom).toAlgebra
    ∃ d : ℕ, Nonempty (Module.Basis (Fin d) A B) := by
  classical
  let O := Padic.coefficientExtensionIntegers ℓ E.1
  let : Algebra ℤ_[ℓ] O := (Scheme.purTwistIntegersMap ℓ E.1).toAlgebra
  obtain ⟨d, ⟨b⟩⟩ := Scheme.purTwistIntegralBasis ℓ E.1
  let I : Ideal ℤ_[ℓ] := Ideal.span {(ℓ : ℤ_[ℓ]) ^ (n + 1)}
  let Q := O ⧸ I.map (algebraMap ℤ_[ℓ] O)
  let : Algebra (ℤ_[ℓ] ⧸ I) Q :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let eT := Algebra.TensorProduct.quotIdealMapEquivQuotTensor O I
  let eO : O ≃+* PadicAlgCl.integers ℓ E.1 := RingEquiv.subringCongr (spIntegers_eq ℓ E)
  let eQ : Q ≃+* spEllQuotient ℓ E n :=
    Ideal.quotientEquiv _ _ eO (by
      simp only [I, spTateEllIdeal, Ideal.map_span, Set.image_singleton, map_pow, map_natCast])
  let eR : (ℤ_[ℓ] ⧸ I) ≃+* ZMod (ℓ ^ (n + 1)) :=
    (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow (n + 1)).symm).trans
      (RingHom.quotientKerEquivOfSurjective
        (ZMod.ringHom_surjective (PadicInt.toZModPow (n + 1))))
  let e : spEllQuotient ℓ E n ≃+ (Fin d → ZMod (ℓ ^ (n + 1))) :=
    eQ.symm.toAddEquiv.trans (eT.toLinearEquiv.toAddEquiv.trans
      ((b.baseChange (ℤ_[ℓ] ⧸ I)).equivFun.toAddEquiv.trans
        (AddEquiv.piCongrRight fun _ ↦ eR.toAddEquiv)))
  let B := ULift.{u + 1} (spEllQuotient ℓ E n)
  let : Algebra (ZMod (ℓ ^ (n + 1))) B := a.toAlgebra
  let eB : B ≃+ (Fin d → ZMod (ℓ ^ (n + 1))) := ULift.ringEquiv.toAddEquiv.trans e
  let eL : B ≃ₗ[ZMod (ℓ ^ (n + 1))] (Fin d → ZMod (ℓ ^ (n + 1))) :=
    { eB with map_smul' := ZMod.map_smul eB.toAddMonoidHom }
  let A := ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))
  let : Algebra A B := (a.comp ULift.ringEquiv.toRingHom).toAlgebra
  let eA : B ≃ₗ[A] (Fin d → A) :=
    { eB.trans (AddEquiv.piCongrRight fun _ ↦ ULift.ringEquiv.toAddEquiv.symm) with
      map_smul' := by
        intro r x
        ext i
        exact congrArg (fun z ↦ z i) (eL.map_smul r.down x) }
  exact ⟨d, ⟨Module.Basis.ofEquivFun eA⟩⟩

/-- One finite native Tate level is represented by a finite étale scheme.
This involves no tower transitions, infinite limits, or inverse-image functors. -/
theorem spIntegralTwistLevel_finiteEtale_representation
    (Y : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    ∃ V : Y.ProEt, IsFinite V.hom ∧ Etale V.hom ∧
      Nonempty ((Scheme.ProEt.topology Y).uliftYoneda.{u + 1}.obj V ≅
        (sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})).obj
          (spIntegralTwistLevel Y ℓ E n).X) := by
  classical
  obtain ⟨a, ⟨e₀⟩⟩ := spIntegralTwistLevel_comparison Y ℓ E n
  let A := ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))
  let B := ULift.{u + 1} (spEllQuotient ℓ E n)
  let iAB : Algebra A B := (a.comp ULift.ringEquiv.toRingHom).toAlgebra
  let : Module A B := iAB.toModule
  obtain ⟨d, ⟨b⟩⟩ := quotient_basis ℓ E n a
  let iFree : Module.Free A B := Module.Free.of_basis b
  let iFin : Module.Finite A B := Module.Finite.of_basis b
  let J := Scheme.ProEt.topology Y
  obtain ⟨k, β, hβ⟩ := @constantFiniteFree_sectionBasis.{u + 1, u, 0}
    Y.ProEt inferInstance J
    (WeilConjectures.integralCoefficientRingSheafify.{u, 0} Y)
    (inferInstanceAs (J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})))
    (WeilConjectures.integralCoefficientAbSheafify.{u, 0} Y)
    (WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} Y)
    (CommRingCat.of A) (CommRingCat.of B) iAB iFree iFin
  let M := Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (n + 1))
  let U := sheafToPresheaf J AddCommGrpCat.{u + 1}
  let e₁ : U.obj (spIntegralTwistLevel Y ℓ E n).X ≅
      ∏ᶜ (fun _ : Fin k ↦ M.obj) :=
    U.mapIso e₀ ≪≫ CategoryTheory.sheafifiedTensorIso
      (Scheme.tateFiniteScalar Y ℓ B n a) k β hβ (Scheme.purTwistRootsModule Y ℓ n)
  let e₂ : (spIntegralTwistLevel Y ℓ E n).X ≅ ∏ᶜ (fun _ : Fin k ↦ M) :=
    U.preimageIso (e₁ ≪≫ (asIso (piComparison U (fun _ : Fin k ↦ M))).symm)
  let F := sheafCompose J (forget AddCommGrpCat.{u + 1})
  let : PreservesLimitsOfShape (Discrete (Fin k)) (F ⋙ sheafToPresheaf J _) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete (Fin k))
      (sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{u + 1})))
  let : PreservesLimitsOfShape (Discrete (Fin k)) F :=
    preservesLimitsOfShape_of_reflects_of_preserves F (sheafToPresheaf J _)
  let e₃ : F.obj (spIntegralTwistLevel Y ℓ E n).X ≅
      ∏ᶜ (fun _ : Fin k ↦ F.obj M) :=
    F.mapIso e₂ ≪≫ asIso (piComparison F (fun _ : Fin k ↦ M))
  have hp : 0 < ℓ ^ (n + 1) := pow_pos (Fact.out : ℓ.Prime).pos _
  have hu : IsUnit ((ℓ ^ (n + 1) : ℕ) : Γ(Y, ⊤)) := by
    simpa only [Nat.cast_pow] using (globalPrimeUnit Y ℓ).pow (n + 1)
  obtain ⟨V, hfin, het, ⟨eV⟩⟩ := roots_power_representation Y _ hp hu k
  exact ⟨V, hfin, het, ⟨eV ≪≫ e₃.symm⟩⟩

end AlgebraicGeometry.ProEtale
