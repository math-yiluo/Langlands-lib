/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteReduction
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Module.Shrink
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteSlice
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteConstants
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite perfect charts under normalized residue coefficients

## References

* Bhatt--Scholze, Lemma 6.5.8(1) and Proposition 6.6.11
* Bhatt--Scholze, Lemma 6.5.8(1), Proposition 6.6.11
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

private abbrev quotientLift {R : Type (u + 1)} {A : Type u}
    [CommRing R] [CommRing A] (e : R ≃+* A) : ModuleCat.{u} A ⥤ ModuleCat.{u + 1} R :=
  ModuleCat.uliftFunctor.{u + 1, u} A ⋙ ModuleCat.restrictScalars e.toRingHom

private theorem smallPerfectModel
    {R : Type (u + 1)} {A : Type u} [CommRing R] [CommRing A]
    (e : R ≃+* A) (P : CochainComplex (ModuleCat.{u + 1} R) ℤ)
    (hP : @DerivedCategory.IsPerfectRingComplex R _
      (HasDerivedCategory.standard _) (DerivedCategory.Q.obj P)) :
    ∃ B : CochainComplex (ModuleCat.{u} A) ℤ,
      DerivedCategory.IsPerfectRingComplex (DerivedCategory.Q.obj B) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj
        (((quotientLift e).mapHomologicalComplex (.up ℤ)).obj B)) := by
  classical
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  obtain ⟨V, a, b, ha, hb, hV, ⟨eP⟩⟩ := hP
  let := ha
  let := hb
  let : (ModuleCat.restrictScalars.{u + 1} e.toRingHom).Full := by
    constructor
    intro X Y f
    let f' : X →ₗ[A] Y :=
      { toFun := fun x ↦ f.hom x
        map_add' := f.hom.map_add
        map_smul' := by
          intro a x
          change (f.hom (a • x) : Y) = a • (f.hom x : Y)
          have hf := f.hom.map_smul (e.symm a) x
          change (f.hom (e (e.symm a) • x) : Y) =
            e (e.symm a) • (f.hom x : Y) at hf
          simpa only [e.apply_symm_apply] using hf }
    refine ⟨ModuleCat.ofHom f', ?_⟩
    ext x
    rfl
  let F := quotientLift e
  have : F.Full := by
    change (ModuleCat.uliftFunctor.{u + 1, u} A ⋙
      ModuleCat.restrictScalars.{u + 1} e.toRingHom).Full
    infer_instance
  have : F.Faithful := by dsimp [F, quotientLift]; infer_instance
  have : F.Additive := by dsimp [F, quotientLift]; infer_instance
  let G := ModuleCat.restrictScalars.{u + 1} e.symm.toRingHom
  have hN (i : ℤ) : Module.Projective A (G.obj (V.X i)) ∧
      Module.Finite A (G.obj (V.X i)) := by
    let := (hV i).1
    let := (hV i).2
    let se : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
        (V.X i) (G.obj (V.X i)) :=
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro r x
          change r • x = e.symm (e r) • x
          rw [e.symm_apply_apply] }
    exact ⟨Module.Projective.of_equiv se,
      Module.Finite.of_surjective se.toLinearMap se.surjective⟩
  let (i : ℤ) : Module.Projective A (G.obj (V.X i)) := (hN i).1
  let (i : ℤ) : Module.Finite A (G.obj (V.X i)) := (hN i).2
  let (i : ℤ) : Small.{u} (G.obj (V.X i)) := Module.Finite.small A _
  let N (i : ℤ) : ModuleCat.{u} A := ModuleCat.of A (Shrink.{u} (G.obj (V.X i)))
  let eN (i : ℤ) : F.obj (N i) ≅ V.X i :=
    (show F.obj (N i) ≃ₗ[R] V.X i from
      { toFun := fun x ↦ Shrink.linearEquiv A (G.obj (V.X i)) x.down
        invFun := fun x ↦ ULift.up ((Shrink.linearEquiv A (G.obj (V.X i))).symm x)
        left_inv := by intro x; cases x; simp
        right_inv := by intro x; simp
        map_add' := by
          intro x y
          change (Shrink.linearEquiv A (G.obj (V.X i))) (x.down + y.down) =
            (Shrink.linearEquiv A (G.obj (V.X i))) x.down +
              (Shrink.linearEquiv A (G.obj (V.X i))) y.down
          exact map_add _ _ _
        map_smul' := by
          intro r x
          change (Shrink.linearEquiv A (G.obj (V.X i))) (e r • x.down) = _
          rw [map_smul]
          change e.symm (e r) • (show V.X i from
            (Shrink.linearEquiv A (G.obj (V.X i))) x.down) =
              r • (show V.X i from (Shrink.linearEquiv A (G.obj (V.X i))) x.down)
          rw [e.symm_apply_apply] }).toModuleIso
  let B : CochainComplex (ModuleCat.{u} A) ℤ :=
    { X := N
      d := fun i j ↦ F.preimage ((eN i).hom ≫ V.d i j ≫ (eN j).inv)
      shape := by
        intro i j hij
        apply F.map_injective
        simp [V.shape i j hij]
      d_comp_d' := by
        intro i j k _ _
        apply F.map_injective
        simp [Category.assoc] }
  let eB : ((F.mapHomologicalComplex (.up ℤ)).obj B) ≅ V :=
    HomologicalComplex.Hom.isoOfComponents eN (by intros; simp [B, Category.assoc])
  have haB : B.IsStrictlyGE a := by
    apply (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff B F a).1
    exact (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi ↦
      (V.isZero_of_isStrictlyGE a i hi).of_iso (eN i)
  have hbB : B.IsStrictlyLE b := by
    apply (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff B F b).1
    exact (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi ↦
      (V.isZero_of_isStrictlyLE b i hi).of_iso (eN i)
  refine ⟨B, ⟨B, a, b, haB, hbB, ?_, ⟨Iso.refl _⟩⟩,
    ⟨eP ≪≫ (DerivedCategory.Q.mapIso eB).symm⟩⟩
  intro i
  exact ⟨inferInstanceAs (Module.Projective A (Shrink.{u} (G.obj (V.X i)))),
    Module.Finite.of_surjective (Shrink.linearEquiv A (G.obj (V.X i))).symm.toLinearMap
      (Shrink.linearEquiv A (G.obj (V.X i))).symm.surjective⟩

private def finitePullbackComp
    (T S V : Scheme.{u}) (g : S ⟶ T) (h : V ⟶ S)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    finiteCoefficientPullback T Λ (h ≫ g) ≅
      finiteCoefficientPullback T Λ g ⋙ finiteCoefficientPullback S Λ h :=
  Functor.isoWhiskerLeft (finiteCoefficientUnrealization T Λ)
    (Functor.isoWhiskerRight (upperStarComp (ModuleCat.{u + 1} Λ) h g)
      (finiteCoefficientRealization V Λ)) ≪≫
    Functor.isoWhiskerLeft
      (finiteCoefficientUnrealization T Λ ⋙ upperStar (ModuleCat.{u + 1} Λ) g)
      (Functor.isoWhiskerRight (finiteCoefficientRealization S Λ).asEquivalence.unitIso
        (upperStar (ModuleCat.{u + 1} Λ) h ⋙ finiteCoefficientRealization V Λ))

private abbrev finiteConstant (S : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :=
  constantSheaf (ProEt.topology S) (ModuleCat.{u + 1} Λ) ⋙ finiteCoefficientRealization S Λ

private def finiteConstantPullback
    (S V : Scheme.{u}) (h : V ⟶ S)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    finiteConstant S Λ ⋙ finiteCoefficientPullback S Λ h ≅ finiteConstant V Λ := by
  let A := ModuleCat.{u + 1} Λ
  let C := constantSheaf (ProEt.topology S) A
  let R := finiteCoefficientRealization S Λ
  let H := upperStar A h
  let R' := finiteCoefficientRealization V Λ
  let ec : C ⋙ H ≅ constantSheaf (ProEt.topology V) A :=
    Functor.isoWhiskerLeft C
        (Functor.sheafPullbackConstruction.sheafPullbackIso (proEtaleBaseChange h) _
          (ProEt.topology S) (ProEt.topology V)).symm ≪≫
      (proEtaleBaseChange h).constantSheafsheafPullbackIso A
        (ProEt.topology S) (ProEt.topology V) (ProEt.isTerminalMkId S)
        ((ProEt.isTerminalMkId S).isTerminalObj (proEtaleBaseChange h) _)
  exact Functor.isoWhiskerLeft C
      (Functor.isoWhiskerRight R.asEquivalence.unitIso.symm (H ⋙ R')) ≪≫
    Functor.isoWhiskerRight ec R'

private def finiteConstantModelIso
    (S : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (P : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) :
    (finiteCoefficientRealization S Λ).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          (((constantSheaf (ProEt.topology S)
              (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (.up ℤ)).obj P)) ≅
      (finiteConstant S Λ).mapDerivedCategory.obj (DerivedCategory.Q.obj P) :=
  (finiteCoefficientRealization S Λ).mapDerivedCategory.mapIso
      (((constantSheaf (ProEt.topology S)
        (ModuleCat.{u + 1} Λ)).mapDerivedCategoryFactors).app P).symm ≪≫
    (Functor.mapDerivedCategoryCompIso
      (constantSheaf (ProEt.topology S) (ModuleCat.{u + 1} Λ))
      (finiteCoefficientRealization S Λ)).app (DerivedCategory.Q.obj P)

private def finiteConstantDerivedPullback
    (S V : Scheme.{u}) (h : V ⟶ S)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (P : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) :
    (finiteCoefficientDerivedPullback S Λ h).obj
        ((finiteConstant S Λ).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≅
      (finiteConstant V Λ).mapDerivedCategory.obj (DerivedCategory.Q.obj P) :=
  (Functor.mapDerivedCategoryCompIso (finiteConstant S Λ)
    (finiteCoefficientPullback S Λ h)).app (DerivedCategory.Q.obj P) ≪≫
    (Functor.mapDerivedCategoryNatIso (finiteConstantPullback S V h Λ)).app
      (DerivedCategory.Q.obj P)

private def residueSliceIso
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)) (n : ℕ)
    (Y : S.Etale)
    {M N : DerivedCategory (SheafOfModules.{u + 1} (completedAdicFiniteRing S d n))}
    (e : M ≅ N) :
    ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing S d n)
        ((toProEt S).obj Y) M ≅
      ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing S d n)
        ((toProEt S).obj Y) N := by
  let R := completedAdicFiniteRing S d n
  let U := (toProEt S).obj Y
  let F := SheafOfModules.overFunctor.{u + 1} R U
  let := (ringedOverFunctor_exactGeneral R U).1
  let := (ringedOverFunctor_exactGeneral R U).2.1
  let := (ringedOverFunctor_exactGeneral R U).2.2
  let cmp (K : DerivedCategory (SheafOfModules.{u + 1} R)) :
      ringedSiteDerivedRestrictionOfUniverses R U K ≅ F.mapDerivedCategory.obj K :=
    (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)).symm ≪≫
      F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K)
  exact cmp M ≪≫ F.mapDerivedCategory.mapIso e ≪≫ (cmp N).symm

/-- A single constant finite perfect chart stays constant after coefficient transport.
No completed object, covering, or propagation to smaller slices is involved. -/
theorem integralResidueFiniteChart
    (T S : Scheme.{u}) (g : S ⟶ T) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (c : IntegralResidueCoefficientModel l E d S) (n : ℕ)
    (C : CochainComplex
      (FiniteCoefficientModules T (PbcQuotient (pbcIntegralDatum l E) n)) ℤ)
    (Y : S.Etale)
    (P : CochainComplex (ModuleCat.{u + 1} (PbcQuotient (pbcIntegralDatum l E) n)) ℤ)
    (hP : @DerivedCategory.IsPerfectRingComplex (PbcQuotient (pbcIntegralDatum l E) n) _
      (HasDerivedCategory.standard _) (DerivedCategory.Q.obj P))
    (eP : Nonempty
      ((finiteCoefficientDerivedPullback T (PbcQuotient (pbcIntegralDatum l E) n)
          (Y.hom ≫ g)).obj (DerivedCategory.Q.obj C) ≅
        (finiteCoefficientRealization Y.left
          (PbcQuotient (pbcIntegralDatum l E) n)).mapDerivedCategory.obj
            (DerivedCategory.Q.obj (((constantSheaf (ProEt.topology Y.left)
              (ModuleCat.{u + 1} (PbcQuotient (pbcIntegralDatum l E) n))).mapHomologicalComplex
                (.up ℤ)).obj P)))) :
    ∃ P' : DerivedCategory (ModuleCat.{u}
        (Padic.coefficientExtensionIntegers l E ⧸ d.ideal ^ (n + 1))),
      DerivedCategory.IsPerfectRingComplex P' ∧
      Nonempty
        (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing S d n)
            ((toProEt S).obj Y)
            (integralResidueFiniteModel S l E d c n
              ((finiteCoefficientDerivedPullback T
                (PbcQuotient (pbcIntegralDatum l E) n) g).obj (DerivedCategory.Q.obj C))) ≅
          ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing S d n)
            ((toProEt S).obj Y)
            ((completedAdicDerivedChange S (residueLisseConstantComparison S d n)).obj
              ((residueLisseDerivedConstant S
                (Padic.coefficientExtensionIntegers l E ⧸ d.ideal ^ (n + 1))).obj P'))) := by
  let Λ := PbcQuotient (pbcIntegralDatum l E) n
  let L := integralResidueQuotientLift l E d hd n
  obtain ⟨B, hB, ⟨eB⟩⟩ := smallPerfectModel (integralResidueQuotientEquiv l E d hd n) P hP
  let B' := (L.mapHomologicalComplex (.up ℤ)).obj B
  have eB' : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj B' := eB
  let M := (finiteCoefficientDerivedPullback T Λ g).obj (DerivedCategory.Q.obj C)
  let N := (finiteCoefficientRealization S Λ).mapDerivedCategory.obj
    (DerivedCategory.Q.obj
      (((constantSheaf (ProEt.topology S)
        (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (.up ℤ)).obj B'))
  let comp := Functor.mapDerivedCategoryNatIso (finitePullbackComp T S Y.left g Y.hom Λ) ≪≫
    (Functor.mapDerivedCategoryCompIso (finiteCoefficientPullback T Λ g)
      (finiteCoefficientPullback S Λ Y.hom)).symm
  obtain ⟨ec⟩ := eP
  let eMN : (finiteCoefficientDerivedPullback S Λ Y.hom).obj M ≅
      (finiteCoefficientDerivedPullback S Λ Y.hom).obj N :=
    (comp.app (DerivedCategory.Q.obj C)).symm ≪≫ ec ≪≫
      finiteConstantModelIso Y.left Λ P ≪≫
      (finiteConstant Y.left Λ).mapDerivedCategory.mapIso eB' ≪≫
      (finiteConstantDerivedPullback S Y.left Y.hom Λ B').symm ≪≫
      (finiteCoefficientDerivedPullback S Λ Y.hom).mapIso
        (finiteConstantModelIso S Λ B').symm
  obtain ⟨es⟩ := integralResidueFiniteSlice S l E d c n Y M N ⟨eMN⟩
  obtain ⟨ek⟩ := integralResidueFiniteConstants S l E d hd c n B
  exact ⟨DerivedCategory.Q.obj B, hB, ⟨es ≪≫ residueSliceIso S l E d n Y ek⟩⟩

end AlgebraicGeometry.Scheme
