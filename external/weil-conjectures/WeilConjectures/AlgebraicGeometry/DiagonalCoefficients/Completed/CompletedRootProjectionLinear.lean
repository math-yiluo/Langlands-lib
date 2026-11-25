/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientMaps

import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedZlReduction
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsEmbeddedCompletionDiagram
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantZModScalarTensor

/-! # Linearity of the normalized finite root projections

Source: diagonal coefficient changes, integral root-limit identification.
(blueprint: lem-diagonal-completed-root-projection-linear).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open InternalAbelianSheafModule
open scoped TensorProduct
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] upperStarFromPoint
  Scheme.purTwistZlCompletionOfUniverses
  InternalAbelianSheafModule.sectionModuleEquivalenceCore

private local instance schemeCommRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, 0} X

private noncomputable def projectionRingSections (X : Scheme.{u}) :
    Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⥤
      Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} where
  obj R := by
    let P := presheafRings ((sheafToPresheaf _ Ab.{u + 1}).obj R.X)
    refine ⟨P, ?_⟩
    apply (Presheaf.isSheaf_iff_isSheaf_comp (Scheme.ProEt.topology X) P
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).2
    exact R.X.property
  map f := ⟨{
    app Z := monToRing.map
      (((Monoidal.monFunctorCategoryEquivalence _ Ab.{u + 1}).functor.map
        ((sheafToPresheaf _ Ab.{u + 1}).mapMon.map f)).app Z)
    naturality := by
      intro Z W g
      ext x
      exact ConcreteCategory.congr_hom (f.hom.hom.naturality g) x }⟩
  map_id R := by ext Z x; rfl
  map_comp f g := by ext Z x; rfl

private noncomputable def projectionRingSectionsIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :
    (projectionRingSections X).obj
        (Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)) ≅ R := by
  let J := Scheme.ProEt.topology X
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hmon : (sheafToPresheaf J Ab.{u + 1}).monObjObj A =
      R.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj A.obj := R.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul A
  apply (fullyFaithfulSheafToPresheaf J RingCat.{u + 1}).preimageIso
  refine NatIso.ofComponents (fun Z ↦ ?_) (fun f ↦ ?_)
  · refine RingEquiv.toRingCatIso
      (R := ((projectionRingSections X).obj (Mon.mk A)).obj.obj Z)
      (S := R.obj.obj Z)
      { toEquiv := Equiv.refl _
        map_add' := fun _ _ ↦ rfl
        map_mul' := ?_ }
    intro a b
    change (((sheafToPresheaf J Ab.{u + 1}).monObjObj A).mul.app Z).hom
      (a ⊗ₜ[ℤ] b) = (show R.obj.obj Z from a) * (show R.obj.obj Z from b)
    have hm := congrArg (fun m : MonObj A.obj ↦ m.mul) hmon
    rw [hm]
    rfl
  · ext a
    rfl

attribute [local irreducible] constantPresentation

private noncomputable def projectionConstantMonIso (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (sfbConstantRing X).obj ((forget₂ CommRingCat RingCat).obj A) ≅
      Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A))) := by
  let e := constantPresentation.{u} (Scheme.ProEt.topology X) A
  have h := IsMonHom.of_eq e.hom
    (constantSheafRingMonObj (Scheme.ProEt.topology X) A).symm rfl
    (hf := constantPresentation_mon.{u} (Scheme.ProEt.topology X) A)
  exact Mon.mkIso e h.one_hom h.mul_hom

private theorem projectionConstantMonIso_hom (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (projectionConstantMonIso X A).hom.hom = (sfbConstantRingAbIso X A).inv := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A))).property
  ext V x
  have h := constantRingAb_unit X A V x
  have he := congrArg (fun f ↦ f.app V x)
    (constantPresentation_unit.{u} (Scheme.ProEt.topology X) A)
  change (projectionConstantMonIso X A).hom.hom.hom.app V _ = _ at he
  change (projectionConstantMonIso X A).hom.hom.hom.app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const _).obj (AddCommGrpCat.of A))).app V x) =
    (sfbConstantRingAbIso X A).inv.hom.app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const _).obj (AddCommGrpCat.of A))).app V x)
  exact he.trans
    (((sheafToPresheaf _ _).mapIso (sfbConstantRingAbIso X A)).hom_inv_id_app_apply V _
      |>.symm.trans (congrArg ((sfbConstantRingAbIso X A).inv.hom.app V) h))

private noncomputable def projectionConstantRingIso (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (projectionRingSections X).obj ((sfbConstantRing X).obj ((forget₂ CommRingCat RingCat).obj A)) ≅
      (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A) :=
  (projectionRingSections X).mapIso (projectionConstantMonIso X A) ≪≫
    projectionRingSectionsIso X _

private theorem projectionConstantRingIso_hom (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (projectionConstantRingIso X A).hom = (sfbConstantRingAbIso X A).inv := by
  change (projectionConstantMonIso X A).hom.hom ≫ 𝟙 _ = _
  rw [Category.comp_id, projectionConstantMonIso_hom]

attribute [local irreducible] projectionConstantRingIso projectionConstantMonIso
  projectionRingSectionsIso

-- Sections of the reconstructed module are acted on by the sections of the coefficient object.
private local instance sectionModuleSMul (X : Scheme.{u})
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
    (M : Mod _ B) (V : X.ProEtᵒᵖ) :
    SMul (B.obj.obj V) (((sectionModuleFunctor (Scheme.ProEt.topology X) B).obj M).val.obj V) :=
  (((sectionModuleFunctor (Scheme.ProEt.topology X) B).obj M).val.obj V).isModule.toSMul

-- Scalar restriction under section reconstruction is unchanged on elements.
private theorem section_comap_smul (X : Scheme.{u})
    {R B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj B] [IsCommMonObj R] [IsCommMonObj B]
    (a : R ⟶ B) [IsMonHom a] (M : Mod _ B) (V : X.ProEtᵒᵖ)
    (r : R.obj.obj V) (x : M.X.obj.obj V) :
    (show ((sectionModuleFunctor (Scheme.ProEt.topology X) R).obj
        ((Mod.comap a).obj M)).val.obj V from
      @SMul.smul _ _
        (((sectionModuleFunctor (Scheme.ProEt.topology X) R).obj
          ((Mod.comap a).obj M)).val.obj V).isModule.toSMul r x) =
      (a.hom.app V r) •
        (show ((sectionModuleFunctor (Scheme.ProEt.topology X) B).obj M).val.obj V from x) := by
  have hμ := congr_app (Functor.LaxMonoidal.μ_natural_left
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) a M.X) V
  exact (ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f ≫ (Mod.act M.X).hom.app V) hμ) (r ⊗ₜ[ℤ] x)).symm

-- Any quotient coefficient ring is killed by its defining positive power.
private theorem finiteCoefficient_nsmul (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField l) (n : ℕ) :
    l ^ (n + 1) • 𝟙 (condensedRingObj (spEllPointRingObj l E n) X) = 0 := by
  have hz : (l ^ (n + 1) : spEllQuotient l E n) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (spTateEllIdeal l E n))]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  let : TopologicalSpace (spEllQuotient l E n) := ⊥
  let : DiscreteTopology (spEllQuotient l E n) := ⟨rfl⟩
  let : IsTopologicalRing (spEllQuotient l E n) := DiscreteTopology.topologicalRing
  have hp : l ^ (n + 1) • 𝟙 (spEllPointRingObj.{u} l E n) = 0 := by
    ext V f
    apply ULift.ext
    change l ^ (n + 1) • f.down = 0
    apply ContinuousMap.ext
    intro t
    change l ^ (n + 1) • f.down t = 0
    rw [nsmul_eq_mul, Nat.cast_pow, hz, zero_mul]
  let F := upperStarFromPoint X
  have : F.IsLeftAdjoint := by
    unfold F upperStarFromPoint
    exact (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  change l ^ (n + 1) • 𝟙 (F.obj (spEllPointRingObj l E n)) = 0
  rw [← F.map_id, ← F.map_nsmul, hp, F.map_zero]

private theorem monHom_of_epi_factor
    {C : Type*} [Category C] [MonoidalCategory C]
    {R S B : C} [MonObj R] [MonObj S] [MonObj B]
    (q : R ⟶ S) [IsMonHom q] [Epi q] (a : R ⟶ B) [IsMonHom a]
    (b : S ⟶ B) (h : q ≫ b = a) [Epi (q ⊗ₘ q)] : IsMonHom b where
  one_hom := by rw [← IsMonHom.one_hom q, Category.assoc, h, IsMonHom.one_hom a]
  mul_hom := by
    apply (cancel_epi (q ⊗ₘ q)).mp
    rw [← IsMonHom.mul_hom_assoc q, h, IsMonHom.mul_hom a,
      tensorHom_comp_tensorHom_assoc, h]

-- The cokernel comparison factors every N-torsion coefficient map through the residue ring.
private theorem finiteCoefficient_factor (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField l) (n : ℕ) :
    ∃ b : ((sfbConstantRing X).obj
        ((sfbZModCoefficientTower l).obj (op (n + 1)))).X ⟶
        condensedRingObj (spEllPointRingObj l E n) X,
      IsMonHom b ∧ (purZlReduction l X (n + 1)).hom ≫ b =
        coefficientMap (integralMap l E) X ≫ spEllReduction X l E n := by
  let a := coefficientMap (integralMap l E) X ≫ spEllReduction X l E n
  obtain ⟨h, ⟨hc⟩⟩ := purReductionCokernel l X (n + 1)
  have ha : (purZlPowerMultiplication l X (n + 1)).hom ≫ a = 0 := by
    change (l ^ (n + 1) • 𝟙 _) ≫ a = 0
    calc
      _ = l ^ (n + 1) • a := by rw [Preadditive.nsmul_comp, Category.id_comp]
      _ = a ≫ (l ^ (n + 1) • 𝟙 _) := by
        rw [Preadditive.comp_nsmul, Category.comp_id]
      _ = 0 := by rw [finiteCoefficient_nsmul l X E n, comp_zero]
  let b : ((sfbConstantRing X).obj
      ((sfbZModCoefficientTower l).obj (op (n + 1)))).X ⟶
      condensedRingObj (spEllPointRingObj l E n) X :=
    hc.desc (CokernelCofork.ofπ a ha)
  have hb : (purZlReduction l X (n + 1)).hom ≫ b = a :=
    hc.fac (CokernelCofork.ofπ a ha) WalkingParallelPair.one
  have : Epi (purZlReduction l X (n + 1)).hom := Cofork.IsColimit.epi hc
  have : Epi ((purZlReduction l X (n + 1)).hom ⊗ₘ
      (purZlReduction l X (n + 1)).hom) := by
    have : Epi ((purZlReduction l X (n + 1)).hom ▷
        (coefficientRing X (Mon.mk
          (Profinite.continuousMapRingObj.{u} ℤ_[l]))).X) :=
      (tensorRight _).map_epi _
    have : Epi (((sfbConstantRing X).obj
        ((sfbZModCoefficientTower l).obj (op (n + 1)))).X ◁
          (purZlReduction l X (n + 1)).hom) := (tensorLeft _).map_epi _
    rw [MonoidalCategory.tensorHom_def]
    infer_instance
  exact ⟨b, monHom_of_epi_factor _ a b hb, hb⟩

private local instance finitePointCommMon (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (n : ℕ) :
    IsCommMonObj (spEllPointRingObj.{u} l E n) := by
  let : TopologicalSpace (spEllQuotient l E n) := ⊥
  let : DiscreteTopology (spEllQuotient l E n) := ⟨rfl⟩
  let : IsTopologicalRing (spEllQuotient l E n) := DiscreteTopology.topologicalRing
  exact Profinite.isCommMonObj_continuousMapRingObj (spEllQuotient l E n)

attribute [-instance] WeilConjectures.SixFunctors.integralModel_coefficientMonObj in
/-- Every finite root projection is linear for the normalized completed coefficients.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), and the coordinatewise
integral twist construction of definition-tate-twists.
(blueprint: lem-diagonal-completed-root-projection-linear).

Proof: the completed root action is defined coordinatewise. Its n-th projection
is scalar multiplication by the n-th coefficient reduction. The equation he
identifies that reduction with the residue of the pulled-back condensed scalar.
The finite quotient coefficient ring is annihilated by l^(n+1). The cokernel
property of normalized reduction therefore factors the actual coefficient map
through the constant cyclic residue ring. Canceling reduction and its tensor
square proves that this factor is unital and multiplicative. The free-module
unit commutes with the resulting cyclic scalar action: locally each scalar is
an integer, and additivity proves the equation there. Separatedness gives the
equation on all sections. The underlying root projection followed by the free-module unit
is natural in the site object; these linear section maps give the morphism.
No invertibility of this morphism is asserted: the source is the whole root
limit and the target is just one finite level. The same argument applies to
the empty scheme. -/
theorem completedRootProjection_linear (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (l : Γ(X, ⊤)))
    (e : (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X)
            (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)) ≅
        Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
    (he : ∀ n : ℕ,
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.inv ≫
            (purZlReduction l X (n + 1)).hom =
          (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              ((sheafCompose (Scheme.ProEt.topology X)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                  (Scheme.purTwistZlProjection X l n)) ≫
            (sfbConstantRingAbIso X
              (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom)
    (n : ℕ) :
    ∃ f : (SheafOfModules.restrictScalars e.hom).obj (Scheme.purTwistZlModule X l) ⟶
        (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X)
          (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)).functor.obj
            ((Mod.comap (coefficientMap (integralMap l (bottomField l)) X)).obj
              (spIntegralTwistLevel X l (bottomField l) n)),
      (SheafOfModules.toSheaf _).map f =
        limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) ≫
          (Mod.freeForgetAdjunction
            (condensedRingObj (spEllPointRingObj l (bottomField l) n) X)).unit.app
              (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))) := by
  have _hX := hX
  let J := Scheme.ProEt.topology X
  let B := condensedRingObj (spEllPointRingObj l (bottomField l) n) X
  let F := Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))
  let M := (Mod.free B).obj F
  let unitMap := (Mod.freeForgetAdjunction B).unit.app F
  let π := limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n)
  let a := coefficientMap (integralMap l (bottomField l)) X ≫
    spEllReduction X l (bottomField l) n
  obtain ⟨b, hb, hba⟩ := finiteCoefficient_factor l X (bottomField l) n
  have : IsMonHom b := hb
  let k := projectionConstantRingIso X (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
  let bMon : (sfbConstantRing X).obj
      ((sfbZModCoefficientTower l).obj (op (n + 1))) ⟶ Mon.mk B := ⟨b⟩
  let β := (projectionRingSections X).map bMon
  let P := (SheafOfModules.restrictScalars (k.inv ≫ β)).obj
    ((sectionModuleFunctor J B).obj M)
  let j := Scheme.abResidueLinearLift X l n (Scheme.purTwistRootsModule X l n) P unitMap
  let A := (SheafOfModules.restrictScalars e.hom).obj (Scheme.purTwistZlModule X l)
  let T := (sectionModuleEquivalence J
    (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)).functor.obj
      ((Mod.comap (coefficientMap (integralMap l (bottomField l)) X)).obj
        (spIntegralTwistLevel X l (bottomField l) n))
  have hk : (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map k.inv =
      (sfbConstantRingAbIso X
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom := by
    have h : (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso k =
        (sfbConstantRingAbIso X
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).symm := by
      apply Iso.ext
      exact projectionConstantRingIso_hom X _
    exact congrArg Iso.inv h
  have hscalar (V : X.ProEtᵒᵖ)
      (r : ((sectionRingSheaf J
        (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)).obj.obj V)) :
      b.hom.app V (k.inv.hom.app V
        ((Scheme.purTwistZlProjection X l n).hom.app V (e.hom.hom.app V r))) =
          a.hom.app V r := by
    have hr := congrArg (fun t ↦ t.hom.app V (e.hom.hom.app V r)) (he n)
    change (purZlReduction l X (n + 1)).hom.hom.app V
        (e.inv.hom.app V (e.hom.hom.app V r)) =
      (sfbConstantRingAbIso X
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.hom.app V
          ((Scheme.purTwistZlProjection X l n).hom.app V (e.hom.hom.app V r)) at hr
    have her : e.inv.hom.app V (e.hom.hom.app V r) = r :=
      ((sheafToPresheaf J RingCat.{u + 1}).mapIso e).hom_inv_id_app_apply V r
    have hr' := (congrArg ((purZlReduction l X (n + 1)).hom.hom.app V) her).symm.trans hr
    have hkV := congrArg (fun t ↦ t.hom.app V
      ((Scheme.purTwistZlProjection X l n).hom.app V (e.hom.hom.app V r))) hk
    change k.inv.hom.app V _ = _ at hkV
    calc
      _ = b.hom.app V ((sfbConstantRingAbIso X
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.hom.app V
            ((Scheme.purTwistZlProjection X l n).hom.app V (e.hom.hom.app V r))) :=
        congrArg (b.hom.app V) hkV
      _ = b.hom.app V ((purZlReduction l X (n + 1)).hom.hom.app V r) :=
        congrArg (b.hom.app V) hr'.symm
      _ = a.hom.app V r := congrArg (fun t ↦ t.hom.app V r) hba
  have hs (V : X.ProEtᵒᵖ)
      (r : ((sectionRingSheaf J
        (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)).obj.obj V))
      (x : A.val.obj V) :
      (π ≫ unitMap).hom.app V (r • x) = r • (show T.val.obj V from (π ≫ unitMap).hom.app V x) := by
    have hp := (Scheme.purTwistZlAction_existsUnique X l).exists.choose_spec.2
      n V (e.hom.hom.app V r) x
    change π.hom.app V (r • x) =
      (Scheme.purTwistZlProjection X l n).hom.app V (e.hom.hom.app V r) •
        (show (Scheme.purTwistRootsModule X l n).val.obj V from π.hom.app V x) at hp
    let c := (Scheme.purTwistZlProjection X l n).hom.app V (e.hom.hom.app V r)
    let y : (Scheme.purTwistRootsModule X l n).val.obj V := π.hom.app V x
    let z : ((sectionModuleFunctor J B).obj M).val.obj V := unitMap.hom.app V y
    have hj : unitMap.hom.app V (c • y) =
        (b.hom.app V (k.inv.hom.app V c)) • z :=
      (j.val.app V).hom.map_smul c y
    have ht₁ := section_comap_smul X (spEllReduction X l (bottomField l) n) M V
      ((coefficientMap (integralMap l (bottomField l)) X).hom.app V r) z
    have ht₂ := section_comap_smul X (coefficientMap (integralMap l (bottomField l)) X)
      ((Mod.comap (spEllReduction X l (bottomField l) n)).obj M) V r z
    calc
      _ = unitMap.hom.app V (c • y) := congrArg (unitMap.hom.app V) hp
      _ = (b.hom.app V (k.inv.hom.app V c)) • z := hj
      _ = (a.hom.app V r) • z :=
        congrArg (fun s : B.obj.obj V ↦ s • z) (hscalar V r)
      _ = r • (show T.val.obj V from z) := ht₁.symm.trans ht₂.symm
  refine ⟨⟨PresheafOfModules.homMk (π ≫ unitMap).hom hs⟩, ?_⟩
  rfl

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
