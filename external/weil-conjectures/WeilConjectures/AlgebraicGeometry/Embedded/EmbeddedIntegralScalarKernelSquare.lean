/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The embedded integral constant scalar square

Source: integral-models-stacks, the coefficient comparison preceding Stacks Tag 09C1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale

attribute [local instance] Sheaf.monoidalCategory

attribute [-instance] integralModel_coefficientMonObj

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  IntegralModelsStacks.smallMap

section RingSheaves
variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J Ab.{u}] [(J.W (A := Ab.{u})).IsMonoidal]
  {S T : Sheaf J RingCat.{u}}
  (f : (sheafCompose J (forget₂ RingCat.{u} Ab.{u})).obj S ⟶
    (sheafCompose J (forget₂ RingCat.{u} Ab.{u})).obj T) [IsMonHom f]

private theorem forgetMon (R : Sheaf J RingCat.{u}) :
    (sheafToPresheaf J Ab.{u}).monObjObj
        ((sheafCompose J (forget₂ RingCat.{u} Ab.{u})).obj R) =
      R.obj.monObjCompForget₂ := by
  apply MonObj.ext
  let A := (sheafCompose J (forget₂ RingCat.{u} Ab.{u})).obj R
  let : MonObj A.obj := R.obj.monObjCompForget₂
  exact Sheaf.μ_comp_map_mul A

private theorem ringSheafMap_mul (U : Cᵒᵖ) (a b : S.obj.obj U) :
    f.hom.app U (a * b) =
      (show T.obj.obj U from f.hom.app U a) * (show T.obj.obj U from f.hom.app U b) := by
  have h := IsMonHom.mul_hom (f := (sheafToPresheaf J Ab.{u}).map f)
  have hS := congrArg (fun m ↦ m.mul) (forgetMon J S)
  have hT := congrArg (fun m ↦ m.mul) (forgetMon J T)
  change _ ≫ f.hom = (f.hom ⊗ₘ f.hom) ≫ _ at h
  rw [hS, hT] at h
  have hh := ConcreteCategory.congr_hom (congr_app h U) (a ⊗ₜ[ℤ] b)
  change f.hom.app U (a * b) =
    (show T.obj.obj U from f.hom.app U a) * (show T.obj.obj U from f.hom.app U b) at hh
  exact hh

private def ringSheafIso
    (e : Mon.mk ((sheafCompose J (forget₂ RingCat.{u} Ab.{u})).obj S) ≅
      Mon.mk ((sheafCompose J (forget₂ RingCat.{u} Ab.{u})).obj T)) : S ≅ T := by
  let er (U : Cᵒᵖ) : S.obj.obj U ≃+* T.obj.obj U :=
    { (((sheafToPresheaf J Ab.{u}).mapIso
        ((Mon.forget _).mapIso e)).app U).addCommGroupIsoToAddEquiv with
      map_mul' := ringSheafMap_mul J e.hom.hom U }
  refine
    { hom := ⟨{ app U := RingCat.ofHom (er U).toRingHom
                naturality := fun U V g ↦ RingCat.hom_ext (by
                  ext x
                  exact ConcreteCategory.congr_hom (e.hom.hom.hom.naturality g) x) }⟩
      inv := ⟨{ app U := RingCat.ofHom (er U).symm.toRingHom
                naturality := fun U V g ↦ RingCat.hom_ext (by
                  ext x
                  exact ConcreteCategory.congr_hom (e.inv.hom.hom.naturality g) x) }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext U x
    exact (er U).symm_apply_apply x
  · ext U x
    exact (er U).apply_symm_apply x
private theorem ringSheafIso_hom
    (e : Mon.mk ((sheafCompose J (forget₂ RingCat.{u} Ab.{u})).obj S) ≅
      Mon.mk ((sheafCompose J (forget₂ RingCat.{u} Ab.{u})).obj T)) :
    (sheafCompose J (forget₂ RingCat.{u} Ab.{u})).map (ringSheafIso J e).hom =
      e.hom.hom := rfl

attribute [local irreducible] ringSheafIso
end RingSheaves

private def constIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : RingCat.of (ULift.{u + 1} A) ≅
      (Profinite.continuousMapRingSheafOfUniverse.{u, u} A).obj.obj
        (op (Profinite.of PUnit.{u + 1})) :=
  RingEquiv.toRingCatIso
    { toFun x := ULift.up (ContinuousMap.const _ x.down)
      invFun f := ULift.up (f.down PUnit.unit)
      left_inv _ := rfl
      right_inv f := by
        apply ULift.ext
        ext y
        exact congrArg f.down (Subsingleton.elim PUnit.unit y)
      map_mul' _ _ := rfl
      map_add' _ _ := rfl }

private def constIsoSmall (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : RingCat.of (ULift.{u + 1} A) ≅
      (Profinite.continuousMapRingSheaf.{u} A).obj.obj
        (op (Profinite.of PUnit.{u + 1})) :=
  RingEquiv.toRingCatIso
    { toFun x := ULift.up (ContinuousMap.const _ x.down)
      invFun f := ULift.up (f.down PUnit.unit)
      left_inv _ := rfl
      right_inv f := by
        apply ULift.ext
        ext y
        exact congrArg f.down (Subsingleton.elim PUnit.unit y)
      map_mul' _ _ := rfl
      map_add' _ _ := rfl }

private theorem scalarCounit (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    ((constantCommuteCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
        (CommRingCat.of (ULift.{u + 1} A))).hom ≫
      (constantSheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}).map
        (constIso A).hom ≫
      (constantSheafAdj (coherentTopology Profinite.{u}) RingCat.{u + 1}
        Profinite.isTerminalPUnit).counit.app
        (Profinite.continuousMapRingSheafOfUniverse A) =
      IntegralModelsStacks.constantToContinuous A := by
  unfold IntegralModelsStacks.constantToContinuous
  congr 1
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) RingCat.{u + 1}
    Profinite.isTerminalPUnit
  change (adj.homEquiv (RingCat.of (ULift.{u + 1} A))
    (Profinite.continuousMapRingSheafOfUniverse A)).symm (constIso A).hom = _
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  dsimp only [adj, constantSheafAdj]
  rw [Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

private theorem scalarCounitSmall (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    ((constantCommuteCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
        (CommRingCat.of (ULift.{u + 1} A))).hom ≫
      (constantSheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}).map
        (constIsoSmall A).hom ≫
      (constantSheafAdj (coherentTopology Profinite.{u}) RingCat.{u + 1}
        Profinite.isTerminalPUnit).counit.app
        (Profinite.continuousMapRingSheaf A) =
      IntegralModelsEmbedded.constantToContinuous A := by
  unfold IntegralModelsEmbedded.constantToContinuous
  congr 1
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) RingCat.{u + 1}
    Profinite.isTerminalPUnit
  change (adj.homEquiv (RingCat.of (ULift.{u + 1} A))
    (Profinite.continuousMapRingSheaf A)).symm (constIsoSmall A).hom = _
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  dsimp only [adj, constantSheafAdj]
  rw [Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

private def liftEquiv {A : Type u} {B : Type} [CommRing A] [CommRing B]
    (f : A ≃+* B) : ULift.{u + 1} A ≃+* ULift.{u + 1} B :=
  ULift.ringEquiv.trans (f.trans ULift.ringEquiv.symm)

private def discreteIso {A : Type u} {B : Type} [CommRing A] [CommRing B]
    (f : A ≃+* B) :
    IntegralModelsStacks.discreteSheaf A ≅ IntegralModelsEmbedded.discreteSheaf.{u} B :=
  (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
    ((constantSheaf _ CommRingCat.{u + 1}).mapIso (liftEquiv f).toCommRingCatIso)

private theorem scalarSquare {A : Type u} {B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (e : Profinite.continuousMapRingSheafOfUniverse.{u, u} A ≅
      Profinite.continuousMapRingSheaf.{u} B) :
    ∃ f : A ≃+* B,
      (discreteIso f).hom ≫ IntegralModelsEmbedded.constantToContinuous B =
        IntegralModelsStacks.constantToContinuous A ≫ e.hom := by
  let d : RingCat.of (ULift.{u + 1} A) ≅ RingCat.of (ULift.{u + 1} B) :=
    constIso A ≪≫ ((sheafToPresheaf _ RingCat.{u + 1}).mapIso e).app
      (op (Profinite.of PUnit.{u + 1})) ≪≫ (constIsoSmall B).symm
  let f : A ≃+* B := ULift.ringEquiv.symm.trans
    (d.ringCatIsoToRingEquiv.trans ULift.ringEquiv)
  refine ⟨f, ?_⟩
  have hfd : (liftEquiv f).toRingCatIso = d := by
    apply Iso.ext
    ext x
    rfl
  let c := constantCommuteCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let F := constantSheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) RingCat.{u + 1}
    Profinite.isTerminalPUnit
  rw [← scalarCounitSmall, ← scalarCounit]
  have hc := c.hom.naturality (liftEquiv f).toCommRingCatIso.hom
  change (discreteIso f).hom ≫ (c.app _).hom = (c.app _).hom ≫
    F.map (liftEquiv f).toRingCatIso.hom at hc
  rw [← Category.assoc, hc, hfd]
  have hd : d.hom ≫ (constIsoSmall B).hom =
      (constIso A).hom ≫ e.hom.hom.app (op (Profinite.of PUnit.{u + 1})) := by
    simp only [d, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rfl
  have hn := adj.counit.naturality e.hom
  change F.map (e.hom.hom.app (op (Profinite.of PUnit.{u + 1}))) ≫
    adj.counit.app (Profinite.continuousMapRingSheaf B) =
      adj.counit.app (Profinite.continuousMapRingSheafOfUniverse A) ≫ e.hom at hn
  simp only [Category.assoc]
  erw [← F.map_comp_assoc, hd, F.map_comp]
  simp only [Category.assoc]
  erw [hn]

private theorem residueIdeal (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)]
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (f : Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val) ≃+*
      PadicAlgCl.integers ℓ E.1) :
    (Ideal.span {π}) ^ (0 + 1) =
      Ideal.map f.toRingHom (Padic.coefficientExtensionIdeal ℓ (ULift.{u} E.val) 1) := by
  let A := Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val)
  have h := (Padic.coefficientExtensionIntegers_dvr ℓ (ULift.{u} E.val)).choose_spec
  let : IsLocalRing A := h.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ℓ (ULift.{u} E.val)} :
      Set A) = Padic.coefficientExtensionMaximalIdeal ℓ (ULift.{u} E.val) :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hmax : Padic.coefficientExtensionMaximalIdeal ℓ (ULift.{u} E.val) =
      IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  rw [pow_one, hπ, Padic.coefficientExtensionIdeal, pow_one, hgen, hmax]
  exact (IsLocalRing.eq_maximalIdeal
    ((IsLocalRing.maximalIdeal.isMaximal A).map_bijective f.toRingHom f.bijective)).symm

private def constantAbFunctor : CommRingCat.{u + 1} ⥤
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  constantSheaf _ CommRingCat.{u + 1} ⋙
    sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})

private def mixedDiscreteIso {A : Type u} {B : Type} [CommRing A] [CommRing B]
    (f : A ≃+* B) : IntegralModelsStacks.discreteObj A ≅
      IntegralModelsEmbedded.discreteObj.{u} B :=
  constantAbFunctor.mapIso
    (ULift.ringEquiv.trans (f.trans ULift.ringEquiv.symm)).toCommRingCatIso

private theorem mixedDiscreteIso_hom {A : Type u} {B : Type} [CommRing A] [CommRing B]
    (f : A ≃+* B) :
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (discreteIso f).hom =
        (mixedDiscreteIso f).hom := rfl

private instance mixedDiscreteIso_mon {A : Type u} {B : Type} [CommRing A] [CommRing B]
    (f : A ≃+* B) : IsMonHom (mixedDiscreteIso.{u} f).hom := by
  dsimp only [mixedDiscreteIso, constantAbFunctor, Functor.mapIso_hom, Functor.comp_map]
  infer_instance

private theorem discreteQuotientSquare {A : Type u} {B : Type} [CommRing A] [CommRing B]
    (f : A ≃+* B) (I : Ideal A) (J : Ideal B) (h : J = Ideal.map f.toRingHom I) :
    (mixedDiscreteIso f).hom ≫ IntegralModelsEmbedded.discreteMap (Ideal.Quotient.mk J) =
      IntegralModelsStacks.discreteMap (Ideal.Quotient.mk I) ≫
        (mixedDiscreteIso (Ideal.quotientEquiv I J f h)).hom := by
  let a := (ULift.ringEquiv.trans (f.trans ULift.ringEquiv.symm)).toCommRingCatIso.hom
  let b := (ULift.ringEquiv.trans
    ((Ideal.quotientEquiv I J f h).trans ULift.ringEquiv.symm)).toCommRingCatIso.hom
  let q : CommRingCat.of (ULift.{u + 1} A) ⟶ CommRingCat.of (ULift.{u + 1} (A ⧸ I)) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk I).comp ULift.ringEquiv.toRingHom))
  let p : CommRingCat.of (ULift.{u + 1} B) ⟶ CommRingCat.of (ULift.{u + 1} (B ⧸ J)) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk J).comp ULift.ringEquiv.toRingHom))
  have he : a ≫ p = q ≫ b := by
    ext x
    rfl
  have he1 := (constantAbFunctor.{u}).congr_map he
  rw [Functor.map_comp, Functor.map_comp] at he1
  exact he1

private theorem smallMap_comp (X : Scheme.{u})
    {R S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T]
    (f : R ⟶ S) (g : S ⟶ T) [IsMonHom f] [IsMonHom g] :
    IntegralModelsStacks.smallMap X (f ≫ g) =
      IntegralModelsStacks.smallMap X f ≫ IntegralModelsStacks.smallMap X g := by
  unfold IntegralModelsStacks.smallMap
  ext U x
  rfl

private theorem smallMap_congr (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f g : R ⟶ S) [IsMonHom f] [IsMonHom g] (h : f = g) :
    IntegralModelsStacks.smallMap X f = IntegralModelsStacks.smallMap X g := by
  subst g
  rfl

private theorem smallMap_id (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    IntegralModelsStacks.smallMap X (𝟙 R) = 𝟙 _ := by
  unfold IntegralModelsStacks.smallMap
  ext U x
  rfl

private def smallIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S) :
    IntegralModelsStacks.smallRing X R ≅ IntegralModelsStacks.smallRing X S where
  hom := IntegralModelsStacks.smallMap X e.hom.hom
  inv := IntegralModelsStacks.smallMap X e.inv.hom
  hom_inv_id := by
    rw [← smallMap_comp]
    have h : e.hom.hom ≫ e.inv.hom = 𝟙 _ :=
      congrArg (fun g ↦ g.hom) e.hom_inv_id
    simp only [h, smallMap_id]
  inv_hom_id := by
    rw [← smallMap_comp]
    have h : e.inv.hom ≫ e.hom.hom = 𝟙 _ :=
      congrArg (fun g ↦ g.hom) e.inv_hom_id
    simp only [h, smallMap_id]

private theorem kernelSquare
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    {R B S T : Sheaf J CommRingCat.{v}}
    (a : R ≅ B) (b : S ≅ T) (q : R ⟶ S) (p : B ⟶ T)
    (h : a.hom ≫ p = q ≫ b.hom) :
    (ConstantCompletion.kernelIdeal q).extension a.hom =
      ConstantCompletion.kernelIdeal p := by
  let K := ConstantCompletion.kernelIdeal q
  let L := ConstantCompletion.kernelIdeal p
  have hK (U : C) : K.sections U = RingHom.ker (q.hom.app (op U)).hom :=
    (ConstantCompletion.kernelIdeal_existsUnique q).exists.choose_spec U
  have hL (U : C) : L.sections U = RingHom.ker (p.hom.app (op U)).hom :=
    (ConstantCompletion.kernelIdeal_existsUnique p).exists.choose_spec U
  have hs (U : C) : L.sections U =
      Ideal.span (Set.range (fun x : K.sections U ↦ a.hom.hom.app (op U) x)) := by
    apply le_antisymm
    · intro x hx
      let y := a.inv.hom.app (op U) x
      have hay : a.hom.hom.app (op U) y = x := by
        exact ConcreteCategory.congr_hom (congr_app
          (congrArg (fun g : B ⟶ B ↦ g.hom) a.inv_hom_id) (op U)) x
      have hy : y ∈ K.sections U := by
        rw [hK]
        change q.hom.app (op U) y = 0
        have he := ConcreteCategory.congr_hom (congr_app
          (congrArg (fun g : R ⟶ T ↦ g.hom) h) (op U)) y
        change p.hom.app (op U) (a.hom.hom.app (op U) y) =
          b.hom.hom.app (op U) (q.hom.app (op U) y) at he
        rw [hay] at he
        rw [hL] at hx
        have hzero : b.hom.hom.app (op U) (q.hom.app (op U) y) = 0 := he.symm.trans hx
        have hh := congrArg (b.inv.hom.app (op U)) hzero
        have hi := ConcreteCategory.congr_hom (congr_app
          (congrArg (fun g : S ⟶ S ↦ g.hom) b.hom_inv_id) (op U)) (q.hom.app (op U) y)
        change b.inv.hom.app (op U)
          (b.hom.hom.app (op U) (q.hom.app (op U) y)) = q.hom.app (op U) y at hi
        rw [hi, map_zero] at hh
        exact hh
      exact hay ▸ Ideal.subset_span ⟨⟨y, hy⟩, rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨y, rfl⟩
      rw [hL]
      change p.hom.app (op U) (a.hom.hom.app (op U) y.val) = 0
      have he := ConcreteCategory.congr_hom (congr_app
        (congrArg (fun g : R ⟶ T ↦ g.hom) h) (op U)) y.val
      change p.hom.app (op U) (a.hom.hom.app (op U) y.val) =
        b.hom.hom.app (op U) (q.hom.app (op U) y.val) at he
      have hy : q.hom.app (op U) y.val = 0 := by
        have hy : y.val ∈ RingHom.ker (q.hom.app (op U)).hom := by
          simpa only [hK] using y.property
        exact hy
      rw [he, hy, map_zero]
  apply (K.existsUnique_extension a.hom).unique
    ((K.existsUnique_extension a.hom).exists.choose_spec)
  intro U x
  constructor
  · intro hx
    refine ⟨⊤, J.top_mem _, ?_⟩
    intro V g _
    rw [← hs V]
    exact L.restriction g x hx
  · rintro ⟨Z, hZ, hx⟩
    exact L.local_mem U x Z hZ (fun V g hg ↦ by rw [hs V]; exact hx V g hg)

private theorem smallKernelSquare (X : Scheme.{u})
    {R B S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj B] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj B] [IsCommMonObj S] [IsCommMonObj T]
    (a : Mon.mk R ≅ Mon.mk B) (b : Mon.mk S ≅ Mon.mk T)
    (q : R ⟶ S) (p : B ⟶ T) [IsMonHom q] [IsMonHom p]
    (h : a.hom.hom ≫ p = q ≫ b.hom.hom) :
    (ConstantCompletion.kernelIdeal (IntegralModelsStacks.smallMap X q)).extension
        (IntegralModelsStacks.smallMap X a.hom.hom) =
      ConstantCompletion.kernelIdeal (IntegralModelsStacks.smallMap X p) := by
  have hs : (smallIso X a).hom ≫ IntegralModelsStacks.smallMap X p =
      IntegralModelsStacks.smallMap X q ≫ (smallIso X b).hom :=
    (smallMap_comp X a.hom.hom p).symm.trans
      ((smallMap_congr X _ _ h).trans (smallMap_comp X q b.hom.hom))
  exact kernelSquare (smallIso X a) (smallIso X b)
    (IntegralModelsStacks.smallMap X q) (IntegralModelsStacks.smallMap X p) hs

private def mixedPullbackIso (X : Scheme.{u})
    {A : Type u} {B : Type} [CommRing A] [CommRing B] (f : A ≃+* B) :
    Mon.mk (condensedRingObj (IntegralModelsStacks.discreteObj A) X) ≅
      Mon.mk (condensedRingObj (IntegralModelsEmbedded.discreteObj B) X) := by
  have : IsMonHom ((upperStarFromPoint X).mapIso (mixedDiscreteIso f)).hom := by
    change IsMonHom ((upperStarFromPoint X).map (mixedDiscreteIso f).hom)
    infer_instance
  exact Mon.mkIso' ((upperStarFromPoint X).mapIso (mixedDiscreteIso f))

private theorem mixedPullbackIso_hom (X : Scheme.{u})
    {A : Type u} {B : Type} [CommRing A] [CommRing B] (f : A ≃+* B) :
    (mixedPullbackIso X f).hom.hom =
      (upperStarFromPoint X).map (mixedDiscreteIso f).hom := rfl

attribute [local irreducible] mixedPullbackIso mixedDiscreteIso constantAbFunctor
  discreteIso liftEquiv smallIso

private theorem discreteKernelSquare (X : Scheme.{u})
    {A : Type u} {B : Type} [CommRing A] [CommRing B]
    (f : A ≃+* B) (I : Ideal A) (J : Ideal B) (h : J = Ideal.map f.toRingHom I) :
    (ConstantCompletion.kernelIdeal (IntegralModelsStacks.smallMap X
      ((upperStarFromPoint X).map
        (IntegralModelsStacks.discreteMap (Ideal.Quotient.mk I))))).extension
          (IntegralModelsStacks.smallMap X (mixedPullbackIso X f).hom.hom) =
      ConstantCompletion.kernelIdeal (IntegralModelsStacks.smallMap X
        ((upperStarFromPoint X).map
          (IntegralModelsEmbedded.discreteMap (Ideal.Quotient.mk J)))) := by
  let b := mixedPullbackIso X (Ideal.quotientEquiv I J f h)
  have hs : (mixedPullbackIso X f).hom.hom ≫
      (upperStarFromPoint X).map (IntegralModelsEmbedded.discreteMap
        (Ideal.Quotient.mk J)) =
      (upperStarFromPoint X).map (IntegralModelsStacks.discreteMap
        (Ideal.Quotient.mk I)) ≫ b.hom.hom := by
    dsimp only [b]
    rw [mixedPullbackIso_hom, mixedPullbackIso_hom, ← Functor.map_comp,
      discreteQuotientSquare, Functor.map_comp]
  exact smallKernelSquare X (mixedPullbackIso X f) b _ _ hs

private theorem scalarPullbackSquare (X : Scheme.{u})
    {A : Type u} {B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (e : Profinite.continuousMapRingSheafOfUniverse.{u, u} A ≅
      Profinite.continuousMapRingSheaf.{u} B) (f : A ≃+* B)
    (h : (discreteIso f).hom ≫ IntegralModelsEmbedded.constantToContinuous B =
      IntegralModelsStacks.constantToContinuous A ≫ e.hom) :
    (mixedPullbackIso X f).hom.hom ≫ (upperStarFromPoint X).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (IntegralModelsEmbedded.constantToContinuous B)) =
      (upperStarFromPoint X).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (IntegralModelsStacks.constantToContinuous A)) ≫
      (upperStarFromPoint X).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.hom) := by
  have he := congrArg ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map) h
  simp only [Functor.map_comp] at he
  rw [mixedDiscreteIso_hom] at he
  rw [mixedPullbackIso_hom]
  simpa only [Functor.map_comp] using (upperStarFromPoint X).congr_map he

private theorem coefficientSquares (X : Scheme.{u})
    {A : Type u} {B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (e : Profinite.continuousMapRingSheafOfUniverse.{u, u} A ≅
      Profinite.continuousMapRingSheaf.{u} B)
    (t : (Profinite.continuousMapRingObjOfUniverse.{u, u} A) ⟶
      (Profinite.continuousMapRingObj.{u} B))
    (ht : (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.hom = t)
    (I : Ideal A) (J : Ideal B) (hIJ : ∀ f : A ≃+* B, J = Ideal.map f.toRingHom I) :
    ∃ a : Mon.mk (condensedRingObj (IntegralModelsStacks.discreteObj A) X) ≅
        Mon.mk (condensedRingObj (IntegralModelsEmbedded.discreteObj B) X),
      a.hom.hom ≫ (upperStarFromPoint X).map
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              (IntegralModelsEmbedded.constantToContinuous B)) =
        (upperStarFromPoint X).map
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              (IntegralModelsStacks.constantToContinuous A)) ≫
        (upperStarFromPoint X).map t ∧
      (ConstantCompletion.kernelIdeal (IntegralModelsStacks.smallMap X
        ((upperStarFromPoint X).map
          (IntegralModelsStacks.discreteMap (Ideal.Quotient.mk I))))).extension
            (IntegralModelsStacks.smallMap X a.hom.hom) =
        ConstantCompletion.kernelIdeal (IntegralModelsStacks.smallMap X
          ((upperStarFromPoint X).map
            (IntegralModelsEmbedded.discreteMap (Ideal.Quotient.mk J)))) := by
  obtain ⟨f, hf⟩ := scalarSquare e
  have hs := scalarPullbackSquare X e f hf
  rw [ht] at hs
  exact ⟨mixedPullbackIso X f, hs, discreteKernelSquare X f I J (hIJ f)⟩

private theorem coefficientMonSquares (X : Scheme.{u})
    {A : Type u} {B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (e : Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (Profinite.continuousMapRingSheafOfUniverse.{u, u} A)) ≅
      Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (Profinite.continuousMapRingSheaf.{u} B)))
    (I : Ideal A) (J : Ideal B) (hIJ : ∀ f : A ≃+* B, J = Ideal.map f.toRingHom I) :
    ∃ a : Mon.mk (condensedRingObj (IntegralModelsStacks.discreteObj A) X) ≅
        Mon.mk (condensedRingObj (IntegralModelsEmbedded.discreteObj B) X),
      a.hom.hom ≫ (upperStarFromPoint X).map
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              (IntegralModelsEmbedded.constantToContinuous B)) =
        (upperStarFromPoint X).map
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              (IntegralModelsStacks.constantToContinuous A)) ≫
        (upperStarFromPoint X).map e.hom.hom ∧
      (ConstantCompletion.kernelIdeal (IntegralModelsStacks.smallMap X
        ((upperStarFromPoint X).map
          (IntegralModelsStacks.discreteMap (Ideal.Quotient.mk I))))).extension
            (IntegralModelsStacks.smallMap X a.hom.hom) =
        ConstantCompletion.kernelIdeal (IntegralModelsStacks.smallMap X
          ((upperStarFromPoint X).map
            (IntegralModelsEmbedded.discreteMap (Ideal.Quotient.mk J)))) := by
  let ec : Profinite.continuousMapRingSheafOfUniverse.{u, u} A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    ringSheafIso (C := Profinite.{u})
      (S := Profinite.continuousMapRingSheafOfUniverse.{u, u} A)
      (T := Profinite.continuousMapRingSheaf.{u} B) (coherentTopology Profinite.{u}) e
  have he : (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map ec.hom = e.hom.hom :=
    ringSheafIso_hom (C := Profinite.{u})
      (S := Profinite.continuousMapRingSheafOfUniverse.{u, u} A)
      (T := Profinite.continuousMapRingSheaf.{u} B) (coherentTopology Profinite.{u}) e
  exact coefficientSquares X ec e.hom.hom he I J hIJ

/-- The constant scalar square and equality of the transported first residue kernels.
Source: integral-models-stacks, scalar comparison; Stacks Tag 09C1
(blueprint: lem-sfb-embedded-integral-scalar-kernel-square).

Proof: evaluate the continuous coefficient isomorphism at the one-point profinite set.
Naturality for maps from that point identifies its action on constant functions with
this ring isomorphism. Sheafify the induced constant-ring isomorphism and pull it back
to X. A ring isomorphism preserves nonunits, hence maximal ideals. The uniformizer
hypothesis identifies the embedded first quotient ideal with the maximal ideal, and
the spectral first quotient ideal is its maximal ideal as well. The induced residue
isomorphism gives a commuting quotient square. Apply constant sheafification, inverse
image, and the small section-ring functor to that square. Its horizontal maps are
isomorphisms, so the local characterization of ideal extension identifies the
transported kernel with the embedded kernel.
-/
theorem embeddedIntegralScalarKernelSquare
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)]
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (e : Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E.val) ≅
      sfbCondensedIntegers ℓ (ULift.{u} E.val))
    (X : Scheme.{u}) [IsNoetherian X] :
    ∃ a : Mon.mk (condensedRingObj
        (IntegralModelsStacks.discreteObj
          (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val))) X) ≅
      Mon.mk (condensedRingObj
        (IntegralModelsEmbedded.discreteObj (PadicAlgCl.integers ℓ E.1)) X),
      a.hom.hom ≫ IntegralModelsEmbedded.scalarMap ℓ E X =
        IntegralModelsStacks.scalarMap ℓ (ULift.{u} E.val) X ≫
          (upperStarFromPoint X).map e.inv.hom ∧
      (ConstantCompletion.kernelIdeal (IntegralModelsStacks.smallMap X
        (IntegralModelsStacks.residueMap ℓ (ULift.{u} E.val) X))).extension
          (IntegralModelsStacks.smallMap X a.hom.hom) =
        ConstantCompletion.kernelIdeal (IntegralModelsStacks.smallMap X
          (IntegralModelsEmbedded.residueMap ℓ E π X)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  let := spectralNorm.normedField ℚ_[ℓ] (ULift.{u} E.val)
  let : TopologicalSpace (ULift.{u} E.val) :=
    (spectralNorm.normedField ℚ_[ℓ] (ULift.{u} E.val)).toUniformSpace.toTopologicalSpace
  exact coefficientMonSquares X (A := Padic.coefficientExtensionIntegers ℓ
      (ULift.{u} E.val)) (B := PadicAlgCl.integers ℓ E.val) e.symm
    (Padic.coefficientExtensionIdeal ℓ (ULift.{u} E.val) 1)
    ((Ideal.span {π}) ^ (0 + 1)) (residueIdeal ℓ E π hπ)

end AlgebraicGeometry.ProEtale
