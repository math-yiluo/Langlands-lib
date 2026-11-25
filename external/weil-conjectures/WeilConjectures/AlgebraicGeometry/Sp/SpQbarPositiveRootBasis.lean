/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement

import WeilConjectures.AlgebraicGeometry.Sp.SpRationalRootDiagramBasis
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import all WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence

/-! # Positive signed degrees from a compatible algebraic-closure root tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u c v i j

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance 20000] HasLimitsOfShape.has_limit HasColimitsOfShape.has_colimit
attribute [local instance 20000] Sheaf.instHasLimitsOfShape AddCommGrpCat.hasLimitsOfShape

namespace AlgebraicGeometry.ProEtale

private def colimitBasisIso
    {C : Type c} [Category.{v} C] [MonoidalCategory C]
    {I : Type i} [Category.{j} I] [IsSifted I]
    (A M : I ⥤ C) [∀ i, MonObj (A.obj i)] [∀ i, ModObj (A.obj i) (M.obj i)]
    (cA : Cocone A) (cM : Cocone M) (hA : IsColimit cA) (hM : IsColimit cM)
    [MonObj cA.pt] [ModObj cA.pt cM.pt]
    [PreservesColimit₂ A A (curriedTensor C)]
    (hcoeff : ∀ i, (cA.ι.app i ⊗ₘ cA.ι.app i) ≫ MonObj.mul (X := cA.pt) =
      MonObj.mul (X := A.obj i) ≫ cA.ι.app i)
    (hact : ∀ i, (cA.ι.app i ⊗ₘ cM.ι.app i) ≫ Mod.act (A := cA.pt) cM.pt =
      Mod.act (M.obj i) ≫ cM.ι.app i)
    (b : A ≅ M)
    (hb : ∀ i, MonObj.mul ≫ b.hom.app i =
      A.obj i ◁ b.hom.app i ≫ Mod.act (M.obj i)) :
    Mod.regular cA.pt ≅ ({ X := cM.pt, mod := inferInstance } : Mod C cA.pt) := by
  let c := (Cocone.precompose b.hom).obj cM
  have hc : IsColimit c := (IsColimit.precomposeHomEquiv b cM).symm hM
  let e := hA.coconePointUniqueUpToIso hc
  have he (i : I) : cA.ι.app i ≫ e.hom = b.hom.app i ≫ cM.ι.app i :=
    hA.comp_coconePointUniqueUpToIso_hom hc i
  apply Mod.isoMk e
  apply (hA.tensor hA).hom_ext
  intro i
  change (cA.ι.app i ⊗ₘ cA.ι.app i) ≫ MonObj.mul (X := cA.pt) ≫ e.hom =
    (cA.ι.app i ⊗ₘ cA.ι.app i) ≫ cA.pt ◁ e.hom ≫ Mod.act (A := cA.pt) cM.pt
  rw [reassoc_of% hcoeff i, he]
  calc
    MonObj.mul (X := A.obj i) ≫ b.hom.app i ≫ cM.ι.app i =
        A.obj i ◁ b.hom.app i ≫ Mod.act (M.obj i) ≫ cM.ι.app i := by rw [reassoc_of% hb i]
    _ = A.obj i ◁ b.hom.app i ≫
        (cA.ι.app i ⊗ₘ cM.ι.app i) ≫ Mod.act (A := cA.pt) cM.pt := by rw [hact]
    _ = _ := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
        Category.id_comp, he]
      simp

private def mapColimitBasisIso
    {C : Type c} [Category.{v} C] [MonoidalCategory C]
    {D : Type*} [Category D] [MonoidalCategory D]
    {I : Type i} [Category.{j} I] [IsSifted I]
    (F : C ⥤ D) [F.LaxMonoidal] [PreservesColimitsOfShape I F]
    (A M : I ⥤ C) [∀ i, MonObj (A.obj i)] [∀ i, ModObj (A.obj i) (M.obj i)]
    (cA : Cocone A) (cM : Cocone M) (hA : IsColimit cA) (hM : IsColimit cM)
    [MonObj cA.pt] [ModObj cA.pt cM.pt]
    [PreservesColimit₂ (A ⋙ F) (A ⋙ F) (curriedTensor D)]
    (hcoeff : ∀ i, (cA.ι.app i ⊗ₘ cA.ι.app i) ≫ MonObj.mul (X := cA.pt) =
      MonObj.mul (X := A.obj i) ≫ cA.ι.app i)
    (hact : ∀ i, (cA.ι.app i ⊗ₘ cM.ι.app i) ≫ Mod.act (A := cA.pt) cM.pt =
      Mod.act (M.obj i) ≫ cM.ι.app i)
    (b : A ⋙ F ≅ M ⋙ F)
    (hb : ∀ i, Functor.LaxMonoidal.μ F (A.obj i) (A.obj i) ≫
      F.map (MonObj.mul (X := A.obj i)) ≫ b.hom.app i =
      F.obj (A.obj i) ◁ b.hom.app i ≫
        Functor.LaxMonoidal.μ F (A.obj i) (M.obj i) ≫ F.map (Mod.act (M.obj i))) :
    Mod.regular (F.obj cA.pt) ≅
      (F.mapMod cA.pt).obj ({ X := cM.pt, mod := inferInstance } : Mod C cA.pt) := by
  letI : ∀ i, MonObj ((A ⋙ F).obj i) := fun i ↦ F.monObjObj (A.obj i)
  letI : ∀ i, ModObj ((A ⋙ F).obj i) ((M ⋙ F).obj i) :=
    fun i ↦ F.modObjObj (A := A.obj i) (M.obj i)
  letI : MonObj (F.mapCocone cA).pt := F.monObjObj cA.pt
  letI : ModObj (F.mapCocone cA).pt (F.mapCocone cM).pt :=
    F.modObjObj (A := cA.pt) cM.pt
  refine colimitBasisIso (A ⋙ F) (M ⋙ F) (F.mapCocone cA) (F.mapCocone cM)
    (isColimitOfPreserves F hA) (isColimitOfPreserves F hM) ?_ ?_ b ?_
  · intro i
    change (F.map (cA.ι.app i) ⊗ₘ F.map (cA.ι.app i)) ≫
        (Functor.LaxMonoidal.μ F cA.pt cA.pt ≫ F.map MonObj.mul) =
      (Functor.LaxMonoidal.μ F (A.obj i) (A.obj i) ≫
        F.map MonObj.mul) ≫ F.map (cA.ι.app i)
    simp only [Category.assoc]
    have hn : (F.map (cA.ι.app i) ⊗ₘ F.map (cA.ι.app i)) ≫
        Functor.LaxMonoidal.μ F cA.pt cA.pt =
      Functor.LaxMonoidal.μ F (A.obj i) (A.obj i) ≫
        F.map (cA.ι.app i ⊗ₘ cA.ι.app i) :=
      Functor.LaxMonoidal.μ_natural F (cA.ι.app i) (cA.ι.app i)
    rw [reassoc_of% hn, ← F.map_comp, hcoeff, F.map_comp]
  · intro i
    change (F.map (cA.ι.app i) ⊗ₘ F.map (cM.ι.app i)) ≫
        (Functor.LaxMonoidal.μ F cA.pt cM.pt ≫ F.map (Mod.act cM.pt)) =
      (Functor.LaxMonoidal.μ F (A.obj i) (M.obj i) ≫
        F.map (Mod.act (M.obj i))) ≫ F.map (cM.ι.app i)
    simp only [Category.assoc]
    have hn : (F.map (cA.ι.app i) ⊗ₘ F.map (cM.ι.app i)) ≫
        Functor.LaxMonoidal.μ F cA.pt cM.pt =
      Functor.LaxMonoidal.μ F (A.obj i) (M.obj i) ≫
        F.map (cA.ι.app i ⊗ₘ cM.ι.app i) :=
      Functor.LaxMonoidal.μ_natural F (cA.ι.app i) (cM.ι.app i)
    rw [reassoc_of% hn, ← F.map_comp, hact, F.map_comp]
  · intro i
    change (Functor.LaxMonoidal.μ F (A.obj i) (A.obj i) ≫ F.map MonObj.mul) ≫
        b.hom.app i = F.obj (A.obj i) ◁ b.hom.app i ≫
          Functor.LaxMonoidal.μ F (A.obj i) (M.obj i) ≫ F.map (Mod.act (M.obj i))
    simpa only [Category.assoc] using hb i

private theorem slicePreservesColimits (X : Scheme.{u}) (W : X.ProEt) :
    PreservesColimitsOfSize.{0, 0}
      ((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W) := by
  let : ((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W).IsLeftAdjoint :=
    ((Over.forgetAdjStar W).sheafPushforwardContinuous
      ((Scheme.ProEt.topology X).over W) (Scheme.ProEt.topology X)
      (E := AddCommGrpCat.{u + 1})).isLeftAdjoint
  infer_instance

private def sliceModuleIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R)
    (W : X.ProEt)
    (e : (((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W).mapMod R).obj M ≅
      (((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W).mapMod R).obj N) :
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor.obj M).over W ≅
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor.obj N).over W := by
  let J := Scheme.ProEt.topology X
  let O := J.overPullback AddCommGrpCat.{u + 1} W
  let G := sheafToPresheaf (J.over W) AddCommGrpCat.{u + 1}
  let H := sheafToPresheaf J AddCommGrpCat.{u + 1}
  let S := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R).functor
  let f : O.obj M.X ⟶ O.obj N.X := e.hom.hom
  have lin (V : (Over W)ᵒᵖ) (r : (InternalAbelianSheafModule.sectionRings J R).obj (op V.unop.left))
      (m : ((S.obj M).over W).val.obj V) :
      f.hom.app V (r • m) =
        r • (show ((S.obj N).over W).val.obj V from f.hom.app V m) := by
    have h : Functor.LaxMonoidal.μ O R M.X ≫ O.map (Mod.act M.X) ≫ f =
        O.obj R ◁ f ≫ Functor.LaxMonoidal.μ O R N.X ≫ O.map (Mod.act N.X) :=
      Mod.act_hom e.hom
    have hh := congrArg (fun f ↦
      Functor.LaxMonoidal.μ G (O.obj R) (O.obj M.X) ≫ G.map f) h
    simp only [Functor.map_comp] at hh
    rw [← Functor.LaxMonoidal.μ_natural_right_assoc] at hh
    have hhV := congr_app hh V
    simp only [NatTrans.comp_app] at hhV
    have hμ (P T : Sheaf J AddCommGrpCat.{u + 1}) :
        (Functor.LaxMonoidal.μ G (O.obj P) (O.obj T)).app V ≫
            (G.map (Functor.LaxMonoidal.μ O P T)).app V =
          (Functor.LaxMonoidal.μ H P T).app (op V.unop.left) :=
      Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
        (Over.forget W) AddCommGrpCat.{u + 1} (J.over W) J P T V
    rw [reassoc_of% hμ R M.X, reassoc_of% hμ R N.X] at hhV
    exact ConcreteCategory.congr_hom hhV (r ⊗ₜ[ℤ] m)
  let i : ((S.obj M).over W).val ≅ ((S.obj N).over W).val :=
    PresheafOfModules.isoMk
      (fun V ↦ ModuleCat.isoMk
        (((G.mapIso ((Mod.forget (O.obj R)).mapIso e))).app V)
          (by intro r; ext m; exact (lin V r m).symm))
      (by
        intro V V' f
        ext m
        exact ConcreteCategory.congr_hom (e.hom.hom.hom.naturality f) m)
  exact
    { hom := ⟨i.hom⟩
      inv := ⟨i.inv⟩
      hom_inv_id := SheafOfModules.hom_ext i.hom_inv_id
      inv_hom_id := SheafOfModules.hom_ext i.inv_hom_id }

set_option backward.isDefEq.respectTransparency true in
private def sectionUnitIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor.obj (Mod.regular R) ≅
        SheafOfModules.unit.{u, u + 1, u + 1} ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
              (Scheme.ProEt.topology X) R)) := by
  let F := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) R).functor
  let i : (F.obj (Mod.regular R)).val ≅
      (SheafOfModules.unit.{u, u + 1, u + 1} _).val :=
    PresheafOfModules.isoMk
      (fun _ ↦ ModuleCat.isoMk (Iso.refl _) (by intro r; ext x; rfl))
      (by intro U V f; rfl)
  exact
    { hom := ⟨i.hom⟩
      inv := ⟨i.inv⟩
      hom_inv_id := SheafOfModules.hom_ext i.hom_inv_id
      inv_hom_id := SheafOfModules.hom_ext i.inv_hom_id }

/-- A compatible root tower trivializes every positive signed degree of the
algebraic-closure coefficient twist on the prescribed slice.

Source: blueprint latest, sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md, clause (3), positive tensor powers
of the compatible algebraic-closure basis.
(blueprint: lem-sp-qbar-positive-root-basis)

Proof: construct the normalized finite-level pure-tensor maps from the supplied
root sections and module isomorphisms. Their transition identities give inverse
maps on the inverse-limit and finite-subextension diagrams. The compatible
maps therefore identify the colimit twist with its coefficient unit. Tensoring
this degree-one identification repeatedly gives every positive signed degree;
the sectionwise/internal equivalence preserves the resulting isomorphisms.
The details are split from the degree-one use in `spQbarRootBasis` so the
finite-level and colimit constructions can be proved independently. -/
theorem spQbarPositiveRootBasis
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)] (W : X.ProEt)
    (ζ : ∀ n : ℕ, (Scheme.purTwistRootsModule X ℓ n).val.obj (op W))
    (e : ∀ n : ℕ,
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n))).over W ≅
        (Scheme.purTwistRootsModule X ℓ n).over W)
    (hζ : ∀ n : ℕ,
      (Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op W) (ζ (n + 1)) = ζ n)
    (he : ∀ (n : ℕ) (V : (Over W)ᵒᵖ)
      (a : ((Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)).over W).obj.obj V),
      (e n).hom.val.app V a =
        a • (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n))
    (d : ℕ) :
    Nonempty ((spSignedTwist X _ (spQbarTwist X ℓ) (d + 1)).over W ≅
      (spSignedTwist X _ (spQbarTwist X ℓ) 0).over W) := by
  let R := condensedRingObj.{u} (Profinite.padicAlgClRingObj.{u} ℓ) X
  let Q := spQbarTwist X ℓ
  let A := Profinite.padicSubfieldRingObjFunctor.{u} ℓ ⋙ upperStarFromPoint X
  let M := spRationalTwistDiagram X ℓ
  let O := (Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W
  let : IsSifted (PadicAlgCl.FiniteIntermediateField ℓ) := IsFiltered.isSifted
  let : ∀ E, MonObj (A.obj E) := by
    change ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      MonObj (condensedRingObj.{u} (Profinite.continuousMapRingObj.{u} E.1) X)
    infer_instance
  let : ∀ E, ModObj (A.obj E) (M.obj E) := by
    change ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      ModObj (condensedRingObj.{u} (Profinite.continuousMapRingObj.{u} E.1) X)
        (spRationalTwist X ℓ E).X
    exact fun E ↦ (spRationalTwist X ℓ E).mod
  let cA := (upperStarFromPoint X).mapCocone (Profinite.padicAlgClRingObjCocone ℓ)
  let cM := colimit.cocone M
  let : MonObj cA.pt := by
    change MonObj R
    infer_instance
  let : ModObj cA.pt cM.pt := Q.mod
  let : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).isLeftAdjoint
  let : PreservesColimitsOfSize.{0, 0} O := slicePreservesColimits X W
  have hA : IsColimit cA := isColimitOfPreserves (upperStarFromPoint X)
    (Profinite.isColimitPadicAlgClRingObjCocone ℓ)
  have hcoeff (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      (cA.ι.app E ⊗ₘ cA.ι.app E) ≫ MonObj.mul (X := R) =
        MonObj.mul (X := A.obj E) ≫ cA.ι.app E := by
    exact (IsMonHom.mul_hom
      (coefficientMap.{u} (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)).symm
  have hact (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      (cA.ι.app E ⊗ₘ cM.ι.app E) ≫ Q.mod.smul =
        (spRationalTwist X ℓ E).mod.smul ≫ cM.ι.app E := by
    change (coefficientMap.{u} (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X ⊗ₘ
      colimit.ι (spRationalTwistDiagram X ℓ) E) ≫
        (spQbarTwistAction_existsUnique X ℓ).exists.choose.smul =
      Mod.act (spRationalTwist X ℓ E).X ≫ colimit.ι (spRationalTwistDiagram X ℓ) E
    simpa only [Profinite.padicSubfieldRingObjMap_id, coefficientMap_id,
      spRationalTwistMap_id, id_tensorHom_id, Category.id_comp] using
      (spQbarTwistAction_existsUnique X ℓ).exists.choose_spec E E E (le_refl E) (le_refl E)
  obtain ⟨b, hb⟩ := spRationalRootDiagramBasis X ℓ W ζ e hζ he
  let eQ : Mod.regular (O.obj R) ≅ (O.mapMod R).obj Q :=
    mapColimitBasisIso O A M cA cM hA (colimit.isColimit M) hcoeff hact b hb
  let eS := sliceModuleIso X R (Mod.regular R) Q W eQ
  let U := (SheafOfModules.overFunctor _ W).mapIso (sectionUnitIso X R)
  let bQ := eS.symm ≪≫ U
  let S := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) R
  let L := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) R).functor.obj Q
  exact ⟨WeilConjectures.linePowerOverUnit X S L W bQ (d + 1)⟩

end AlgebraicGeometry.ProEtale
