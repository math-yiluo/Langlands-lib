/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.MonoidalCompat

/-! # Slice Koszul compatibility

Source: Stacks Project, Tags 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-koszul-coherence).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe c v u w w' a b x y

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory

namespace CategoryTheory

attribute [local instance 20000] siteAbelianHasSheafify siteAbelianWEqualsLocallyBijective

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

private theorem tensorGenerator_ext
    (P Q F : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (φ ψ : (coefficientTotalTensor.{u, c, v} J A).obj (P, Q) ⟶ F)
    (h : ∀ (p q k : ℤ) (hpq : p + q = k) (V : Cᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      (φ.f k).val.app V (coefficientTensorGenerator.{u, c, v} J A P Q p q k hpq V x y) =
        (ψ.f k).val.app V (coefficientTensorGenerator.{u, c, v} J A P Q p q k hpq V x y)) :
    φ = ψ := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients A
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (R := A) (P.X p) (Q.X q)).inv).mp
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).obj)
  apply (adj.homEquiv ((P.X p).val ⊗ (Q.X q).val) (F.X k)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h p q k hpq V x y

private theorem symmetry_of_iso
    {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
    {H : Dᵒᵖ × D ⥤ D} {HU : Eᵒᵖ × E ⥤ E} {r : D ⥤ E}
    {S : CoefficientClosedStructure H} {SU : CoefficientClosedStructure HU} {K : Prop}
    (d : RingedSliceEvaluationComparisons H HU r S SU K)
    {P Q L M : D} (e : P ≅ L) (e' : Q ≅ M)
    (h : r.map (d.sigma P Q).hom ≫ (d.rho Q P).hom =
      (d.rho P Q).hom ≫ (d.sigmaU (r.obj P) (r.obj Q)).hom) :
    r.map (d.sigma L M).hom ≫ (d.rho M L).hom =
      (d.rho L M).hom ≫ (d.sigmaU (r.obj L) (r.obj M)).hom := by
  let f := e.hom
  let g := e'.hom
  have : IsIso (S.tensor.map (Prod.mkHom f g)) := by
    have : IsIso (Prod.mkHom f g) :=
      (CategoryTheory.isIso_prod_iff (f := Prod.mkHom f g)).mpr
        ⟨inferInstanceAs (IsIso e.hom), inferInstanceAs (IsIso e'.hom)⟩
    infer_instance
  have : IsIso (r.map (S.tensor.map (Prod.mkHom f g))) := inferInstance
  apply (cancel_epi (r.map (S.tensor.map (Prod.mkHom f g)))).mp
  calc
    _ = r.map (d.sigma P Q).hom ≫
        (r.map (S.tensor.map (Prod.mkHom g f)) ≫ (d.rho M L).hom) := by
      rw [← Category.assoc, ← r.map_comp, d.sigma_naturality, r.map_comp]
      simp only [Category.assoc]
    _ = r.map (d.sigma P Q).hom ≫ (d.rho Q P).hom ≫
        SU.tensor.map (Prod.mkHom (r.map g) (r.map f)) := by
      rw [d.rho_naturality]
    _ = (d.rho P Q).hom ≫ (d.sigmaU (r.obj P) (r.obj Q)).hom ≫
        SU.tensor.map (Prod.mkHom (r.map g) (r.map f)) := by
      rw [← Category.assoc, h, Category.assoc]
    _ = (d.rho P Q).hom ≫ SU.tensor.map (Prod.mkHom (r.map f) (r.map g)) ≫
        (d.sigmaU (r.obj L) (r.obj M)).hom := by
      rw [← d.sigmaU_naturality]
    _ = _ := by
      rw [← Category.assoc, ← d.rho_naturality, Category.assoc]

private theorem symmetry_of_models
    {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
    {H : Dᵒᵖ × D ⥤ D} {HU : Eᵒᵖ × E ⥤ E} {r : D ⥤ E}
    {S : CoefficientClosedStructure H} {SU : CoefficientClosedStructure HU} {K : Prop}
    (d : RingedSliceEvaluationComparisons H HU r S SU K)
    {P Q X Y : D} {PU QU XU YU : E}
    (i : X ≅ S.tensor.obj (P, Q)) (i' : Y ≅ S.tensor.obj (Q, P))
    (j : XU ≅ SU.tensor.obj (PU, QU)) (j' : YU ≅ SU.tensor.obj (QU, PU))
    (aP : r.obj P ≅ PU) (aQ : r.obj Q ≅ QU)
    (c : r.obj X ≅ XU) (c' : r.obj Y ≅ YU)
    (β : X ≅ Y) (βU : XU ≅ YU)
    (hr : r.map i.hom ≫ (d.rho P Q).hom ≫
      SU.tensor.map (Prod.mkHom aP.hom aQ.hom) = c.hom ≫ j.hom)
    (hr' : r.map i'.hom ≫ (d.rho Q P).hom ≫
      SU.tensor.map (Prod.mkHom aQ.hom aP.hom) = c'.hom ≫ j'.hom)
    (hs : i.hom ≫ (d.sigma P Q).hom = β.hom ≫ i'.hom)
    (hsU : j.hom ≫ (d.sigmaU PU QU).hom = βU.hom ≫ j'.hom)
    (hc : r.map β.hom ≫ c'.hom = c.hom ≫ βU.hom) :
    r.map (d.sigma P Q).hom ≫ (d.rho Q P).hom =
      (d.rho P Q).hom ≫ (d.sigmaU (r.obj P) (r.obj Q)).hom := by
  have : IsIso (Prod.mkHom aQ.hom aP.hom) :=
    (CategoryTheory.isIso_prod_iff (f := Prod.mkHom aQ.hom aP.hom)).mpr
      ⟨inferInstance, inferInstance⟩
  have : IsIso (SU.tensor.map (Prod.mkHom aQ.hom aP.hom)) := inferInstance
  apply (cancel_epi (r.map i.hom)).mp
  apply (cancel_mono (SU.tensor.map (Prod.mkHom aQ.hom aP.hom))).mp
  calc
    _ = r.map β.hom ≫
        (r.map i'.hom ≫ (d.rho Q P).hom ≫
          SU.tensor.map (Prod.mkHom aQ.hom aP.hom)) := by
      simp only [← r.map_comp, ← Category.assoc, hs]
    _ = r.map β.hom ≫ c'.hom ≫ j'.hom := by rw [hr']
    _ = c.hom ≫ βU.hom ≫ j'.hom := by rw [← Category.assoc, hc, Category.assoc]
    _ = c.hom ≫ j.hom ≫ (d.sigmaU PU QU).hom := by
      rw [← hsU]
    _ = _ := by
      rw [← Category.assoc, ← hr]
      simp only [Category.assoc]
      rw [d.sigmaU_naturality]

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
  CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

attribute [local irreducible] coefficientTotalTensor ringedSliceDerivedRestriction

-- The representative squares compare long dependent tensor endpoints at independent universes.
set_option backward.isDefEq.respectTransparency.types true in
/-- Restriction preserves the normalized Koszul exchange.
Source: Stacks Project, Tags 06YN and 07A4
(blueprint: lem-weil-pbc-ringed-slice-koszul-coherence).
Proof: compare the two chain maps on sheafified pure-tensor summands. Both send
x tensor y in bidegree (p,q) to (-1)^(pq) y tensor x. The representative squares
for rho and both symmetries identify their localizations. Naturality transports
this equality along flat-term K-flat resolutions to arbitrary derived objects. -/
theorem ringedSlice_koszul_coherence
    (U : C) [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU
      (RingedSliceFlatRestriction.{c, v, u} J A U))
    (hd : RingedSliceEvaluationNormalized.{c, v, u, w, w'} J A U S T SU TU d)
    (L M : DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj A))) :
    (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map (d.sigma L M).hom ≫
        (d.rho M L).hom =
      (d.rho L M).hom ≫
        (d.sigmaU ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj L)
          ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj M)).hom := by
  classical
  let r := ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U
  let R := ringedSliceComplexRestriction.{c, v, u} J A U
  let α := ringedSliceLocalizationIso.{c, v, u, w, w'} J A U
  have base
      (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
        CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q)
      (fP : ∀ n, SheafOfModules.IsFlatOnSite (J := J) (R := A) (P.X n))
      (fQ : ∀ n, SheafOfModules.IsFlatOnSite (J := J) (R := A) (Q.X n)) :
      r.map (d.sigma (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
          (d.rho (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)).hom =
        (d.rho (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
          (d.sigmaU (r.obj (DerivedCategory.Q.obj P)) (r.obj (DerivedCategory.Q.obj Q))).hom := by
    -- Share the representatives and project their specifications without dependent elimination.
    have hγ := hd.1 P Q hP hQ fP fQ
    let γ := hγ.choose
    have hρ := hγ.choose_spec.2
    have hγ := hγ.choose_spec.1
    have hγ' := hd.1 Q P hQ hP fQ fP
    let γ' := hγ'.choose
    have hρ' := hγ'.choose_spec.2
    have hγ' := hγ'.choose_spec.1
    have hβ := hd.2.2.1 P Q hP hQ
    let β := hβ.choose
    have hσ := hβ.choose_spec.2
    have hβ := hβ.choose_spec.1
    have hβU := hd.2.2.2 (R.obj P) (R.obj Q)
      (d.kflat P hP fP).1 (d.kflat Q hQ fQ).1
    let βU := hβU.choose
    have hσU := hβU.choose_spec.2
    have hβU := hβU.choose_spec.1
    have hchain : R.map β.hom ≫ γ'.hom = γ.hom ≫ βU.hom := by
      apply (cancel_epi γ.inv).mp
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      apply tensorGenerator_ext.{max c v, v, u} (J.over U) (A.over U)
      intro p q k hpq V x y
      have hi : (γ.inv.f k).val.app V
          (coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
            (R.obj P) (R.obj Q) p q k hpq V x y) =
          coefficientTensorGenerator.{u, c, v} J A P Q p q k hpq (op V.unop.left) x y := by
        calc
          _ = (γ.inv.f k).val.app V ((γ.hom.f k).val.app V
              (coefficientTensorGenerator.{u, c, v} J A P Q p q k hpq
                (op V.unop.left) x y)) := by
            exact congrArg ((γ.inv.f k).val.app V) (hγ p q k hpq V.unop x y).symm
          _ = _ := by
            have h := congrArg (fun f ↦ (f.f k).val.app V
              (coefficientTensorGenerator.{u, c, v} J A P Q p q k hpq
                (op V.unop.left) x y)) γ.hom_inv_id
            set_option backward.isDefEq.respectTransparency.types false in
            simpa only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
              PresheafOfModules.comp_app, ModuleCat.comp_apply,
              HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
              ModuleCat.id_apply] using h
      simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
        PresheafOfModules.comp_app, ModuleCat.comp_apply]
      rw [hi]
      change (γ'.hom.f k).val.app V
          ((β.hom.f k).val.app (op V.unop.left)
            (coefficientTensorGenerator.{u, c, v} J A P Q p q k hpq
              (op V.unop.left) x y)) = _
      calc
        _ = (γ'.hom.f k).val.app V ((p * q).negOnePow •
            coefficientTensorGenerator.{u, c, v} J A Q P q p k (by omega)
              (op V.unop.left) y x) :=
          congrArg ((γ'.hom.f k).val.app V)
            (hβ p q k hpq (by omega) (op V.unop.left) x y)
        _ = (p * q).negOnePow • (γ'.hom.f k).val.app V
            (coefficientTensorGenerator.{u, c, v} J A Q P q p k (by omega)
              (op V.unop.left) y x) := map_zsmul_unit _ _ _
        _ = (p * q).negOnePow •
            coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
              (R.obj Q) (R.obj P) q p k (by omega) V y x := by
          have hc := hγ' q p k (by omega) V.unop y x
          simp only [op_unop] at hc
          exact congrArg ((p * q).negOnePow • ·) hc
        _ = _ := (hβU p q k hpq (by omega) V x y).symm
    apply symmetry_of_models d
      (T.iso J A S P Q hP hQ) (T.iso J A S Q P hQ hP)
      (TU.iso (J.over U) (A.over U) SU (R.obj P) (R.obj Q)
        (d.kflat P hP fP).1 (d.kflat Q hQ fQ).1)
      (TU.iso (J.over U) (A.over U) SU (R.obj Q) (R.obj P)
        (d.kflat Q hQ fQ).1 (d.kflat P hP fP).1)
      (α.app P) (α.app Q)
      ((α.app _) ≪≫ DerivedCategory.Q.mapIso γ)
      ((α.app _) ≪≫ DerivedCategory.Q.mapIso γ')
      (DerivedCategory.Q.mapIso β) (DerivedCategory.Q.mapIso βU)
    · simpa only [α, R, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Prod.mkHom,
        Category.assoc] using hρ
    · simpa only [α, R, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Prod.mkHom,
        Category.assoc] using hρ'
    · exact hσ
    · exact hσU
    · have hn := α.hom.naturality β.hom
      change r.map (DerivedCategory.Q.map β.hom) ≫ α.hom.app _ =
        α.hom.app _ ≫ DerivedCategory.Q.map (R.map β.hom) at hn
      change r.map (DerivedCategory.Q.map β.hom) ≫
          (α.hom.app _ ≫ DerivedCategory.Q.map γ'.hom) =
        (α.hom.app _ ≫ DerivedCategory.Q.map γ.hom) ≫ DerivedCategory.Q.map βU.hom
      rw [← Category.assoc, hn]
      simp only [Category.assoc]
      have hh := congrArg (fun f ↦ DerivedCategory.Q.map f) hchain
      simp only [Functor.map_comp] at hh
      exact congrArg (α.hom.app _ ≫ ·) hh
  let X := DerivedCategory.Q.objPreimage L
  let Y := DerivedCategory.Q.objPreimage M
  obtain ⟨P, f, hP, fP, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := A) X
  obtain ⟨Q, g, hQ, fQ, hg, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := A) Y
  have : QuasiIso f := hf
  have : QuasiIso g := hg
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hf
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hg
  let e := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso L
  let e' := asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  apply symmetry_of_iso d e e'
  apply base P Q hP hQ
  · intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso A (P.X n)).symm (fP n)
  · intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso A (Q.X n)).symm (fQ n)

end CategoryTheory
