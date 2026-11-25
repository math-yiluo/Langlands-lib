/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.SecondLocalizationMap
import WeilConjectures.Algebra.Homology.SecondLocalizationOrdinaryBSquare
/-! # Ordinary comparison for second localization
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-ordinary-square). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

private theorem map_homology_pi {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (S : ShortComplex C) [S.HasHomology]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq (hl := S.leftHomologyData)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  rw [ShortComplex.LeftHomologyData.mapCyclesIso_eq (hl := S.leftHomologyData)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  change _ ≫ F.map S.leftHomologyData.π ≫ F.map S.leftHomologyData.homologyIso.inv = _
  rw [← F.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
  simp only [Functor.map_comp]

private theorem forget_restrict_cyclesIso
    (E D : Type u) [CommRing E] [CommRing D] (f : E →+* D)
    (S : ShortComplex (ModuleCat.{u} D)) :
    ((S.map (ModuleCat.restrictScalars f)).mapCyclesIso
      (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})).hom ≫
        (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}).map
          (S.mapCyclesIso (ModuleCat.restrictScalars f)).hom =
    (S.mapCyclesIso (forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u})).hom := by
  apply (cancel_mono ((forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}).map S.iCycles)).1
  simp only [Category.assoc]
  rw [← ModuleCat.forget₂_map_restrictScalars f S.iCycles]
  rw [← Functor.map_comp, ShortComplex.mapCyclesIso_hom_iCycles]
  rw [ShortComplex.mapCyclesIso_hom_iCycles]
  rw [ModuleCat.forget₂_map_restrictScalars, ShortComplex.mapCyclesIso_hom_iCycles]
  rfl

private theorem forget_restrict_homologyIso
    (E D : Type u) [CommRing E] [CommRing D] (f : E →+* D)
    (S : ShortComplex (ModuleCat.{u} D)) :
    ((S.map (ModuleCat.restrictScalars f)).mapHomologyIso
      (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})).hom ≫
        (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}).map
          (S.mapHomologyIso (ModuleCat.restrictScalars f)).hom =
    (S.mapHomologyIso (forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u})).hom := by
  apply (cancel_epi (((S.map (ModuleCat.restrictScalars f)).map
    (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})).homologyπ)).1
  rw [← Category.assoc, map_homology_pi (S.map (ModuleCat.restrictScalars f))
    (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})]
  simp only [Category.assoc]
  rw [← Functor.map_comp, map_homology_pi, Functor.map_comp]
  rw [← Category.assoc, forget_restrict_cyclesIso]
  rw [ModuleCat.forget₂_map_restrictScalars]
  exact (map_homology_pi S (forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u})).symm

private theorem forget_comparison_transport
    (B E : Type u) [CommRing B] [CommRing E] (f : B →+* E)
    (M : ModuleCat.{u} E) (X : CochainComplex (ModuleCat.{u} E) ℤ)
    (i : ℤ) (a : M ⟶ X.homology i) :
    (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}).map a ≫
      ((X.sc i).mapHomologyIso (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})).inv =
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map
      ((ModuleCat.restrictScalars f).map a ≫
        ((X.sc i).mapHomologyIso (ModuleCat.restrictScalars f)).inv) ≫
      (((X.sc i).map (ModuleCat.restrictScalars f)).mapHomologyIso
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})).inv := by
  let UE := forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}
  let UB := forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}
  let qE := (X.sc i).mapHomologyIso UE
  let qR := (X.sc i).mapHomologyIso (ModuleCat.restrictScalars f)
  let qB := ((X.sc i).map (ModuleCat.restrictScalars f)).mapHomologyIso UB
  have he : qB ≪≫ UB.mapIso qR = qE := by
    apply Iso.ext
    exact forget_restrict_homologyIso B E f (X.sc i)
  have hi := congrArg (fun e ↦ e.inv) he
  simp only [Iso.trans_inv, Functor.mapIso_inv] at hi
  simp only [Functor.map_comp, ModuleCat.forget₂_map_restrictScalars, Category.assoc]
  exact congrArg (fun k ↦ UE.map a ≫ k) hi.symm

variable (R A B Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra B Bp] [Algebra R Bp]
  [tRB : IsScalarTower R B Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[R] Bp) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

include tRB in
/-- The ordinary counit comparison commutes with flat change of the second coefficient.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change; Tag 0DJ8.
(blueprint: lem-pc-second-localization-ordinary-square).

Proof: exact extension of scalars from B to Bp preserves homology. The defining
leftDerivedLift factorization of secondLocalizationDerivedMap makes its composite
with K.counit equal L.counit extended to Bp and followed by the ordinary scalar
extension associator. Evaluate at the restriction of Q to R and apply degree-i
homology. Naturality of flatDerivedHomologyIso, and of the homotopy and derived
homology factorization isomorphisms, identifies this with the ordinary coefficient
map b tensor x to image(b) tensor x. Transpose the B-to-Bp scalar extension
adjunction: its unit evaluates at 1 tensor x, giving exactly
secondLocalizationCohomologyMap. Substitute comparison_eq for both models and
cancel cohomologyIso. The ordinaryIso_tmul equations identify the coefficient
chain map with φ: precompose with L.ordinaryIso and use tensor induction in each
degree. Exact restriction and forgetting scalars commute with homology, by
naturality of mapHomologyIso and its composition identity (compare their maps on
cycles and the surjective homology projection). This gives the displayed
additive square. This argument precedes extension to D: it uses neither
ordinaryToLocalized nor localizedComparison, and makes no invertibility claim
about either comparison. Identity coefficient maps and zero complexes give the
same counit identity; no flatness of D is required. -/
theorem secondLocalization_ordinary_square (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (φ : ((forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj (((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
          (.up ℤ)).obj Q) ⟶
      ((forget₂ (ModuleCat.{u} (A ⊗[R] Bp)) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj (((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex
          (.up ℤ)).obj Q))
    (hφ : ∀ (j : ℤ) (b : B) (x : Q.X j),
      φ.f j (L.ordinaryIso.hom.f j (b ⊗ₜ[R,algebraMap R B] x)) =
        K.ordinaryIso.hom.f j (algebraMap B Bp b ⊗ₜ[R,algebraMap R Bp] x)) :
    (forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u}).map (L.comparison i) ≫
      (((((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
        (.up ℤ)).obj Q).sc i).mapHomologyIso
          (forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u})).inv ≫
      HomologicalComplex.homologyMap φ i =
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map
      (secondLocalizationCohomologyMap R A B Bp D hflat Q L K i) ≫
      (forget₂ (ModuleCat.{u} (A ⊗[R] Bp)) AddCommGrpCat.{u}).map (K.comparison i) ≫
        (((((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex
          (.up ℤ)).obj Q).sc i).mapHomologyIso
            (forget₂ (ModuleCat.{u} (A ⊗[R] Bp)) AddCommGrpCat.{u})).inv := by
  let X := ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)).obj Q
  let Y := ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex
    (.up ℤ)).obj Q
  let f := (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let g := (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom
  let r := ModuleCat.restrictScalars (algebraMap B Bp)
  let XB := ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj X
  let YBp := ((ModuleCat.restrictScalars g).mapHomologicalComplex (.up ℤ)).obj Y
  let YB := (r.mapHomologicalComplex (.up ℤ)).obj YBp
  let UB := forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}
  let φB : XB ⟶ YB :=
    { f := fun j ↦ ModuleCat.ofHom (X := XB.X j) (Y := YB.X j)
        { toFun := fun z ↦ φ.f j z
          map_add' := fun z z' ↦ (φ.f j).hom.map_add z z'
          map_smul' := by
            intro b z
            obtain ⟨z, rfl⟩ := (CategoryTheory.Iso.toLinearEquiv
              ((HomologicalComplex.eval (ModuleCat.{u} B) (.up ℤ) j).mapIso
                L.ordinaryIso)).surjective z
            induction z using TensorProduct.inductionOn with
            | tmul c x =>
                change B at c
                change Q.X j at x
                change φ.f j (b • L.ordinaryIso.hom.f j
                  (c ⊗ₜ[R,algebraMap R B] x)) =
                  algebraMap B Bp b • (show YBp.X j from
                    φ.f j (L.ordinaryIso.hom.f j (c ⊗ₜ[R,algebraMap R B] x)))
                erw [← map_smul, TensorProduct.smul_tmul', hφ, hφ,
                  ← map_smul, TensorProduct.smul_tmul']
                change K.ordinaryIso.hom.f j (algebraMap B Bp (b * c) ⊗ₜ[R] x) =
                  K.ordinaryIso.hom.f j
                    ((algebraMap B Bp b * algebraMap B Bp c) ⊗ₜ[R] x)
                rw [map_mul]
            | add z z' hz hz' =>
                simp only [map_add, smul_add] at hz hz' ⊢
                rw [hz, hz'] }
      comm' := by
        intro j k hjk
        apply ModuleCat.hom_ext
        ext z
        exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (φ.comm j k)) z }
  have hφB : ∀ (j : ℤ) (b : B) (x : Q.X j),
      φB.f j (L.ordinaryIso.hom.f j (b ⊗ₜ[R,algebraMap R B] x)) =
        K.ordinaryIso.hom.f j (algebraMap B Bp b ⊗ₜ[R,algebraMap R Bp] x) := hφ
  have hL := forget_comparison_transport B (A ⊗[R] B) f
    (L.cohomology i) X i (L.comparison i)
  have hK := forget_comparison_transport Bp (A ⊗[R] Bp) g
    (K.cohomology i) Y i (K.comparison i)
  have hK' := forget_comparison_transport B Bp (algebraMap B Bp)
    ((ModuleCat.restrictScalars g).obj (K.cohomology i)) YBp i
    ((ModuleCat.restrictScalars g).map (K.comparison i) ≫
      ((Y.sc i).mapHomologyIso (ModuleCat.restrictScalars g)).inv)
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} B) (.up ℤ) i).map φB) UB
  have hb := secondLocalization_ordinary_B_square R A B Bp D hflat i Q L K φB hφB
  have hh := congrArg UB.map hb
  simp only [Functor.map_comp] at hh
  rw [← Category.assoc, hL, hK]
  erw [hK']
  change UB.map (HomologicalComplex.homologyMap φB i) ≫
      ((YB.sc i).mapHomologyIso UB).inv =
    ((XB.sc i).mapHomologyIso UB).inv ≫ HomologicalComplex.homologyMap φ i at hn
  simp only [Category.assoc]
  calc
    _ = UB.map ((ModuleCat.restrictScalars f).map (L.comparison i) ≫
        ((X.sc i).mapHomologyIso (ModuleCat.restrictScalars f)).inv) ≫
      UB.map (HomologicalComplex.homologyMap φB i) ≫
        ((YB.sc i).mapHomologyIso UB).inv := by
      exact congrArg (fun k ↦ UB.map ((ModuleCat.restrictScalars f).map
        (L.comparison i) ≫ ((X.sc i).mapHomologyIso
          (ModuleCat.restrictScalars f)).inv) ≫ k) hn.symm
    _ = _ := by
      have hh' := congrArg (fun k ↦ k ≫ ((YB.sc i).mapHomologyIso UB).inv) hh
      have hq : (YB.sc i).mapHomologyIso UB =
          ((YBp.sc i).map r).mapHomologyIso UB := by rfl
      rw [hq] at hh'
      simp only [Functor.map_comp, Category.assoc] at hh' ⊢
      (convert hh' using 1; rfl)

end RingTensorCohomology
