/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleScalar.ConstantModuleScalarCenter
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import WeilConjectures.CategoryTheory.ConstantModuleScalar.ConstantScalarCoordinates

/-! # Normalized finite-basis inclusions for exact constant scalar extension -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w i
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RingedCoefficientCounit
open scoped ChangeOfRings

namespace CategoryTheory.ConstantModuleScalar

section Normalized

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {A B : CommRingCat.{r}} [Algebra A B]
  [HasDerivedCategory.{w} (modules (constantRing J A))]
  [HasDerivedCategory.{w} (modules (constantRing J B))]

/-- The coordinate projection on the chosen model of extension of scalars. -/
def projE (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      (constAlgebraMap J A B)) (q : B →ₗ[A] A) (M : modules (constantRing J A)) :
    (restriction (constAlgebraMap J A B)).obj (D.E.obj M) ⟶ M :=
  (restriction (constAlgebraMap J A B)).map (eqToHom (D.obj_eq M)) ≫ proj J A B q M

theorem projE_naturality (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      (constAlgebraMap J A B)) (q : B →ₗ[A] A) {M N : modules (constantRing J A)}
    (f : M ⟶ N) :
    (restriction (constAlgebraMap J A B)).map (D.E.map f) ≫ projE D q N =
      projE D q M ≫ f := by
  rw [projE, projE, D.map_eq]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [proj_naturality]

/-- The coordinate projection on unbounded cochain complexes. -/
def projC (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      (constAlgebraMap J A B)) (q : B →ₗ[A] A)
    (K : CochainComplex (modules (constantRing J A)) ℤ) :
    ((restriction (constAlgebraMap J A B)).mapHomologicalComplex (.up ℤ)).obj
      ((D.E.mapHomologicalComplex (.up ℤ)).obj K) ⟶ K where
  f n := projE D q (K.X n)
  comm' i j _ := (projE_naturality D q (K.d i j)).symm

theorem projC_f (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      (constAlgebraMap J A B)) (q : B →ₗ[A] A)
    (K : CochainComplex (modules (constantRing J A)) ℤ) (n : ℤ) :
    (projC D q K).f n = projE D q (K.X n) := rfl

/-- The basis inclusion on unbounded cochain complexes, as the localized-unit model:
the termwise unit followed by multiplication by the basis vector. -/
def inclC (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      (constAlgebraMap J A B))
    (a : D.E ⊣ restriction (constAlgebraMap J A B)) (c : B)
    (K : CochainComplex (modules (constantRing J A)) ℤ) :
    K ⟶ ((restriction (constAlgebraMap J A B)).mapHomologicalComplex (.up ℤ)).obj
      ((D.E.mapHomologicalComplex (.up ℤ)).obj K) :=
  (a.mapHomologicalComplex (.up ℤ)).unit.app K ≫
    ((restriction (constAlgebraMap J A B)).mapHomologicalComplex (.up ℤ)).map
      ((cochain J B c).app ((D.E.mapHomologicalComplex (.up ℤ)).obj K))

theorem inclC_f (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      (constAlgebraMap J A B))
    (a : D.E ⊣ restriction (constAlgebraMap J A B)) (c : B)
    (hk : ∀ M, a.unit.app M ≫ (restriction (constAlgebraMap J A B)).map
      ((ordinary J B c).app (D.E.obj M)) =
        incl J A B c M ≫ (restriction (constAlgebraMap J A B)).map (eqToHom (D.obj_eq M).symm))
    (K : CochainComplex (modules (constantRing J A)) ℤ) (n : ℤ) :
    (inclC D a c K).f n =
      incl J A B c (K.X n) ≫
        (restriction (constAlgebraMap J A B)).map (eqToHom (D.obj_eq (K.X n)).symm) := by
  rw [← hk]
  rfl

theorem inclC_projC (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      (constAlgebraMap J A B))
    (a : D.E ⊣ restriction (constAlgebraMap J A B)) {I : Type i} (b : Module.Basis I A B)
    (hk : ∀ c M, a.unit.app M ≫ (restriction (constAlgebraMap J A B)).map
      ((ordinary J B (b c)).app (D.E.obj M)) =
        incl J A B (b c) M ≫
          (restriction (constAlgebraMap J A B)).map (eqToHom (D.obj_eq M).symm))
    (K : CochainComplex (modules (constantRing J A)) ℤ) (c d : I) :
    inclC D a (b c) K ≫ projC D (b.coord d) K =
      @ite _ (c = d) (Classical.propDecidable _) (𝟙 K) 0 := by
  ext n : 1
  rw [HomologicalComplex.comp_f, inclC_f D a (b c) (hk c), projC_f, projE, Category.assoc,
    ← Functor.map_comp_assoc, eqToHom_trans, eqToHom_refl, Functor.map_id, Category.id_comp]
  by_cases h : c = d
  · subst h
    rw [ite_eq_left rfl, incl_proj_self]
    rfl
  · rw [ite_eq_right h, incl_proj_of_ne J A B b h]
    rfl

theorem sum_projC_inclC (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      (constAlgebraMap J A B))
    (a : D.E ⊣ restriction (constAlgebraMap J A B)) {I : Type i} [Fintype I]
    (b : Module.Basis I A B)
    (hk : ∀ c M, a.unit.app M ≫ (restriction (constAlgebraMap J A B)).map
      ((ordinary J B (b c)).app (D.E.obj M)) =
        incl J A B (b c) M ≫
          (restriction (constAlgebraMap J A B)).map (eqToHom (D.obj_eq M).symm))
    (K : CochainComplex (modules (constantRing J A)) ℤ) :
    ∑ c, projC D (b.coord c) K ≫ inclC D a (b c) K = 𝟙 _ := by
  ext n : 1
  have h := Functor.map_sum (HomologicalComplex.eval _ (.up ℤ) n)
    (fun c ↦ projC D (b.coord c) K ≫ inclC D a (b c) K) Finset.univ
  simp only [HomologicalComplex.eval_map, HomologicalComplex.comp_f] at h
  have h2 (c : I) : (projC D (b.coord c) K).f n ≫ (inclC D a (b c) K).f n =
      (restriction (constAlgebraMap J A B)).map (eqToHom (D.obj_eq (K.X n))) ≫
        (proj J A B (b.coord c) (K.X n) ≫ incl J A B (b c) (K.X n)) ≫
          (restriction (constAlgebraMap J A B)).map (eqToHom (D.obj_eq (K.X n)).symm) := by
    rw [projC_f, inclC_f D a (b c) (hk c), projE]
    simp only [Category.assoc]
  rw [h, HomologicalComplex.id_f, Finset.sum_congr rfl (fun c _ ↦ h2 c), ← Preadditive.comp_sum,
    ← Preadditive.sum_comp, sum_proj_incl, Category.id_comp, ← Functor.map_comp, eqToHom_trans,
    eqToHom_refl, Functor.map_id]
  rfl

theorem sum_Q_projC_inclC
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      (constAlgebraMap J A B))
    (a : D.E ⊣ restriction (constAlgebraMap J A B)) {I : Type i} [Fintype I]
    (b : Module.Basis I A B)
    (hk : ∀ c M, a.unit.app M ≫ (restriction (constAlgebraMap J A B)).map
      ((ordinary J B (b c)).app (D.E.obj M)) =
        incl J A B (b c) M ≫
          (restriction (constAlgebraMap J A B)).map (eqToHom (D.obj_eq M).symm))
    (K : CochainComplex (modules (constantRing J A)) ℤ) :
    ∑ c, DerivedCategory.Q.map (projC D (b.coord c) K ≫ inclC D a (b c) K) = 𝟙 _ := by
  rw [← Functor.map_sum, sum_projC_inclC D a b hk, Functor.map_id]

theorem unit_center_comp
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      (constAlgebraMap J A B))
    [PreservesFiniteLimits D.E] [PreservesFiniteColimits D.E]
    [PreservesFiniteLimits (restriction (constAlgebraMap J A B))]
    [PreservesFiniteColimits (restriction (constAlgebraMap J A B))]
    (a : D.E ⊣ restriction (constAlgebraMap J A B)) (c : B)
    (K : CochainComplex (modules (constantRing J A)) ℤ) :
    (a.onDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
      (restriction (constAlgebraMap J A B)).mapDerivedCategory.map
        ((derived J B c).app (D.E.mapDerivedCategory.obj (DerivedCategory.Q.obj K)))) ≫
      (restriction (constAlgebraMap J A B)).mapDerivedCategory.map
        (D.E.mapDerivedCategoryFactors.hom.app K) ≫
      (restriction (constAlgebraMap J A B)).mapDerivedCategoryFactors.hom.app
        ((D.E.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map (inclC D a c K) := by
  have hu : a.onDerivedCategory.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        (restriction (constAlgebraMap J A B)).mapDerivedCategoryFactors.inv.app
          ((D.E.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (restriction (constAlgebraMap J A B)).mapDerivedCategory.map
          (D.E.mapDerivedCategoryFactors.inv.app K) := by
    simp only [Adjunction.onDerivedCategory, Adjunction.localization_unit_app]
    rfl
  have hz : (derived J B c).app (D.E.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      D.E.mapDerivedCategoryFactors.hom.app K =
        D.E.mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map
            ((cochain J B c).app ((D.E.mapHomologicalComplex (.up ℤ)).obj K)) := by
    rw [derived]
    refine (((cochain J B c).localization DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))).naturality
        (D.E.mapDerivedCategoryFactors.hom.app K)).symm.trans ?_
    exact congrArg (D.E.mapDerivedCategoryFactors.hom.app K ≫ ·)
      (CatCenter.localization_app _ _ _ _)
  rw [hu]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  rw [hz, Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp]
  rfl


end Normalized

/-- The scalar-unit inclusions are finite-biproduct inclusions with their prescribed
pure-tensor representatives on every unbounded complex.
Source: Stacks 03CY, 03CZ and 07A6; finite-coefficient transport Steps 1 and 3
(blueprint: lem-pur-constant-scalar-normalized-basis).
Proof: sheafify the basis of B over A and its dual coordinate functionals. They give
mutually inverse maps between restricted tensor extension of M and a finite power
of M. Define each inclusion as the scalar unit followed by multiplication by its
basis vector; the adjunction formula makes this precisely x maps to b_a tensor x.
The coordinate functional sends c tensor x to q_a(c)x. Tensor balancing proves
linearity, including for locally constant coefficient sections. The basis expansion
and Kronecker identities prove both finite-matrix identities before sheafification;
the universal property of sheafification preserves them. All maps are natural in M,
so they commute with differentials. Apply the exact localization to these cochain
maps and their matrix identities. The localized unit and both exact-functor
factorizations yield exactly the last equation below. Transport the matrix
identities along Q.objObjPreimageIso to arbitrary derived objects. The empty
basis gives the zero object and the same empty-sum identity. -/
theorem normalized_basis
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (A B : CommRingCat.{r}) [Algebra A B]
    [HasDerivedCategory.{w} (modules (constantRing J A))]
    [HasDerivedCategory.{w} (modules (constantRing J B))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))
    [PreservesFiniteLimits D.E] [PreservesFiniteColimits D.E]
    [PreservesFiniteLimits (restriction
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))]
    [PreservesFiniteColimits (restriction
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))]
    (a : D.E ⊣ restriction
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))
    (ha : ∀ (M : modules (constantRing J A)) (N : modules (constantRing J B))
      (f : SheafOfModules.changeOfRings.{v, u, r}
        ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))) M ⟶ N)
      (V : Cᵒᵖ) (x : M.val.obj V),
      (a.homEquiv M N (eqToHom (D.obj_eq M) ≫ f)).val.app V x =
        f.val.app V ((toSheafify J
          (SheafOfModules.changeOfRingsPresheaf.{v, u, r}
            ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B)))
              M).presheaf).app V
                ((1 : (constantRing J B).obj.obj V)
                  ⊗ₜ[(constantRing J A).obj.obj V,(((constantSheaf J CommRingCat).map
                    (CommRingCat.ofHom (algebraMap A B))).hom.app V).hom] x)))
    {I : Type i} [Fintype I] (b : Module.Basis I A B) :
    let U := (restriction ((constantSheaf J CommRingCat).map
      (CommRingCat.ofHom (algebraMap A B)))).mapDerivedCategory
    let S := D.E.mapDerivedCategory
    let ι := fun (M : DerivedCategory (modules (constantRing J A))) (c : I) ↦
      a.onDerivedCategory.unit.app M ≫ U.map ((derived J B (b c)).app (S.obj M))
    (∀ M, ∃ q : I → (U.obj (S.obj M) ⟶ M),
      (∀ c d : I, ι M c ≫ q d =
        @ite _ (c = d) (Classical.propDecidable _) (𝟙 M) 0) ∧
      ∑ c : I, q c ≫ ι M c = 𝟙 _) ∧
    ∀ (K : CochainComplex (modules (constantRing J A)) ℤ) (c : I),
      ∃ k : K ⟶ ((restriction ((constantSheaf J CommRingCat).map
        (CommRingCat.ofHom (algebraMap A B)))).mapHomologicalComplex (.up ℤ)).obj
          ((D.E.mapHomologicalComplex (.up ℤ)).obj K),
        (∀ (n : ℤ) (V : Cᵒᵖ) (x : (K.X n).val.obj V),
          (k.f n).val.app V x =
            (eqToHom (D.obj_eq (K.X n)).symm).val.app V
              ((toSheafify J (SheafOfModules.changeOfRingsPresheaf.{v, u, r}
                ((constantSheaf J CommRingCat).map
                  (CommRingCat.ofHom (algebraMap A B))) (K.X n)).presheaf).app V
                    ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V (b c)
                      ⊗ₜ[(constantRing J A).obj.obj V,
                        (((constantSheaf J CommRingCat).map
                          (CommRingCat.ofHom (algebraMap A B))).hom.app V).hom] x))) ∧
        ι (DerivedCategory.Q.obj K) c ≫
            U.map (D.E.mapDerivedCategoryFactors.hom.app K) ≫
            (restriction ((constantSheaf J CommRingCat).map
              (CommRingCat.ofHom (algebraMap A B)))).mapDerivedCategoryFactors.hom.app
                ((D.E.mapHomologicalComplex (.up ℤ)).obj K) = DerivedCategory.Q.map k := by
  intro U S ι
  have hk (c : I) (M : modules (constantRing J A)) :
      a.unit.app M ≫ (restriction (constAlgebraMap J A B)).map
        ((ordinary J B (b c)).app (D.E.obj M)) =
        incl J A B (b c) M ≫
          (restriction (constAlgebraMap J A B)).map (eqToHom (D.obj_eq M).symm) := by
    ext V x
    have hu := ha M (D.E.obj M) (eqToHom (D.obj_eq M).symm) V x
    rw [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at hu
    change ((ordinary J B (b c)).app (D.E.obj M)).val.app V ((a.unit.app M).val.app V x) =
      (eqToHom (D.obj_eq M).symm).val.app V ((incl J A B (b c) M).val.app V x)
    erw [hu]
    rw [incl_apply]
    refine (((eqToHom (D.obj_eq M).symm).val.app V).hom.map_smul _ _).symm.trans ?_
    congr 1
    refine (toSheafify_smul
      (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M) V _ _).symm.trans ?_
    congr 1
    exact congrArg (fun s ↦ s ⊗ₜ[(constantRing J A).obj.obj V,
      ((constAlgebraMap J A B).hom.app V).hom] x) (mul_one (constSection J B (b c) V))
  have hι (X Y : DerivedCategory (modules (constantRing J A))) (f : X ⟶ Y) (c : I) :
      f ≫ ι Y c = ι X c ≫ U.map (S.map f) := by
    have h1 := a.onDerivedCategory.unit_naturality f
    have h2 := (derived J B (b c)).naturality (S.map f)
    simp only [ι, Functor.id_obj, Functor.comp_obj] at h1 h2 ⊢
    rw [← reassoc_of% h1, Category.assoc, ← U.map_comp, ← U.map_comp, h2]
  refine ⟨fun M ↦ ?_, fun K c ↦ ⟨inclC (A := A) (B := B) D a (b c) K, fun n V x ↦ ?_,
    unit_center_comp (A := A) (B := B) D a (b c) K⟩⟩
  · let K := DerivedCategory.Q.objPreimage M
    let e := DerivedCategory.Q.objObjPreimageIso M
    let Φ := U.map (D.E.mapDerivedCategoryFactors.hom.app K) ≫
      (restriction (constAlgebraMap J A B)).mapDerivedCategoryFactors.hom.app
        ((D.E.mapHomologicalComplex (.up ℤ)).obj K)
    have hιK (c : I) : ι (DerivedCategory.Q.obj K) c ≫ Φ =
        DerivedCategory.Q.map (inclC (A := A) (B := B) D a (b c) K) :=
      unit_center_comp (A := A) (B := B) D a (b c) K
    refine ⟨fun d ↦ U.map (S.map e.inv) ≫ Φ ≫
      DerivedCategory.Q.map (projC (A := A) (B := B) D (b.coord d) K) ≫ e.hom,
      fun c d ↦ ?_, ?_⟩
    · rw [← Category.assoc, ← hι, Category.assoc, ← Category.assoc (ι _ c), hιK,
        ← Category.assoc (DerivedCategory.Q.map _), ← Functor.map_comp,
        inclC_projC (A := A) (B := B) D a b hk]
      by_cases h : c = d
      · rw [ite_eq_left h, ite_eq_left h, Functor.map_id, Category.id_comp, Iso.inv_hom_id]
        rfl
      · rw [ite_eq_right h, ite_eq_right h, Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
    · have hΦ : ι (DerivedCategory.Q.obj K) = fun c ↦
          DerivedCategory.Q.map (inclC (A := A) (B := B) D a (b c) K) ≫ inv Φ := by
        funext c
        rw [← hιK, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      have h (c : I) : (U.map (S.map e.inv) ≫ Φ ≫
          DerivedCategory.Q.map (projC (A := A) (B := B) D (b.coord c) K) ≫ e.hom) ≫ ι M c =
          U.map (S.map e.inv) ≫ Φ ≫
            DerivedCategory.Q.map (projC (A := A) (B := B) D (b.coord c) K ≫
              inclC (A := A) (B := B) D a (b c) K) ≫
              inv Φ ≫ U.map (S.map e.hom) := by
        simp only [Category.assoc]
        rw [hι _ _ e.hom c, hΦ, Functor.map_comp]
        simp only [Category.assoc]
      rw [Finset.sum_congr rfl (fun c _ ↦ h c)]
      rw [← Preadditive.comp_sum, ← Preadditive.comp_sum, ← Preadditive.sum_comp]
      rw [sum_Q_projC_inclC (A := A) (B := B) D a b hk K]
      erw [Category.id_comp]
      rw [IsIso.hom_inv_id_assoc, ← U.map_comp, ← S.map_comp, Iso.inv_hom_id, S.map_id, U.map_id]
  · rw [inclC_f (A := A) (B := B) D a (b c) (hk c)]
    rfl

end CategoryTheory.ConstantModuleScalar
