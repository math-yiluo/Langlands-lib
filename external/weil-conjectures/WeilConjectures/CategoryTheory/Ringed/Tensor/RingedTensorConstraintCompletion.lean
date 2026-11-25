/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorComparisonExtension
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Completion of tensor constraints specified on K-flat pairs

Source: Stacks Project, Tag 0FPT
(blueprint: lem-sfb-ringed-tensor-constraint-completion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures SheafOfModules
namespace CategoryTheory
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
private abbrev Mod := RingedTensorModules.{c, v, r} J R

noncomputable local instance ringedTensorUnitSMul
    (M : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    (U : Cᵒᵖ) :
    SMul (((ringedTensorUnitComplex.{c, v, r} J R).X 0).val.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule.toSMul

private def pure (A B : Mod.{c, v, r} J R) (U : Cᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) : (A ⊗ B).val.obj U :=
  (tensorObjIsoSheafification A B).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 _)).unit.app
      (A.val ⊗ B.val)).app U (x ⊗ₜ[R.obj.obj U] y))

private theorem pure_restrict (A B : Mod.{c, v, r} J R)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : A.val.obj U) (y : B.val.obj U) :
    (A ⊗ B).val.map f (pure.{c, v, r} J R A B U x y) =
      pure.{c, v, r} J R A B V (A.val.map f x) (B.val.map f y) := by
  let η := ((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 _)).unit.app
    (A.val ⊗ B.val)) ≫ (tensorObjIsoSheafification A B).inv.val
  exact (PresheafOfModules.naturality_apply η f (x ⊗ₜ[R.obj.obj U] y)).symm

private theorem pure_ext_private (A B N : Mod.{c, v, r} J R) {f g : A ⊗ B ⟶ N}
    (h : ∀ U x y, f.val.app U (pure.{c, v, r} J R A B U x y) =
      g.val.app U (pure.{c, v, r} J R A B U x y)) : f = g := by
  apply (cancel_epi (tensorObjIsoSheafification A B).inv).mp
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)
  apply (adj.homEquiv (A.val ⊗ B.val) N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

/-- Public export of the private `pure_ext_private`
(used by `import all` importers; linter.privateModule). -/
alias pure_ext := pure_ext_private

private theorem pure_braiding (A B : Mod.{c, v, r} J R) (U : Cᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) :
    (β_ A B).hom.val.app U (pure.{c, v, r} J R A B U x y) = pure.{c, v, r} J R B A U y x := by
  exact CochainPullback.moduleTmul_braiding A B U x y

private theorem pure_map
    {M M' N N' : Mod.{c, v, r} J R} (f : M ⟶ M') (g : N ⟶ N')
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (f ⊗ₘ g).val.app V (pure.{c, v, r} J R M N V x y) =
      pure.{c, v, r} J R M' N' V (f.val.app V x) (g.val.app V y) := by
  exact CochainPullback.moduleTmul_map f g V x y

private theorem pure_ext₃ (A B D N : Mod.{c, v, r} J R)
    {f g : (A ⊗ B) ⊗ D ⟶ N}
    (h : ∀ U x y z,
      f.val.app U (pure.{c, v, r} J R (A ⊗ B) D U (pure.{c, v, r} J R A B U x y) z) =
        g.val.app U (pure.{c, v, r} J R (A ⊗ B) D U (pure.{c, v, r} J R A B U x y) z)) : f = g := by
  apply (cancel_epi (β_ D (A ⊗ B)).hom).mp
  apply (SheafOfModules.tensorHomEquiv_kfi (R := R) D (A ⊗ B) N).injective
  change (SheafOfModules.tensorHomEquiv_kfi (R := R) D (A ⊗ B) N
      ((β_ D (A ⊗ B)).hom ≫ f)) = _
  refine pure_ext_private.{c, v, r} J R A B (SheafOfModules.homObjSmall_kfi (R := R) D N)
    (f := SheafOfModules.tensorHomEquiv_kfi (R := R) D (A ⊗ B) N ((β_ D (A ⊗ B)).hom ≫ f))
    (g := SheafOfModules.tensorHomEquiv_kfi (R := R) D (A ⊗ B) N ((β_ D (A ⊗ B)).hom ≫ g)) ?_
  intro U x y
  apply (PresheafOfModules.homEquivSmall_kfi.{max c v r, c, v} D.val N.val U).injective
  change PresheafOfModules.homEquivSmall_kfi.{max c v r, c, v} D.val N.val U
      ((PresheafOfModules.tensorHomCurry_kfi.{max c v r, c, v} _).app U
        (pure.{c, v, r} J R A B U x y)) =
    PresheafOfModules.homEquivSmall_kfi.{max c v r, c, v} D.val N.val U
      ((PresheafOfModules.tensorHomCurry_kfi.{max c v r, c, v} _).app U
        (pure.{c, v, r} J R A B U x y))
  rw [PresheafOfModules.tensorHomCurry_app_apply_kfi.{max c v r, c, v},
    PresheafOfModules.tensorHomCurry_app_apply_kfi.{max c v r, c, v}]
  apply PresheafOfModules.hom_ext
  intro W
  ext z
  change f.val.app (op W.unop.left)
      ((β_ D (A ⊗ B)).hom.val.app (op W.unop.left)
        (pure.{c, v, r} J R D (A ⊗ B) (op W.unop.left) z
          ((A ⊗ B).val.map W.unop.hom.op (pure.{c, v, r} J R A B U x y)))) =
    g.val.app (op W.unop.left)
      ((β_ D (A ⊗ B)).hom.val.app (op W.unop.left)
        (pure.{c, v, r} J R D (A ⊗ B) (op W.unop.left) z
          ((A ⊗ B).val.map W.unop.hom.op (pure.{c, v, r} J R A B U x y))))
  rw [pure_braiding, pure_restrict]
  exact h (op W.unop.left) _ _ z

private abbrev Complex := CochainComplex (Mod.{c, v, r} J R) ℤ

private theorem tensorGenerator_ext_private
    (P Q F : Complex.{c, v, r} J R)
    (φ ψ : (coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ⟶ F)
    (h : ∀ (p q k : ℤ) (hpq : p + q = k) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      (φ.f k).val.app U (coefficientTensorGenerator.{r, c, v} J R P Q p q k hpq U x y) =
        (ψ.f k).val.app U (coefficientTensorGenerator.{r, c, v} J R P Q p q k hpq U x y)) :
    φ = ψ := by
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := P) (K₂ := Q) (F := curriedTensor (Mod.{c, v, r} J R)) (c := .up ℤ)
  intro p q hpq
  apply pure_ext_private.{c, v, r} J R (P.X p) (Q.X q) (F.X k)
  intro U x y
  exact h p q k hpq U x y

/-- Public export of the private `tensorGenerator_ext_private`
(used by `import all` importers; linter.privateModule). -/
alias tensorGenerator_ext := tensorGenerator_ext_private

private theorem tensorGenerator_ext₃_private
    (P Q N F : Complex.{c, v, r} J R)
    (φ ψ : (coefficientTotalTensor.{r, c, v} J R).obj
      ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q), N) ⟶ F)
    (h : ∀ (p q t i k : ℤ) (hpq : p + q = i) (hit : i + t = k) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (N.X t).val.obj U),
      (φ.f k).val.app U (coefficientTensorGenerator.{r, c, v} J R
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) N i t k hit U
        (coefficientTensorGenerator.{r, c, v} J R P Q p q i hpq U x y) z) =
      (ψ.f k).val.app U (coefficientTensorGenerator.{r, c, v} J R
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) N i t k hit U
        (coefficientTensorGenerator.{r, c, v} J R P Q p q i hpq U x y) z)) : φ = ψ := by
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
    (K₁ := P) (K₂ := Q) (K₃ := N)
    (F₁₂ := curriedTensor (Mod.{c, v, r} J R))
    (G := curriedTensor (Mod.{c, v, r} J R)) (c₁₂ := .up ℤ) (c₄ := .up ℤ)
  intro p q t hpqt
  have hpqt' : (p + q) + t = k := hpqt
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq
    (curriedTensor (Mod.{c, v, r} J R)) (curriedTensor (Mod.{c, v, r} J R))
    P Q N (.up ℤ) (.up ℤ) p q t (p + q) k rfl hpqt']
  apply pure_ext₃.{c, v, r} J R (P.X p) (Q.X q) (N.X t) (F.X k)
  intro U x y z
  have hm := pure_map.{c, v, r} J R
    (HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q (p + q) rfl)
    (𝟙 (N.X t)) U (pure.{c, v, r} J R (P.X p) (Q.X q) U x y) z
  simp only [tensorHom_id, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] at hm
  have hh := h p q t (p + q) k rfl hpqt' U x y z
  let j := HomologicalComplex.ιMapBifunctor
    ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) N
    (curriedTensor (Mod.{c, v, r} J R)) (.up ℤ) (p + q) t k hpqt'
  exact (congrArg (fun a ↦ (φ.f k).val.app U (j.val.app U a)) hm).trans
    (hh.trans (congrArg (fun a ↦ (ψ.f k).val.app U (j.val.app U a)) hm).symm)

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]

/-- The scalar unit, reassociation and signed interchange on simultaneous K-flat models.
Source: Stacks Tag 0FPT
(blueprint: lem-sfb-ringed-tensor-constraint-completion). -/
structure RingedTensorConstraintModels
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T : CoefficientTensorModels.{r, c, v, w} J R S)
    (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
      _ S.monoidal)
    (u : S.monoidal.tensorUnit ≅ DerivedCategory.Q.obj
      (ringedTensorUnitComplex.{c, v, r} J R)) where
  /-- The ordinary coefficient complex is K-flat. -/
  unitKFlat : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R)
    (ringedTensorUnitComplex.{c, v, r} J R)
  /-- The symmetry descends the actual signed interchange of total-complex summands. -/
  symmetry_model : ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (hP :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P) (hQ :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q),
    ∃ σ : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ⟶
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, P),
      (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (σ.f k).val.app U (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q k h U x
      y) =
          (p * q).negOnePow • WeilConjectures.coefficientTensorGenerator.{r, c, v} J R Q P q p k h'
      U y x) ∧
      (T.iso J R S P Q hP hQ).hom ≫
          (s.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
        DerivedCategory.Q.map σ ≫ (T.iso J R S Q P hQ hP).hom
  /-- The right unit constraint is induced by the actual scalar multiplication map. -/
  unit_model : ∀ (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (hP :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P),
    ∃ ρ : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P,
      ringedTensorUnitComplex.{c, v, r} J R) ⟶ P,
      (∀ (p : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
        (a : ((ringedTensorUnitComplex.{c, v, r} J R).X 0).val.obj U),
        (ρ.f p).val.app U
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P
      (ringedTensorUnitComplex.{c, v, r} J R)
              p 0 p (Int.add_zero p) U x a) = (show R.obj.obj U from a) • x) ∧
      (T.iso J R S P (ringedTensorUnitComplex.{c, v, r} J R)
          hP unitKFlat).hom ≫ S.tensor.map (Prod.mkHom (𝟙 _) u.inv) ≫
          (S.monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom = DerivedCategory.Q.map ρ
  /-- The associator descends the actual reassociation of total-complex summands. -/
  associator_model : ∀ (P Q V : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q)
      (hV : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) V),
    ∃ α : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q), V) ⟶
        (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P,
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, V)),
      (∀ (p q t i j k : ℤ) (hpq : p + q = i) (hit : i + t = k)
        (hqt : q + t = j) (hpj : p + j = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (V.X t).val.obj U),
        (α.f k).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) V i t k hit U
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q i hpq U x y) z) =
          WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, V)) p j k hpj U x
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R Q V q t j hqt U y z)) ∧
      (T.iso J R S ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) V
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hV).hom ≫
        S.tensor.map (Prod.mkHom (T.iso J R S P Q hP hQ).hom (𝟙 _)) ≫
        (S.monoidal.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj V)).hom =
      DerivedCategory.Q.map α ≫
        (T.iso J R S P ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q,
      V)) hP
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R Q V hQ hV)).hom ≫
        S.tensor.map (Prod.mkHom (𝟙 _) (T.iso J R S Q V hQ hV).hom)

private theorem model_symmetry
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T : CoefficientTensorModels.{r, c, v, w} J R S)
    (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
      _ S.monoidal)
    (u : S.monoidal.tensorUnit ≅ DerivedCategory.Q.obj
      (ringedTensorUnitComplex.{c, v, r} J R))
    (M : RingedTensorConstraintModels.{c, v, r, w} J R S T s u) :
    RingedDerivedTensorSymmetryModel.{c, v, r, w} J R S T s := by
  intro P Q hP hQ
  obtain ⟨σ, hσ, he⟩ := M.symmetry_model P Q hP hQ
  have hs : σ = (β_ P Q).hom := by
    apply tensorGenerator_ext_private.{c, v, r} J R
    intro p q k hpq U x y
    have hqp : q + p = k := (add_comm q p).trans hpq
    exact (hσ p q k hpq hqp U x y).trans
      ((RingedDerivedNative.complexConstraints.{c, v, r} J R).symmetry
        P Q p q k hpq hqp U x y).symm
  exact ⟨β_ P Q, (RingedDerivedNative.complexConstraints.{c, v, r} J R).symmetry P Q,
    hs ▸ he⟩

-- The dependent nested tensor comparisons require additional elaboration steps.
private theorem model_associator
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T : CoefficientTensorModels.{r, c, v, w} J R S)
    (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
      _ S.monoidal)
    (u : S.monoidal.tensorUnit ≅ DerivedCategory.Q.obj
      (ringedTensorUnitComplex.{c, v, r} J R))
    (M : RingedTensorConstraintModels.{c, v, r, w} J R S T s u)
    (t : RingedDerivedTensorComparison.{c, v, r, w} J R S)
    (ht : RingedDerivedTensorBothModel.{c, v, r, w} J R S T t) :
    RingedDerivedTensorAssociatorModel.{c, v, r, w} J R S T t := by
  intro P Q N hP hQ hN
  obtain ⟨a, ha, he⟩ := M.associator_model P Q N hP hQ hN
  have heq : a = (α_ P Q N).hom := by
    apply tensorGenerator_ext₃_private.{c, v, r} J R
    intro p q t i k hpq hit U x y z
    have hpj : p + (q + t) = k := by omega
    exact (ha p q t i (q + t) k hpq hit rfl hpj U x y z).trans
      ((RingedDerivedNative.complexConstraints.{c, v, r} J R).associator
        P Q N p q t i (q + t) k hpq rfl hit hpj U x y z).symm
  refine ⟨α_ P Q N,
    (RingedDerivedNative.complexConstraints.{c, v, r} J R).associator P Q N, ?_⟩
  rw [ht _ N (coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hN,
    ht P _ hP (coefficientTotalTensor_isKFlat.{r, c, v} J R Q N hQ hN)]
  exact heq ▸ he

private theorem model_rightUnitor
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T : CoefficientTensorModels.{r, c, v, w} J R S)
    (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
      _ S.monoidal)
    (u : S.monoidal.tensorUnit ≅ DerivedCategory.Q.obj
      (ringedTensorUnitComplex.{c, v, r} J R))
    (M : RingedTensorConstraintModels.{c, v, r, w} J R S T s u)
    (t : RingedDerivedTensorComparison.{c, v, r, w} J R S)
    (ht : RingedDerivedTensorBothModel.{c, v, r, w} J R S T t) :
    RingedDerivedTensorRightUnitorModel.{c, v, r, w} J R S t u := by
  intro P hP
  obtain ⟨ρ, hρ, he⟩ := M.unit_model P hP
  have heq : ρ = (ρ_ P).hom := by
    apply HomologicalComplex.hom_ext
    intro k
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := P) (K₂ := ringedTensorUnitComplex.{c, v, r} J R)
      (F := curriedTensor (Mod.{c, v, r} J R)) (c := .up ℤ)
    intro p q hpq
    change p + q = k at hpq
    by_cases hq : q = 0
    · subst q
      have hk : k = p := by omega
      subst hk
      apply pure_ext_private.{c, v, r} J R (P.X k)
        ((ringedTensorUnitComplex.{c, v, r} J R).X 0) (P.X k)
      intro U x a
      exact (hρ k U x a).trans
        ((RingedDerivedNative.complexConstraints.{c, v, r} J R).rightUnitor
          P k (Int.add_zero k) U a x).symm
    · apply IsZero.eq_of_src
      exact (tensorLeft (P.X p)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ q hq)
  refine ⟨ρ_ P, (RingedDerivedNative.complexConstraints.{c, v, r} J R).rightUnitor P, ?_⟩
  rw [ht P (ringedTensorUnitComplex.{c, v, r} J R) hP M.unitKFlat]
  exact heq ▸ he

private theorem model_leftUnitor
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T : CoefficientTensorModels.{r, c, v, w} J R S)
    (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
      _ S.monoidal)
    (u : S.monoidal.tensorUnit ≅ DerivedCategory.Q.obj
      (ringedTensorUnitComplex.{c, v, r} J R))
    (M : RingedTensorConstraintModels.{c, v, r, w} J R S T s u)
    (t : RingedDerivedTensorComparison.{c, v, r, w} J R S)
    (ht : RingedDerivedTensorBothModel.{c, v, r, w} J R S T t) :
    RingedDerivedTensorLeftUnitorModel.{c, v, r, w} J R S t u := by
  intro P hP
  obtain ⟨σ, hσ, heσ⟩ := model_symmetry.{c, v, r, w} J R S T s u M
    (ringedTensorUnitComplex.{c, v, r} J R) P M.unitKFlat hP
  obtain ⟨ρ, hρ, heρ⟩ := model_rightUnitor.{c, v, r, w} J R S T s u M t ht P hP
  refine ⟨σ ≪≫ ρ, ?_, ?_⟩
  · intro n hn U a x
    change (ρ.hom.f n).val.app U ((σ.hom.f n).val.app U
      (coefficientTensorGenerator.{r, c, v} J R
        (ringedTensorUnitComplex.{c, v, r} J R) P 0 n n hn U
        (ringedTensorUnitSection.{c, v, r} J R U a) x)) = _
    rw [hσ 0 n n hn (Int.add_zero n) U _ x]
    simpa only [zero_mul, Int.negOnePow_zero, one_smul] using hρ n (Int.add_zero n) U a x
  · let := S.monoidal
    let := s
    rw [ht (ringedTensorUnitComplex.{c, v, r} J R) P M.unitKFlat hP]
    have hu : S.tensor.map
        (X := (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, r} J R),
          DerivedCategory.Q.obj P))
        (Y := (S.monoidal.tensorUnit, DerivedCategory.Q.obj P))
        (u.inv, 𝟙 (DerivedCategory.Q.obj P)) ≫
        (λ_ (DerivedCategory.Q.obj P)).hom =
      (s.braiding (DerivedCategory.Q.obj
        (ringedTensorUnitComplex.{c, v, r} J R)) (DerivedCategory.Q.obj P)).hom ≫
        S.tensor.map
          (X := (DerivedCategory.Q.obj P,
            DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, r} J R)))
          (Y := (DerivedCategory.Q.obj P, S.monoidal.tensorUnit))
          (𝟙 (DerivedCategory.Q.obj P), u.inv) ≫
          (ρ_ (DerivedCategory.Q.obj P)).hom := by
      change (u.inv ⊗ₘ 𝟙 _) ≫ (λ_ _).hom =
        (β_ _ _).hom ≫ (𝟙 _ ⊗ₘ u.inv) ≫ (ρ_ _).hom
      rw [← braiding_rightUnitor,
        BraidedCategory.braiding_naturality_assoc]
    rw [hu, ← Category.assoc, heσ]
    simp only [Category.assoc]
    rw [← ht P _ hP M.unitKFlat, heρ, ← Functor.map_comp]
    rfl

/-- The constraints on simultaneous K-flat representatives determine full representative
coherence, with the same prescribed coefficient-unit identification.
Source: Stacks Tags 06YT and 0FPT
(blueprint: lem-sfb-ringed-tensor-constraint-completion).

Proof: extend the tensor comparison by functorial flat resolution. The actual braiding,
associator and right unit maps of complexes have precisely the stipulated formulas.
Two maps with these formulas agree: use sheafification, total-coproduct inclusions,
and tensor-Hom currying to detect nested tensors. Consequently the stipulated maps
are those actual isomorphisms. Agreement of the extended comparison on K-flat pairs
transports their three constraint equations. The left unitor follows from symmetry
and the right unitor; its interchange sign is trivial in degree zero. -/
theorem ringedTensorConstraint_completion
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T : CoefficientTensorModels.{r, c, v, w} J R S)
    (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
      _ S.monoidal)
    (u : S.monoidal.tensorUnit ≅ DerivedCategory.Q.obj
      (ringedTensorUnitComplex.{c, v, r} J R))
    (M : RingedTensorConstraintModels.{c, v, r, w} J R S T s u) :
    ∃ K : RingedDerivedTensorCoherence.{c, v, r, w} J R S T s, K.unitIso = u := by
  obtain ⟨t, ht, hn⟩ := ringedTensorComparison_extension.{c, v, r, w} J R S T
  exact ⟨⟨t, ht, hn, u, model_symmetry J R S T s u M,
    model_associator J R S T s u M t ht, model_leftUnitor J R S T s u M t ht,
    model_rightUnitor J R S T s u M t ht⟩, rfl⟩

end CategoryTheory

namespace CategoryTheory
/-- Public export of the private `tensorGenerator_ext₃_private` (used by `import all` importers;
linter.privateModule). -/
alias tensorGenerator_ext₃ := tensorGenerator_ext₃_private

end CategoryTheory
