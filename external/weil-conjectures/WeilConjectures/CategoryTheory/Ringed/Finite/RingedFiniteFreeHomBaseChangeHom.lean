/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeCoordinates
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
/-! # The internal-Hom transpose component of finite-free base change.

The finite-free hypothesis and the normalized strong tensor comparison determine the
transpose uniquely; the proof is the restriction-of-scalars finite-biproduct argument
from Stacks Tags 08J9 and 08JA.
(blueprint: lem-sf-ringed-finite-free-hom-base-change)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace CategoryTheory

section Matrices
variable {A : Type*} [Category A] [HasZeroMorphisms A]
private theorem matrix_identity {I : Type*} [DecidableEq I]
    (F : I → A) [HasBiproduct F] (m : (⨁ F) ⟶ ⨁ F)
    (hm : ∀ i j, biproduct.ι F i ≫ m ≫ biproduct.π F j =
      if h : i = j then eqToHom (congrArg F h) else 0) : m = 𝟙 _ := by
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simpa [Category.assoc, biproduct.ι_π] using hm i j
private theorem matrix_isIso {I : Type*} [DecidableEq I]
    (F : I → A) [HasBiproduct F] {X Y : A}
    (a : (⨁ F) ≅ X) (b : Y ≅ ⨁ F) (f : X ⟶ Y)
    (hm : ∀ i j, biproduct.ι F i ≫ a.hom ≫ f ≫ b.hom ≫ biproduct.π F j =
      if h : i = j then eqToHom (congrArg F h) else 0) : IsIso f := by
  have heq : a.hom ≫ f ≫ b.hom = 𝟙 _ := by
    apply matrix_identity
    simpa only [Category.assoc] using hm
  have : IsIso (a.hom ≫ f ≫ b.hom) := by rw [heq]; infer_instance
  have : IsIso (f ≫ b.hom) := IsIso.of_isIso_comp_left a.hom _
  exact IsIso.of_isIso_comp_right f b.hom

end Matrices

section Products
universe u
variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
  {H : Aᵒᵖ × A ⥤ A} (AR : WeilConjectures.CoefficientClosedStructure H)
private def hom_biproduct (P : A) {I : Type} (F : I → A)
    [HasBiproduct F] [HasBiproduct (fun i ↦ H.obj (op P, F i))] :
    H.obj (op P, ⨁ F) ≅ ⨁ fun i ↦ H.obj (op P, F i) := by
  let G := Prod.sectR (op P) A ⋙ H
  let : G.IsRightAdjoint := (AR.adjunction P).isRightAdjoint
  let : HasProduct (fun i ↦ G.obj (F i)) :=
    inferInstanceAs (HasProduct (fun i ↦ H.obj (op P, F i)))
  exact G.mapIso (biproduct.isoProduct F) ≪≫ PreservesProduct.iso G F ≪≫
    (biproduct.isoProduct (fun i ↦ H.obj (op P, F i))).symm
private theorem hom_biproduct_π (P : A) {I : Type} (F : I → A)
    [HasBiproduct F] [HasBiproduct (fun i ↦ H.obj (op P, F i))] (j : I) :
    (hom_biproduct AR P F).hom ≫ biproduct.π _ j =
      H.map (Prod.mkHom (𝟙 (op P)) (biproduct.π F j)) := by
  let G := Prod.sectR (op P) A ⋙ H
  let : G.IsRightAdjoint := (AR.adjunction P).isRightAdjoint
  let : HasProduct (fun i ↦ G.obj (F i)) :=
    inferInstanceAs (HasProduct (fun i ↦ H.obj (op P, F i)))
  let : HasBiproduct (fun i ↦ G.obj (F i)) :=
    inferInstanceAs (HasBiproduct (fun i ↦ H.obj (op P, F i)))
  dsimp [hom_biproduct]
  simp only [Category.assoc, biproduct.isoProduct_inv, biproduct.lift_π,
    biproduct.isoProduct_hom]
  change H.map ((Prod.sectR (op P) A).map (Pi.lift (biproduct.π F))) ≫
      piComparison G F ≫ Pi.π _ j = _
  rw [piComparison_comp_π]
  change G.map (Pi.lift (biproduct.π F)) ≫ G.map (Pi.π F j) =
    G.map (biproduct.π F j)
  rw [← G.map_comp]
  simp

end Products

section Naturality
universe u₁ v₁ u₂ v₂
variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {H : Aᵒᵖ × A ⥤ A} {K : Bᵒᵖ × B ⥤ B}
  (AR : WeilConjectures.CoefficientClosedStructure H)
  (AS : WeilConjectures.CoefficientClosedStructure K)
  (T : A ⥤ B) (μ : AR.tensor ⋙ T ≅ T.prod T ⋙ AS.tensor)

private theorem evaluation_target (P Q Q' : A) (g : Q ⟶ Q') :
    AR.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P)) g)) (𝟙 P)) ≫
      AR.evaluation P Q' = AR.evaluation P Q ≫ g := by
  simpa [WeilConjectures.CoefficientClosedStructure.evaluation,
    WeilConjectures.CoefficientClosedStructure.tensor] using
    (AR.adjunction P).counit.naturality g

private theorem evaluation_source (P P' Q : A) (f : P' ⟶ P) :
    AR.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
      AR.evaluation P' Q =
    AR.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) f) ≫ AR.evaluation P Q := by
  simpa [WeilConjectures.CoefficientClosedStructure.evaluation,
    WeilConjectures.CoefficientClosedStructure.tensor] using
    AR.evaluation_naturality P P' Q f

private theorem transpose_uncurry (X P Q : B) (f : AS.tensor.obj (X, P) ⟶ Q) :
    AS.tensor.map (Prod.mkHom (AS.transpose X P Q f) (𝟙 P)) ≫
      AS.evaluation P Q = f := by
  have hh : (@MonoidalCategory.tensorRight B _ AS.monoidal P).map
      (AS.transpose X P Q f) ≫ AS.evaluation P Q = f :=
    (AS.transpose X P Q).symm_apply_apply f
  simpa [WeilConjectures.CoefficientClosedStructure.tensor] using hh

private theorem uncurry_formula (X P Q : B) (b : X ⟶ K.obj (op P, Q)) :
    (AS.transpose X P Q).symm b =
      AS.tensor.map (Prod.mkHom b (𝟙 P)) ≫ AS.evaluation P Q := by
  change (@MonoidalCategory.tensorRight B _ AS.monoidal P).map b ≫
    AS.evaluation P Q = _
  simp [WeilConjectures.CoefficientClosedStructure.tensor]

private theorem evaluation_both (P P' Q Q' : A) (f : P' ⟶ P) (g : Q ⟶ Q') :
    AR.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
      AR.evaluation P' Q' =
    AR.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) f) ≫ AR.evaluation P Q ≫ g := by
  have hf : Prod.mkHom f.op g =
      Prod.mkHom f.op (𝟙 Q) ≫ Prod.mkHom (𝟙 (op P')) g := by simp
  rw [hf, H.map_comp]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') := by simp
  rw [ht, AR.tensor.map_comp, Category.assoc, evaluation_target,
    ← Category.assoc, evaluation_source, Category.assoc]

private theorem uncurry_both (X P P' Q Q' : B)
    (b : X ⟶ K.obj (op P, Q)) (f : P' ⟶ P) (g : Q ⟶ Q') :
    AS.tensor.map (Prod.mkHom (b ≫ K.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
      AS.evaluation P' Q' =
    AS.tensor.map (Prod.mkHom (𝟙 X) f) ≫
      AS.tensor.map (Prod.mkHom b (𝟙 P)) ≫ AS.evaluation P Q ≫ g := by
  have ht : Prod.mkHom (b ≫ K.map (Prod.mkHom f.op g)) (𝟙 P') =
      Prod.mkHom b (𝟙 P') ≫
        Prod.mkHom (K.map (Prod.mkHom f.op g)) (𝟙 P') := by simp
  rw [ht, AS.tensor.map_comp, Category.assoc, evaluation_both]
  have ht' : Prod.mkHom b (𝟙 P') ≫
      Prod.mkHom (𝟙 (K.obj (op P, Q))) f =
      Prod.mkHom (𝟙 X) f ≫ Prod.mkHom b (𝟙 P) := by simp
  rw [← Category.assoc, ← Category.assoc, ← AS.tensor.map_comp, ht', AS.tensor.map_comp]
  simp only [Category.assoc]

private theorem comparison_natural (P P' Q Q' : A) (f : P' ⟶ P) (g : Q ⟶ Q') :
    T.map (H.map (Prod.mkHom f.op g)) ≫
      AS.transpose _ (T.obj P') (T.obj Q')
        (μ.inv.app (H.obj (op P', Q'), P') ≫ T.map (AR.evaluation P' Q')) =
    AS.transpose _ (T.obj P) (T.obj Q)
        (μ.inv.app (H.obj (op P, Q), P) ≫ T.map (AR.evaluation P Q)) ≫
      K.map (Prod.mkHom (T.map f).op (T.map g)) := by
  apply (AS.transpose _ (T.obj P') (T.obj Q')).symm.injective
  change (@MonoidalCategory.tensorRight B _ AS.monoidal (T.obj P')).map
      (T.map (H.map (Prod.mkHom f.op g)) ≫ _) ≫ AS.evaluation _ _ = _
  rw [Functor.map_comp, Category.assoc]
  rw [show (@MonoidalCategory.tensorRight B _ AS.monoidal (T.obj P')).map
      (AS.transpose _ (T.obj P') (T.obj Q')
        (μ.inv.app (H.obj (op P', Q'), P') ≫ T.map (AR.evaluation P' Q'))) ≫
      AS.evaluation _ _ = _ from
    (AS.transpose _ (T.obj P') (T.obj Q')).symm_apply_apply _]
  rw [uncurry_formula]
  have ht : (@MonoidalCategory.tensorRight B _ AS.monoidal (T.obj P')).map
      (T.map (H.map (Prod.mkHom f.op g))) =
      AS.tensor.map (Prod.mkHom (T.map (H.map (Prod.mkHom f.op g))) (𝟙 (T.obj P'))) := by
    let _ := AS.monoidal
    simp [WeilConjectures.CoefficientClosedStructure.tensor,
      MonoidalCategory.tensorHom_id]
  rw [ht]
  change AS.tensor.map (Prod.mkHom (T.map (H.map (Prod.mkHom f.op g))) (𝟙 (T.obj P'))) ≫
      (μ.inv.app (H.obj (op P', Q'), P') ≫ T.map (AR.evaluation P' Q')) =
    AS.tensor.map (Prod.mkHom (_ ≫ K.map (Prod.mkHom (T.map f).op (T.map g))) (𝟙 _)) ≫
      AS.evaluation _ _
  rw [uncurry_both]
  rw [← Category.assoc
    (AS.tensor.map (Prod.mkHom
      (AS.transpose _ (T.obj P) (T.obj Q)
        (μ.inv.app (H.obj (op P, Q), P) ≫ T.map (AR.evaluation P Q))) (𝟙 (T.obj P))))
    (AS.evaluation (T.obj P) (T.obj Q)) (T.map g), transpose_uncurry]
  have hn := μ.inv.naturality
    (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P'))
  have hf := μ.inv.naturality (Prod.mkHom (𝟙 (H.obj (op P, Q))) f)
  dsimp at hn hf
  rw [T.map_id] at hn hf
  rw [← Category.assoc, hn, Category.assoc, ← T.map_comp,
    evaluation_both, T.map_comp, T.map_comp, ← Category.assoc, ← Category.assoc,
    ← hf]
  simp only [Category.assoc]

private theorem comparison_iso
    (hiso : ∀ P Q : A, IsIso
      (AS.transpose _ (T.obj P) (T.obj Q)
        (μ.inv.app (H.obj (op P, Q), P) ≫ T.map (AR.evaluation P Q)))) :
    ∃ α : H ⋙ T ≅ T.op.prod T ⋙ K,
      ∀ P Q : A, α.hom.app (op P, Q) =
        AS.transpose _ (T.obj P) (T.obj Q)
          (μ.inv.app (H.obj (op P, Q), P) ≫ T.map (AR.evaluation P Q)) := by
  let τ : H ⋙ T ⟶ T.op.prod T ⋙ K :=
    { app := fun X ↦ AS.transpose _ (T.obj X.1.unop) (T.obj X.2)
        (μ.inv.app (H.obj X, X.1.unop) ≫ T.map (AR.evaluation X.1.unop X.2))
      naturality := fun X Y f ↦ by
        exact comparison_natural AR AS T μ X.1.unop Y.1.unop X.2 Y.2 f.1.unop f.2 }
  have : ∀ X, IsIso (τ.app X) := fun X ↦ hiso X.1.unop X.2
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact ⟨asIso τ, fun _ _ ↦ rfl⟩

end Naturality

section Site
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

private theorem conservative
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J R)]
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J S)]
    {X Y : DerivedCategory (SheafOfModules.scalarModules J S)} (f : X ⟶ Y)
    (hf : IsIso ((SheafOfModules.scalarDerivedRestriction φ).map f)) : IsIso f := by
  let U := SheafOfModules.scalarRestriction φ
  have : U.Faithful := by
    constructor
    intro X Y f g h
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictScalars _).map_injective
      (congrArg SheafOfModules.Hom.val h)
  have : U.ReflectsIsomorphisms := inferInstance
  rw [DerivedCategory.isIso_iff]
  intro n
  have h : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((SheafOfModules.scalarDerivedRestriction φ).map f)) := inferInstance
  have h' : IsIso ((DerivedCategory.homologyFunctor _ n ⋙ U).map f) :=
    (NatIso.isIso_map_iff (U.mapDerivedCategoryHomologyFunctorIso n) f).2 h
  have : IsIso (U.map ((DerivedCategory.homologyFunctor _ n).map f)) := h'
  exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor _ n).map f) U

/-- The evaluation transpose for normalized finite-free scalar extension is invertible.
The ordinary functor, its universal derived pair and both representative tensor
normalizations are hypotheses; an arbitrary tensor-preserving functor is insufficient.
Source: Stacks Project, sites-cohomology.tex, Tags 08J9 and 08JA,
labels lemma-internal-hom and lemma-section-RHom-over-U; finite-free specialization.
(blueprint: lem-sf-ringed-finite-free-hom-transpose).

Proof: let U be exact restriction of scalars. A basis S = R^d gives natural
isomorphisms X^d ≅ U(T X), computed on K-flat representatives by the maps
(x_j) mapped to sum e_j tensor x_j and the inverse basis coefficient maps.
The normalized scalar-Hom adjunction identifies U H_S(TP,TQ) with H_R(P,UTQ).
Its transpose is restricted S-evaluation after the scalar unit on P.
The right adjoint H_R(P,-) preserves finite products. Finite products are finite
biproducts, so the target identifies with H_R(P,Q)^d, as does U T H_R(P,Q).
Under these identifications the proposed evaluation transpose has matrix entry
(i,j) equal to delta_ij times identity: on K-flat tensors the scalar unit inserts
1, and κ and μ multiply it by e_j. The two normalization assumptions identify
this calculation with the actual derived morphism. Uniqueness of transpose
therefore identifies every matrix entry. The matrix is the identity, so U sends
the comparison to an isomorphism. Restriction reflects isomorphisms because it
is exact and reflects isomorphisms of cohomology sheaves. Thus each comparison
is invertible. Naturality of evaluation and μ, together with uniqueness of
transpose, makes these components a natural transformation; their inverses
assemble to a natural inverse. Rank zero is the empty biproduct and obeys the
same argument. The defining transpose is basis independent. -/
theorem ringedFiniteFreeHomBaseChange_hom
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (hfree : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map φ)).obj
          (SheafOfModules.unit
            (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        SheafOfModules.free (R :=
          SheafOfModules.derivedChangeRingIndependentCoefficients J R)
            (ULift.{max c v r} (Fin d))))
    (E : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤ SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
      (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
      (_hm : ∀ {M N : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)} (f : M ⟶ N),
        E.map f = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
          eqToHom (h N).symm)
      (_hE : E.Additive)
      (T : DerivedCategory (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ⥤
        DerivedCategory (SheafOfModules.{max c v r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J S)))
      (ε : DerivedCategory.Q ⋙ T ⟶
        E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (_hT : T.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) (ComplexShape.up ℤ)))
      (AR : WeilConjectures.CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, w} J R))
      (AS : WeilConjectures.CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, w} J S))
      (MR : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R AR)
      (MS : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J S AS)
      (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S)
      (μ : AR.tensor ⋙ T ≅ T.prod T ⋙ AS.tensor)
    (hκ : (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h (Q.X q) U 1 y)))
    (hcomp : (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
        ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          IsIso (ε.app P) ∧ IsIso (ε.app Q) ∧
          T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              AS.tensor.map (Prod.mkHom (ε.app P) (ε.app Q)) =
            ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
              DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
              (MS.iso J S AS _ _ hEP hEQ).hom)) :
    ∃ α : derivedInternalHomOfUniverses.{c, v, r, w} J R ⋙ T ≅
        T.op.prod T ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J S,
      ∀ P Q : DerivedCategory (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)),
        α.hom.app (op P, Q) = AS.transpose _ (T.obj P) (T.obj Q)
          (μ.inv.app ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q), P) ≫
            T.map (AR.evaluation P Q)) := by
  obtain ⟨d, ⟨e⟩⟩ := hfree
  apply comparison_iso AR AS T μ
  intro P Q
  obtain ⟨adj, δ, hunit, hδ, hcoords⟩ :=
    ringedFiniteFreeHomBaseChange_coordinates.{c, v, r, w}
      J φ d e E h _hm T ε _hT AR AS MR MS κ μ hκ hcomp
  obtain ⟨a, aQ, β, ha, haQ, hβ, hcoord⟩ := hcoords P Q
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
  let G := Prod.sectR (op P) _ ⋙ H
  have : G.IsRightAdjoint := (AR.adjunction P).isRightAdjoint
  let γ := hom_biproduct AR P (fun _ : Fin d ↦ Q)
  let b := β ≪≫ G.mapIso aQ.symm ≪≫ γ
  let f := AS.transpose _ (T.obj P) (T.obj Q)
    (μ.inv.app (H.obj (op P, Q), P) ≫ T.map (AR.evaluation P Q))
  have hrow (i : Fin d) :
      biproduct.ι _ i ≫ a.hom ≫
        (SheafOfModules.scalarDerivedRestriction φ).map f ≫ b.hom =
      G.map (biproduct.ι (fun _ : Fin d ↦ Q) i) ≫ γ.hom := by
    calc
      _ = (biproduct.ι _ i ≫ a.hom ≫
          (SheafOfModules.scalarDerivedRestriction φ).map f ≫ β.hom) ≫
          G.map aQ.inv ≫ γ.hom := by simp [b, Category.assoc]
      _ = G.map (biproduct.ι (fun _ : Fin d ↦ Q) i ≫ aQ.hom) ≫
          G.map aQ.inv ≫ γ.hom := by rw [hcoord i]; rfl
      _ = G.map (biproduct.ι (fun _ : Fin d ↦ Q) i) ≫ γ.hom := by
        rw [← Category.assoc, ← G.map_comp]
        simp
  apply conservative.{c, v, r, w} J φ
  apply matrix_isIso (fun _ : Fin d ↦ H.obj (op P, Q)) a b
  intro i j
  have hrowπ := congrArg
    (fun k ↦ k ≫ biproduct.π (fun _ : Fin d ↦ H.obj (op P, Q)) j) (hrow i)
  simp only [Category.assoc] at hrowπ
  rw [hrowπ, hom_biproduct_π]
  change G.map (biproduct.ι (fun _ : Fin d ↦ Q) i) ≫
    G.map (biproduct.π (fun _ : Fin d ↦ Q) j) = _
  rw [← G.map_comp]
  split_ifs with hij
  · simp [hij, G, H]
  · rw [biproduct.ι_π_ne _ hij]
    simpa [G, H] using G.map_zero Q Q

end Site
end CategoryTheory
