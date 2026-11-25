/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Unbounded derived tensor with a locally free line

Source: Stacks Project, Tags 0B8N, 0B8Q, 06YN, 06YT, 06YU and 015F;
blueprint main-20261015, Tate-twist local freeness, proof (3).
(blueprint: lem-pur-line-unbounded-derived-tensor)

The tensor bifunctor is the published K-flat derived tensor. The representative
normalizations below specify the actual evaluation transformations, including their
triangle identities. The ring of global sections acts canonically; restriction along
any B-algebra structure B → Γ(R) gives every asserted B-linearity statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t a w u v b

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry

namespace SheafOfModules.LineUnbounded

/-- The comparison, evaluation, shift, triangle, cohomology and linearity clauses
of the line-tensor assertion, written over an abstract abelian category to avoid
repeated expansion of the concrete sheaf category. `nP` and `nD` specify the
representative normalization, and `evP`, `evD` are the specified ordinary evaluations.
This is a transparent proposition, with no chosen functor, map or proof.
Source: Stacks, 0B8N, 06YU, 015F and 010N
(blueprint: lem-pur-line-unbounded-derived-tensor). -/
def comparisonData {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (B : Type b) [CommRing B] [Linear B A]
    (T S : A ⥤ A) [T.Additive] [S.Additive]
    (evP : T ⋙ S ≅ 𝟭 A) (evD : S ⋙ T ≅ 𝟭 A)
    (F G : DerivedCategory A ⥤ DerivedCategory A)
    (nP : ∀ K : CochainComplex A ℤ,
      (F.obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj K)) → Prop)
    (nD : ∀ K : CochainComplex A ℤ,
      (G.obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj ((S.mapHomologicalComplex (.up ℤ)).obj K)) → Prop) : Prop :=
  ∃ sP : F.CommShift ℤ,
  ∃ sD : G.CommShift ℤ,
  (fun [_instP : F.CommShift ℤ]
    [_instD : G.CommShift ℤ] ↦
    F.IsTriangulated ∧ G.IsTriangulated ∧
    ∃ cP : DerivedCategory.Q ⋙ F ≅
      T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
    ∃ cD : DerivedCategory.Q ⋙ G ≅
      S.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      NatTrans.CommShift cP.hom ℤ ∧ NatTrans.CommShift cD.hom ℤ ∧
      (∀ K, nP K (cP.app K)) ∧ (∀ K, nD K (cD.app K)) ∧
      ∃ α : F ⋙ G ≅ 𝟭 _,
      ∃ β : G ⋙ F ≅ 𝟭 _,
        NatTrans.CommShift α.hom ℤ ∧ NatTrans.CommShift β.hom ℤ ∧
        (∀ K : CochainComplex A ℤ,
          α.hom.app (DerivedCategory.Q.obj K) =
            G.map (cP.hom.app K) ≫
              cD.hom.app ((T.mapHomologicalComplex (.up ℤ)).obj K) ≫
              DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso evP (.up ℤ) ≪≫
                Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app K)) ∧
        (∀ K : CochainComplex A ℤ,
          β.hom.app (DerivedCategory.Q.obj K) =
            F.map (cD.hom.app K) ≫
              cP.hom.app
                ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
              DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso evD (.up ℤ) ≪≫
                Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app K)) ∧
        (∀ K : DerivedCategory A,
          F.map (α.inv.app K) ≫
            β.hom.app (F.obj K) = 𝟙 _) ∧
        (∀ K : DerivedCategory A,
          α.inv.app (G.obj K) ≫
            G.map (β.hom.app K) = 𝟙 _) ∧
        (∀ i : ℤ, Nonempty (F ⋙ DerivedCategory.homologyFunctor A i ≅
          DerivedCategory.homologyFunctor A i ⋙ T)) ∧
        T.Linear B ∧ S.Linear B ∧ F.Linear B ∧ G.Linear B) (_instP := sP) (_instD := sD)

section Localization

variable {C D : Type*} [Category C] [Category D]
  (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
  (T S : C ⥤ C) (F G : D ⥤ D)
  (cF : Q ⋙ F ≅ T ⋙ Q) (cG : Q ⋙ G ≅ S ⋙ Q)

private def cancellationComparison (e : T ⋙ S ≅ 𝟭 C) : Q ⋙ (F ⋙ G) ≅ Q :=
  (Functor.associator Q F G).symm ≪≫ Functor.isoWhiskerRight cF G ≪≫
    Functor.associator T Q G ≪≫ Functor.isoWhiskerLeft T cG ≪≫
    (Functor.associator T S Q).symm ≪≫ Functor.isoWhiskerRight e Q ≪≫
    Functor.leftUnitor Q

private def localizedCancellation (e : T ⋙ S ≅ 𝟭 C) : F ⋙ G ≅ 𝟭 D :=
  Localization.liftNatIso Q W _ _ _ _
    (cancellationComparison Q T S F G cF cG e ≪≫ (Functor.rightUnitor Q).symm)

private theorem localizedCancellation_app (e : T ⋙ S ≅ 𝟭 C) (K : C) :
    (localizedCancellation Q W T S F G cF cG e).hom.app (Q.obj K) =
      G.map (cF.hom.app K) ≫ cG.hom.app (T.obj K) ≫ Q.map (e.hom.app K) := by
  simp [localizedCancellation, cancellationComparison, Localization.liftNatTrans_app,
    Localization.Lifting.iso]

private theorem localizedCancellation_inv_app (e : T ⋙ S ≅ 𝟭 C) (K : C) :
    (localizedCancellation Q W T S F G cF cG e).inv.app (Q.obj K) =
      Q.map (e.inv.app K) ≫ cG.inv.app (T.obj K) ≫ G.map (cF.inv.app K) := by
  simp [localizedCancellation, cancellationComparison, Localization.liftNatTrans_app,
    Localization.Lifting.iso]

private theorem localizedCancellation_triangles
    (a : T ⋙ S ≅ 𝟭 C) (b : S ⋙ T ≅ 𝟭 C)
    (ht : ∀ K : C, T.map (a.inv.app K) ≫ b.hom.app (T.obj K) = 𝟙 _) :
    (∀ K : D,
      F.map ((localizedCancellation Q W T S F G cF cG a).inv.app K) ≫
        (localizedCancellation Q W S T G F cG cF b).hom.app (F.obj K) = 𝟙 _) ∧
    (∀ K : D,
      (localizedCancellation Q W T S F G cF cG a).inv.app (G.obj K) ≫
        G.map ((localizedCancellation Q W S T G F cG cF b).hom.app K) = 𝟙 _) := by
  let alpha := localizedCancellation Q W T S F G cF cG a
  let beta := localizedCancellation Q W S T G F cG cF b
  have htri : Functor.whiskerRight alpha.inv F ≫ Functor.whiskerLeft F beta.hom =
      𝟙 F := by
    apply Localization.natTrans_ext Q W
    intro K
    change F.map (alpha.inv.app (Q.obj K)) ≫ beta.hom.app (F.obj (Q.obj K)) = 𝟙 _
    apply (cancel_mono (cF.hom.app K)).mp
    simp only [Category.assoc, Category.id_comp]
    have hn := beta.hom.naturality (cF.hom.app K)
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hn
    rw [← hn]
    rw [← F.map_comp_assoc]
    dsimp only [alpha]
    rw [localizedCancellation_inv_app]
    simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id_app]
    erw [G.map_id, Category.comp_id]
    dsimp only [beta]
    rw [localizedCancellation_app]
    rw [F.map_comp (Q.map (a.inv.app K)) (cG.inv.app (T.obj K))]
    simp only [Category.assoc]
    erw [← F.map_comp_assoc (cG.inv.app (T.obj K)) (cG.hom.app (T.obj K)),
      Iso.inv_hom_id_app, F.map_id, Category.id_comp]
    have hnF := cF.hom.naturality (a.inv.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hnF
    rw [← Category.assoc, hnF]
    rw [Category.assoc, ← Q.map_comp, ht]
    erw [Q.map_id, Category.comp_id]
  have htF (K : D) : F.map (alpha.inv.app K) ≫ beta.hom.app (F.obj K) = 𝟙 _ :=
    congrArg (fun n : F ⟶ F ↦ n.app K) htri
  let E : D ≌ D := ⟨F, G, alpha.symm, beta, htF⟩
  exact ⟨htF, E.unit_inverse_comp⟩

private theorem localizedCancellation_commShift [HasShift C ℤ] [HasShift D ℤ]
    [Q.CommShift ℤ] [T.CommShift ℤ] [S.CommShift ℤ]
    [F.CommShift ℤ] [G.CommShift ℤ]
    [NatTrans.CommShift cF.hom ℤ] [NatTrans.CommShift cG.hom ℤ]
    (e : T ⋙ S ≅ 𝟭 C) [NatTrans.CommShift e.hom ℤ] :
    NatTrans.CommShift (localizedCancellation Q W T S F G cF cG e).hom ℤ := by
  let a := localizedCancellation Q W T S F G cF cG e
  have he : Functor.whiskerLeft Q a.hom =
      (cancellationComparison Q T S F G cF cG e ≪≫ (Functor.rightUnitor Q).symm).hom := by
    ext K
    simp [a, localizedCancellation, Localization.liftNatTrans_app, Localization.Lifting.iso]
  have : NatTrans.CommShift (Functor.whiskerLeft Q a.hom) ℤ := by
    rw [he]
    dsimp [cancellationComparison]
    infer_instance
  have : Q.EssSurj := Localization.essSurj Q W
  exact NatTrans.CommShift.of_whiskerLeft a.hom Q (fun X ↦
    ⟨Q.objPreimage X, (Q.objObjPreimageIso X).inv, inferInstance⟩)

end Localization

private theorem whiskered_normalization
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (Q : D ⥤ E) (H : C ⥤ E)
    (chi : H ≅ F ⋙ Q) (e : F ≅ G) (K : C)
    {r : H.obj K ≅ Q.obj (F.obj K)} (hr : chi.app K = r) :
    (chi ≪≫ Functor.isoWhiskerRight e Q).app K = r ≪≫ Q.mapIso (e.app K) := by
  rw [NatIso.trans_app, hr]
  apply Iso.ext
  rfl

private theorem comparison_of_localized_pair
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (B : Type b) [CommRing B] [Linear B A]
    (T S : A ⥤ A) [T.Additive] [S.Additive]
    (evP : T ⋙ S ≅ 𝟭 A) (evD : S ⋙ T ≅ 𝟭 A)
    (F G : DerivedCategory A ⥤ DerivedCategory A)
    (nP : ∀ K : CochainComplex A ℤ,
      (F.obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj K)) → Prop)
    (nD : ∀ K : CochainComplex A ℤ,
      (G.obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj ((S.mapHomologicalComplex (.up ℤ)).obj K)) → Prop)
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (cP : DerivedCategory.Q ⋙ F ≅ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (cD : DerivedCategory.Q ⋙ G ≅ S.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [NatTrans.CommShift cP.hom ℤ] [NatTrans.CommShift cD.hom ℤ]
    (hnP : ∀ K, nP K (cP.app K)) (hnD : ∀ K, nD K (cD.app K))
    (aP : T ⋙ S ≅ 𝟭 A) (aD : S ⋙ T ≅ 𝟭 A)
    (haP : aP = evP) (haD : aD = evD)
    (ht : ∀ M, T.map (aP.inv.app M) ≫ aD.hom.app (T.obj M) = 𝟙 _)
    (hcoh : ∀ i : ℤ, Nonempty (F ⋙ DerivedCategory.homologyFunctor A i ≅
      DerivedCategory.homologyFunctor A i ⋙ T))
    [T.Linear B] [S.Linear B] [F.Linear B] [G.Linear B] :
    comparisonData B T S evP evD F G nP nD := by
  subst aP
  subst aD
  let a := Functor.mapHomologicalComplexCompIso evP (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso A (.up ℤ)
  let b := Functor.mapHomologicalComplexCompIso evD (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso A (.up ℤ)
  have hId : NatTrans.CommShift (Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom ℤ := by
    constructor
    intro n
    ext K i
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
      Functor.mapHomologicalComplexIdIso_hom_app_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Functor.commShiftIso_id_hom_app]
    erw [Category.id_comp]
  have haS : NatTrans.CommShift a.hom ℤ := by
    dsimp only [a, Iso.trans_hom]
    infer_instance
  have hbS : NatTrans.CommShift b.hom ℤ := by
    dsimp only [b, Iso.trans_hom]
    infer_instance
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let alpha := localizedCancellation DerivedCategory.Q W _ _ _ _ cP cD a
  let beta := localizedCancellation DerivedCategory.Q W _ _ _ _ cD cP b
  have htC (K : CochainComplex A ℤ) :
      (T.mapHomologicalComplex (.up ℤ)).map (a.inv.app K) ≫
        b.hom.app ((T.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := by
    ext i
    simpa [a, b, Functor.mapHomologicalComplex] using ht (K.X i)
  obtain ⟨ht1, ht2⟩ := localizedCancellation_triangles DerivedCategory.Q W
    _ _ _ _ cP cD a b htC
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    cP, cD, inferInstance, inferInstance, hnP, hnD, alpha, beta,
    localizedCancellation_commShift DerivedCategory.Q W _ _ _ _ cP cD a,
    localizedCancellation_commShift DerivedCategory.Q W _ _ _ _ cD cP b,
    localizedCancellation_app DerivedCategory.Q W _ _ _ _ cP cD a,
    localizedCancellation_app DerivedCategory.Q W _ _ _ _ cD cP b,
    ht1, ht2, hcoh, inferInstance, inferInstance, inferInstance, inferInstance⟩

variable (X : Scheme.{t})
  [EssentiallySmall.{max a (t + 1)} X.ProEt]
  (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)})

/-- The existing module category on the small pro-etale site.
Source: Stacks, 03DA (blueprint: lem-pur-line-unbounded-derived-tensor). -/
abbrev Modules := KFlatFixedTensor.Modules.{t + 1, t, max a (t + 1)} R

/-- Global sections of the given commutative ring sheaf, with the coefficient size fixed.
Source: Stacks, 04TT (blueprint: lem-pur-line-unbounded-derived-tensor). -/
abbrev scalars := RingCat.sectionsSubring
  (R.obj ⋙ forget₂ CommRingCat.{max a (t + 1)} RingCat.{max a (t + 1)})

/-- The existing global-section action on module morphisms, componentwise on sections.
Source: Stacks, 04TT (blueprint: lem-pur-line-unbounded-derived-tensor). -/
instance coefficientLinear : Linear (scalars.{t, a} X R) (Modules.{t, a} X R) :=
  SheafOfModules.homLinear.{max a (t + 1), t, t + 1, max a (t + 1)} R.obj
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{max a (t + 1)} RingCat.{max a (t + 1)})).obj R).property

/-- The existing internal sheaf dual, without a change of site or module universe.
Source: Stacks, 0B8Q (blueprint: lem-pur-line-unbounded-derived-tensor). -/
abbrev dual (P : Modules.{t, a} X R) : Modules.{t, a} X R :=
  homObj.{max a (t + 1), t, t + 1, max a (t + 1)} (R := R) P
    (𝟙_ (Modules.{t, a} X R))

/-- Ordinary tensor with a fixed right factor.
Source: Stacks, 03EK (blueprint: lem-pur-line-unbounded-derived-tensor). -/
def tensor (P : Modules.{t, a} X R) : Modules.{t, a} X R ⥤ Modules.{t, a} X R := tensorRight P

/-- Additivity of the existing ordinary tensor functor.
Source: Stacks, 03EK (blueprint: lem-pur-line-unbounded-derived-tensor). -/
instance tensorAdditive (P : Modules.{t, a} X R) : (tensor.{t, a} X R P).Additive :=
  inferInstanceAs (tensorRight P).Additive

/-- A module in degree zero in the unbounded cochain category.
Source: Stacks, 06YN (blueprint: lem-pur-line-unbounded-derived-tensor). -/
abbrev single (P : Modules.{t, a} X R) : CochainComplex (Modules.{t, a} X R) ℤ :=
  (CochainComplex.singleFunctor (Modules.{t, a} X R) 0).obj P

/-- The canonical pure tensor in the localization tensor, via the sheafification unit.
Source: Stacks, 03EK (blueprint: lem-pur-line-unbounded-derived-tensor). -/
def pureTensor (P Q : Modules.{t, a} X R) (U : X.ProEtᵒᵖ)
    (p : P.val.obj U) (q : Q.val.obj U) : (P ⊗ Q).val.obj U :=
  (tensorObjIsoSheafification P Q).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app (P.val ⊗ Q.val)).app U
          (p ⊗ₜ[R.obj.obj U] q))

/-- Associate, evaluate the last two factors, then apply the right unitor.
Source: Stacks, 0B8N (blueprint: lem-pur-line-unbounded-derived-tensor). -/
def cancellation (P Q : Modules.{t, a} X R) (e : P ⊗ Q ≅ 𝟙_ (Modules.{t, a} X R)) :
    tensor.{t, a} X R P ⋙ tensor.{t, a} X R Q ≅ 𝟭 (Modules.{t, a} X R) :=
  (tensorRightTensor P Q).symm ≪≫ (tensoringRight (Modules.{t, a} X R)).mapIso e ≪≫
    rightUnitorNatIso (Modules.{t, a} X R)

private theorem cancellation_eq (P Q : Modules.{t, a} X R)
    (e : P ⊗ Q ≅ 𝟙_ (Modules.{t, a} X R)) :
    cancellation X R P Q e = LineEvaluation.cancellation R P Q e := rfl

/-- Collapse the total tensor with a degree-zero right factor to termwise tensor.
Source: Stacks, 06YU (blueprint: lem-pur-line-unbounded-derived-tensor). -/
def collapse (P : Modules.{t, a} X R) :
    (KFlatFixedTensor.totalTensor.{t + 1, t, max a (t + 1)} R).flip.obj (single.{t, a} X R P) ≅
      (tensor.{t, a} X R P).mapHomologicalComplex (.up ℤ) :=
  CochainComplex.map₂HomologicalComplexFlipObjSingleIso
    (KFlatFixedTensor.ordinaryTensor.{t + 1, t, max a (t + 1)} R) P

variable [HasDerivedCategory.{w} (Modules.{t, a} X R)]

/-- Tensor with the degree-zero object using exactly the published derived tensor.
Source: Stacks, 06YU (blueprint: lem-pur-line-unbounded-derived-tensor). -/
def derived (P : Modules.{t, a} X R) :
    DerivedCategory (Modules.{t, a} X R) ⥤ DerivedCategory (Modules.{t, a} X R) :=
  (KFlatFixedTensor.derivedTensor.{t + 1, t, max a (t + 1), w} R).flip.obj
    (DerivedCategory.Q.obj (single.{t, a} X R P))

/-- The canonical normalization of a termwise comparison on resolving complexes.
It uses the actual K-flat representative comparison and the degree-zero total collapse.
Source: Stacks, 06YU and 015F (blueprint: lem-pur-line-unbounded-derived-tensor). -/
def normalization (P : Modules.{t, a} X R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) (single.{t, a} X R P))
    (hPf : ∀ n : ℤ, IsFlatOnSite.{t + 1, t, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) ((single.{t, a} X R P).X n))
    (F : DerivedCategory (Modules.{t, a} X R) ⥤ DerivedCategory (Modules.{t, a} X R))
    (hF : F = derived.{t, a} X R P) (K : CochainComplex (Modules.{t, a} X R) ℤ)
    (c : F.obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj
      (((tensor.{t, a} X R P).mapHomologicalComplex (.up ℤ)).obj K)) : Prop :=
  ∀ (hK : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) K)
    (hKf : ∀ n : ℤ, IsFlatOnSite.{t + 1, t, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) (K.X n)),
    c = eqToIso (congrArg (fun H ↦ H.obj (DerivedCategory.Q.obj K)) hF) ≪≫
      (KFlatFixedTensor.representativeIso.{t + 1, t, max a (t + 1), w} R K
        (single.{t, a} X R P) hK hP hKf hPf).symm ≪≫
          DerivedCategory.Q.mapIso ((collapse.{t, a} X R P).app K)

/-- Tensoring an arbitrary unbounded complex with a locally free line is termwise,
with its inverse given by the internal dual and the specified evaluation. Global-section
linearity is equivalent to the universal B-linearity clause: every sheaf B-algebra
structure is a ring map B → Γ(R), and B = Γ(R) is itself allowed. Every component of
an ordinary evaluation is R-linear; the derived evaluations are their images under Q,
as required by the two representative equations.

Source: Stacks, Tags 0B8Q, 0B8N, 06YN, 06YU, 015F and 010N;
blueprint Tate-twist local freeness, proof (3)
(blueprint: lem-pur-line-unbounded-derived-tensor).

Proof plan (all eight steps of the node):
1. On a trivializing slice write P = Rp and its internal dual = Rp*. Evaluation
   sends ap tensor bp* to ab; its inverse sends a to ap tensor p*. Under p' = up,
   p'* = u⁻¹p*, so the inverses agree on overlaps and glue (0B8Q).
2. Associate, evaluate and apply the unitor, in both orders. On pure tensors the
   resulting inverse-pair triangle identities are the identities cx tensor p = x tensor cp
   and dx tensor p* = x tensor dp*. These local identities glue (0B8N).
3. The ordinary inverse tensor equivalence is additive and preserves finite limits
   and colimits by their universal properties. Thus both factors are flat.
4. Tot(C tensor L[0]) is degreewise C^i tensor L with differential d tensor 1.
   Exactness identifies its cohomology with H^i(C) tensor L. It sends acyclics to
   acyclics, proving K-flatness of L[0], with flat terms including the zero terms.
5. Use lem-weil-pbc-kflat-fixed-tensor-triangulated for both lines and the exact
   functor factorization (015F). The localization universal property identifies the
   derived tensor with the termwise induced functor. The comparisons commute with
   integer shifts and preserve distinguished triangles, including connecting arrows.
6. Localize the degreewise cancellation isomorphisms. Uniqueness of localization
   of natural transformations descends their compositions, inverses and triangle
   identities. Their components satisfy exactly the representative equations below.
7. Exact-functor cohomology (010N) and the termwise comparisons give the natural
   H^i isomorphisms, independent of representatives by localization. No bound enters.
8. Balanced tensor is linear over Γ(R); linear localization and the exact-linear
   derived-functor lemma give linearity of both derived functors. The evaluations
   are images of R-linear sheaf maps. Restrict scalars along B → Γ(R).
-/
theorem line_unbounded_derived_tensor (P : Modules.{t, a} X R)
    [P.IsFiniteLocallyFreeOfRank 1] :
    IsFlatOnSite.{t + 1, t, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) P ∧
    IsFlatOnSite.{t + 1, t, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) (dual.{t, a} X R P) ∧
    ∃ hP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) (single.{t, a} X R P),
    ∃ hD : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) (single.{t, a} X R (dual.{t, a} X R P)),
    ∃ hPf : ∀ n : ℤ, IsFlatOnSite.{t + 1, t, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) ((single.{t, a} X R P).X n),
    ∃ hDf : ∀ n : ℤ, IsFlatOnSite.{t + 1, t, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) ((single.{t, a} X R (dual.{t, a} X R P)).X n),
    PreservesFiniteLimits (tensor.{t, a} X R P) ∧ PreservesFiniteColimits (tensor.{t, a} X R P) ∧
    PreservesFiniteLimits (tensor.{t, a} X R (dual.{t, a} X R P)) ∧
    PreservesFiniteColimits (tensor.{t, a} X R (dual.{t, a} X R P)) ∧
    ∃ e : P ⊗ dual.{t, a} X R P ≅ 𝟙_ (Modules.{t, a} X R),
      (∀ (U : X.ProEtᵒᵖ) (p : P.val.obj U) (φ : (dual.{t, a} X R P).val.obj U),
        e.hom.val.app U (pureTensor.{t, a} X R P (dual.{t, a} X R P) U p φ) =
          φ.app (op (Over.mk (𝟙 U.unop))) p) ∧
      (∀ (U : X.ProEtᵒᵖ) (p : P.val.obj U) (φ : (dual.{t, a} X R P).val.obj U),
        φ.app (op (Over.mk (𝟙 U.unop))) p = (1 : R.obj.obj U) →
        ∀ b : R.obj.obj U, e.inv.val.app U b =
          pureTensor.{t, a} X R P (dual.{t, a} X R P) U (b • p) φ) ∧
      ∃ F G : DerivedCategory (Modules.{t, a} X R) ⥤ DerivedCategory (Modules.{t, a} X R),
      ∃ hF : F = derived.{t, a} X R P,
      ∃ hG : G = derived.{t, a} X R (dual.{t, a} X R P),
      comparisonData (scalars.{t, a} X R)
        (tensor.{t, a} X R P) (tensor.{t, a} X R (dual.{t, a} X R P))
        (cancellation.{t, a} X R P (dual.{t, a} X R P) e)
        (cancellation.{t, a} X R (dual.{t, a} X R P) P
          ((β_ (dual.{t, a} X R P) P) ≪≫ e)) F G
        (normalization.{t, a} X R P hP hPf F hF)
        (normalization.{t, a} X R (dual.{t, a} X R P) hD hDf G hG) := by
  classical
  let Rm := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat RingCat)).obj R
  have hcover : ∀ U : X.ProEt, ∃ s : Sieve U, s ∈ Scheme.ProEt.topology X U ∧
      ∀ (V : X.ProEt) (f : V ⟶ U), s f →
        Nonempty (P.over V ≅ unit (Rm.over V)) := by
    obtain ⟨I, V, hV, h⟩ :=
      (isFiniteLocallyFreeOfRank_iff_exists_over_iso_free (M := P) (r := 1)).mp
        inferInstance
    intro U
    refine ⟨Sieve.ofObjects V U, hV U, ?_⟩
    rintro Z f ⟨i, ⟨g⟩⟩
    let e : P.over (V i) ≅ unit (Rm.over (V i)) :=
      (h i).some ≪≫ freeUniqueIso (ULift (Fin 1))
    exact ⟨((overFunctorMap Rm g).app P).symm ≪≫
      (overMap Rm g).mapIso e ≪≫ overMapUnitIso (R := Rm) g⟩
  obtain ⟨_, _, _, hPl, hPc, hDl, hDc, hP, hD, hPT, hDT,
    e, he, hei, a, b, ha, hb, ht, _, _⟩ :=
    LineEvaluation.evaluation_inverse_pair.{t + 1, t, max a (t + 1)} R P hcover
  obtain ⟨hK, hKf, _, _, hcollapseP, _, _, _, sP, htriP, chiP, hchiP, hnP,
    etaP, hetaP, heP, hcohP⟩ :=
    FlatSingleDerivedNormalization.flat_single_derived_normalization.{t + 1, t,
      max a (t + 1), w} R P hP
  obtain ⟨hKD, hKDf, _, _, hcollapseD, _, _, _, sD, htriD, chiD, hchiD, hnD,
    etaD, hetaD, heD, _⟩ :=
    FlatSingleDerivedNormalization.flat_single_derived_normalization.{t + 1, t,
      max a (t + 1), w} R (dual.{t, a} X R P) hD
  refine ⟨hP, hD, hK, hKD, hKf, hKDf, hPl, hPc, hDl, hDc, e, he,
    (fun U p phi h ↦ (hei U p phi h).2.1), derived.{t, a} X R P,
    derived.{t, a} X R (dual.{t, a} X R P), rfl, rfl, ?_⟩
  let := sP
  let := sD
  have := hPl
  have := hPc
  have := hDl
  have := hDc
  have := hPT
  have := hDT
  have := hchiP
  have := hchiD
  have := hcollapseP
  have := hcollapseD
  let cP := chiP ≪≫ Functor.isoWhiskerRight
    (FlatSingleDerivedNormalization.collapse R P) DerivedCategory.Q
  let cD := chiD ≪≫ Functor.isoWhiskerRight
    (FlatSingleDerivedNormalization.collapse R (dual.{t, a} X R P)) DerivedCategory.Q
  have hcP : NatTrans.CommShift cP.hom ℤ := by
    change NatTrans.CommShift (chiP.hom ≫
      Functor.whiskerRight (FlatSingleDerivedNormalization.collapse R P).hom
        DerivedCategory.Q) ℤ
    infer_instance
  have hcD : NatTrans.CommShift cD.hom ℤ := by
    change NatTrans.CommShift (chiD.hom ≫
      Functor.whiskerRight (FlatSingleDerivedNormalization.collapse R (dual.{t, a} X R P)).hom
        DerivedCategory.Q) ℤ
    infer_instance
  have hLP := Functor.linear_of_iso (scalars.{t, a} X R) etaP.symm
  have hLD := Functor.linear_of_iso (scalars.{t, a} X R) etaD.symm
  have := htriP
  have := htriD
  apply comparison_of_localized_pair (scalars.{t, a} X R) _ _ _ _ _ _ _ _ cP cD
    (aP := a) (aD := b) (haP := ha.trans (cancellation_eq X R _ _ e).symm)
    (haD := hb.trans (cancellation_eq X R _ _ ((β_ (dual.{t, a} X R P) P) ≪≫ e)).symm)
  · intro K hK' hKf'
    dsimp only [normalization, cP, NatIso.trans_app]
    simp only [eqToIso_refl, Iso.refl_trans]
    exact whiskered_normalization _ _ _ _ _ (hnP K hK' hKf')
  · intro K hK' hKf'
    dsimp only [normalization, cD, NatIso.trans_app]
    simp only [eqToIso_refl, Iso.refl_trans]
    exact whiskered_normalization _ _ _ _ _ (hnD K hK' hKf')
  · exact ht
  · intro i
    exact ⟨(hcohP i).choose⟩

end SheafOfModules.LineUnbounded
