/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceRepresentativeEvaluation
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

/-! # Slice evaluation compatibility

Source: Stacks Project, Tags 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-evaluation-coherence).
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

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
  CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_iso_naturality
    {D : Type a} [Category.{x} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {P Q L M : D} (e : P ≅ L) (g : Q ⟶ M) :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom e.inv.op g)) e.hom) ≫
        S.evaluation L M = S.evaluation P Q ≫ g := by
  let := S.monoidal
  have hn : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op L)) g)) (𝟙 L)) ≫
      S.evaluation L M = S.evaluation L Q ≫ g := by
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorRight,
      Functor.flip, MonoidalCategory.curriedTensor, MonoidalCategory.tensorHom_id,
      Functor.comp_map, Prod.sectR,
      Functor.id_map] using
      (S.adjunction L).counit.naturality g
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom e.inv.op (𝟙 Q))) (𝟙 L)) ≫
      S.evaluation L Q = S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) e.inv) ≫
        S.evaluation P Q := by
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorRight, MonoidalCategory.tensorLeft,
      Functor.flip, MonoidalCategory.curriedTensor, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom] using S.evaluation_naturality P L Q e.inv
  have hh : H.map (Prod.mkHom e.inv.op g) =
      H.map (Prod.mkHom e.inv.op (𝟙 Q)) ≫
        H.map (Prod.mkHom (𝟙 (op L)) g) := by
    rw [← H.map_comp]
    simp
  rw [hh]
  have ht : S.tensor.map
      (Prod.mkHom (H.map (Prod.mkHom e.inv.op (𝟙 Q)) ≫
        H.map (Prod.mkHom (𝟙 (op L)) g)) e.hom) =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) e.hom) ≫
        S.tensor.map (Prod.mkHom (H.map (Prod.mkHom e.inv.op (𝟙 Q))) (𝟙 L)) ≫
          S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op L)) g)) (𝟙 L)) := by
    simp only [← S.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [ht]
  simp only [Category.assoc]
  rw [hn, ← Category.assoc _ (S.evaluation L Q) g, he]
  simp only [Category.assoc]
  simp only [← Category.assoc, ← S.tensor.map_comp]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_of_iso
    {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
    {H : Dᵒᵖ × D ⥤ D} {HU : Eᵒᵖ × E ⥤ E} {r : D ⥤ E}
    {S : CoefficientClosedStructure H} {SU : CoefficientClosedStructure HU} {K : Prop}
    (d : RingedSliceEvaluationComparisons H HU r S SU K)
    {P Q L M : D} (e : P ≅ L) (e' : Q ≅ M)
    (h : (d.rho (H.obj (op P, Q)) P).inv ≫ r.map (S.evaluation P Q) =
      SU.tensor.map (Prod.mkHom (d.eta P Q).hom (𝟙 (r.obj P))) ≫
        SU.evaluation (r.obj P) (r.obj Q)) :
    (d.rho (H.obj (op L, M)) L).inv ≫ r.map (S.evaluation L M) =
      SU.tensor.map (Prod.mkHom (d.eta L M).hom (𝟙 (r.obj L))) ≫
        SU.evaluation (r.obj L) (r.obj M) := by
  let t := H.map (Prod.mkHom e.inv.op e'.hom)
  have : IsIso (Prod.mkHom e.inv.op e'.hom) :=
    (CategoryTheory.isIso_prod_iff (f := Prod.mkHom e.inv.op e'.hom)).mpr
      ⟨inferInstance, inferInstance⟩
  have : IsIso t := inferInstanceAs (IsIso (H.map (Prod.mkHom e.inv.op e'.hom)))
  have : IsIso (Prod.mkHom (r.map t) (r.map e.hom)) :=
    (CategoryTheory.isIso_prod_iff (f := Prod.mkHom (r.map t) (r.map e.hom))).mpr
      ⟨inferInstance, inferInstance⟩
  have : IsIso (SU.tensor.map (Prod.mkHom (r.map t) (r.map e.hom))) := inferInstance
  have ht := evaluation_iso_naturality S e e'.hom
  change S.tensor.map (Prod.mkHom t e.hom) ≫ S.evaluation L M =
    S.evaluation P Q ≫ e'.hom at ht
  have hn : SU.tensor.map (Prod.mkHom (r.map t) (r.map e.hom)) ≫
      (d.rho (H.obj (op L, M)) L).inv =
      (d.rho (H.obj (op P, Q)) P).inv ≫ r.map (S.tensor.map (Prod.mkHom t e.hom)) := by
    apply (cancel_mono (d.rho (H.obj (op L, M)) L).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      d.rho_naturality, Iso.inv_hom_id_assoc]
  have heta := d.eta_naturality P Q L M e.inv e'.hom
  change r.map t ≫ (d.eta L M).hom =
    (d.eta P Q).hom ≫ HU.map (Prod.mkHom (r.map e.inv).op (r.map e'.hom)) at heta
  have hu := evaluation_iso_naturality SU (r.mapIso e) (r.map e'.hom)
  apply (cancel_epi (SU.tensor.map (Prod.mkHom (r.map t) (r.map e.hom)))).mp
  calc
    _ = (d.rho (H.obj (op P, Q)) P).inv ≫
        r.map (S.tensor.map (Prod.mkHom t e.hom) ≫ S.evaluation L M) := by
      rw [← Category.assoc, hn, Category.assoc, r.map_comp]
    _ = (d.rho (H.obj (op P, Q)) P).inv ≫ r.map (S.evaluation P Q) ≫
        r.map e'.hom := by rw [ht, r.map_comp]
    _ = (SU.tensor.map (Prod.mkHom (d.eta P Q).hom (𝟙 (r.obj P))) ≫
        SU.evaluation (r.obj P) (r.obj Q)) ≫ r.map e'.hom := by
      rw [← Category.assoc, h]
    _ = SU.tensor.map (Prod.mkHom (d.eta P Q).hom (𝟙 (r.obj P))) ≫
        SU.tensor.map (Prod.mkHom
          (HU.map (Prod.mkHom (r.map e.inv).op (r.map e'.hom))) (r.map e.hom)) ≫
            SU.evaluation (r.obj L) (r.obj M) := by
      simpa only [Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc] using
        congrArg (SU.tensor.map (Prod.mkHom (d.eta P Q).hom (𝟙 (r.obj P))) ≫ ·) hu.symm
    _ = _ := by
      simp only [← Category.assoc, ← SU.tensor.map_comp]
      congr 1
      apply congrArg SU.tensor.map
      ext
      · exact heta.symm
      · simp

/-- Exact slice restriction preserves the representative-normalized evaluation counit.
Source: Stacks Project, Tags 08J9 and 08JB, and equation-internal-hom
(blueprint: lem-weil-pbc-ringed-slice-evaluation-coherence).

Proof: resolve L by a flat-term K-flat complex P and M by a K-injective complex I.
Resolve Hom(P,I) by a flat-term K-flat complex Q. Exact restriction preserves the
resolving quasi-isomorphisms, and the kflat field gives the corresponding tensor models
on the slice. The Hom normalization identifies the local components of Hom(P,I) with
those of Hom(rP,rI), through the augmentations to the fixed K-injective replacements.
Apply the uncurry_model fields of T and TU to the maps from Q into those fixed Hom
complexes. Both evaluation chain maps, after the tensor and Hom comparisons, send
a pure tensor x tensor p to q(x)(p). The Hom normalization makes this equality hold
over every further slice object as well. The sheafification universal property and
the coproduct universal property show the two chain maps agree on the entire total
complex. Localize the equality, substitute the representative squares ht and hh,
and cancel the tensor, Hom, and resolving isomorphisms. This proves the displayed
counit identity for the chosen representatives. Naturality of the tensor comparisons,
Hom comparisons, and adjunction counits transports it to the original L and M.
No evaluation map is cancelled, and no boundedness or perfectness is used. -/
theorem ringedSlice_evaluation_coherence
    (U : C) [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U))
      (ht : RingedSliceTensorModel.{c, v, u, w, w'} J A U S T SU TU d)
      (hh : RingedSliceHomModel.{c, v, u, w, w'} J A U S T SU TU d)
      (L M : DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
        CommRingCat.{max c v u} RingCat.{max c v u})).obj A))) :
    (d.rho ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj (op L, M)) L).inv ≫
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map
            (S.evaluation L M) =
      SU.tensor.map (X := ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj
        ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj (op L, M)),
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj L)) (Y :=
        ((derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).obj (op
        ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj L),
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj M),
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj L)) ((d.eta L M).hom, 𝟙 _) ≫
        SU.evaluation
          ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj L)
          ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj M) := by
  classical
  let X := DerivedCategory.Q.objPreimage L
  let Y := DerivedCategory.Q.objPreimage M
  obtain ⟨P, f, hP, fP, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := A) X
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  let I := (coefficientHomResolution.{u, c, v} J A).obj Y
  have : I.IsKInjective := by
    dsimp [I, coefficientHomResolution]
    infer_instance
  let ι := coefficientHomAugmentation.{c, v, u} J A Y
  have hι : QuasiIso ι := by
    exact (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ Y).2
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hf
  have : IsIso (DerivedCategory.Q.map ι) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hι
  let e := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso L
  let e' := (asIso (DerivedCategory.Q.map ι)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso M
  apply evaluation_of_iso d e e'
  apply ringedSlice_representativeEvaluation J A U S T SU TU d ht hh P I hP
  intro n
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso A (P.X n)).symm (fP n)

end CategoryTheory
