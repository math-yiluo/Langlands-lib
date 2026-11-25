/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement

/-! # Detection of the complex tensor associator on local pure triples

Source: Stacks Project, Tags 03EK and 06YN
(blueprint: lem-sf-ringed-tensor-associator-detection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
-- Keep the localization tensor and its sheafification presentation behind their APIs.
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  CategoryTheory.Adjunction.rightAdjointLaxMonoidal

universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

namespace CategoryTheory.RingedForgetTensorTransposition

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

private theorem presentation_ext₃ (M N T H : RingedTensorModules.{c, v, r} J R)
    (e : (PresheafOfModules.sheafification.{max c v r}
        (𝟙 ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)).obj
        ((M.val ⊗ N.val) ⊗ T.val) ≅
      (SheafOfModules.monoidalCategory R).tensorObj
        ((SheafOfModules.monoidalCategory R).tensorObj M N) T)
    (he : ∀ V x y z, e.hom.val.app V
        (((PresheafOfModules.sheafificationAdjunction.{max c v r}
          (𝟙 ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)).unit.app
              ((M.val ⊗ N.val) ⊗ T.val)).app V
                ((x ⊗ₜ[R.obj.obj V] y) ⊗ₜ[R.obj.obj V] z)) =
      CochainPullback.moduleTmul (R := R) _ _ V
        (CochainPullback.moduleTmul (R := R) M N V x y) z)
    {f g : (SheafOfModules.monoidalCategory R).tensorObj
      ((SheafOfModules.monoidalCategory R).tensorObj M N) T ⟶ H}
    (h : ∀ V x y z,
      f.val.app V (CochainPullback.moduleTmul (R := R) _ _ V
        (CochainPullback.moduleTmul (R := R) M N V x y) z) =
      g.val.app V (CochainPullback.moduleTmul (R := R) _ _ V
        (CochainPullback.moduleTmul (R := R) M N V x y) z)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v r}
    (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)
  apply (cancel_epi e.hom).1
  apply (adj.homEquiv ((M.val ⊗ N.val) ⊗ T.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro x y z
  change f.val.app V (e.hom.val.app V
      ((adj.unit.app ((M.val ⊗ N.val) ⊗ T.val)).app V
        ((x ⊗ₜ[R.obj.obj V] y) ⊗ₜ[R.obj.obj V] z))) =
    g.val.app V (e.hom.val.app V
      ((adj.unit.app ((M.val ⊗ N.val) ⊗ T.val)).app V
        ((x ⊗ₜ[R.obj.obj V] y) ⊗ₜ[R.obj.obj V] z)))
  rw [he]
  exact h V x y z

private theorem pure_ext₃ (M N T H : RingedTensorModules.{c, v, r} J R)
    {f g : (SheafOfModules.monoidalCategory R).tensorObj
      ((SheafOfModules.monoidalCategory R).tensorObj M N) T ⟶ H}
    (h : ∀ V x y z,
      f.val.app V (CochainPullback.moduleTmul (R := R) _ _ V
        (CochainPullback.moduleTmul (R := R) M N V x y) z) =
      g.val.app V (CochainPullback.moduleTmul (R := R) _ _ V
        (CochainPullback.moduleTmul (R := R) M N V x y) z)) : f = g := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  let := SheafOfModules.monoidalCategory R
  let RB := (sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 RB.obj)
  let S := PresheafOfModules.sheafification.{max c v r} (𝟙 RB.obj)
  let E := M.val ⊗ N.val
  have hη : (J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj))
      (adj.unit.app E) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms (𝟙 RB.obj)]
    change IsIso (S.map (adj.unit.app E))
    infer_instance
  have hi : IsIso (S.map ((adj.unit.app E) ⊗ₘ 𝟙 T.val)) := by
    have ht := (J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj)).tensorHom_mem
      (adj.unit.app E) (𝟙 T.val) hη
      ((J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj)).id_mem _)
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 RB.obj)] at ht
    exact ht
  let q := S.map ((adj.unit.app E) ⊗ₘ 𝟙 T.val) ≫
    (SheafOfModules.tensorObjIsoSheafification (S.obj E) T).inv ≫
      ((SheafOfModules.tensorObjIsoSheafification M N).inv ⊗ₘ 𝟙 T)
  have : IsIso q := by dsimp only [q]; infer_instance
  apply presentation_ext₃.{c, v, r} J R M N T H (asIso q) ?_ h
  intro V x y z
  have he := congrArg (fun k ↦ k.app V ((x ⊗ₜ[R.obj.obj V] y) ⊗ₜ[R.obj.obj V] z))
    (adj.unit.naturality ((adj.unit.app E) ⊗ₘ 𝟙 T.val))
  change (adj.unit.app ((S.obj E).val ⊗ T.val)).app V
      ((adj.unit.app E).app V (x ⊗ₜ[R.obj.obj V] y) ⊗ₜ[R.obj.obj V] z) =
    (S.map ((adj.unit.app E) ⊗ₘ 𝟙 T.val)).val.app V
      ((adj.unit.app (E ⊗ T.val)).app V
        ((x ⊗ₜ[R.obj.obj V] y) ⊗ₜ[R.obj.obj V] z)) at he
  change (((SheafOfModules.tensorObjIsoSheafification M N).inv ⊗ₘ 𝟙 T).val.app V)
      ((SheafOfModules.tensorObjIsoSheafification (S.obj E) T).inv.val.app V
        ((S.map ((adj.unit.app E) ⊗ₘ 𝟙 T.val)).val.app V
          ((adj.unit.app (E ⊗ T.val)).app V
            ((x ⊗ₜ[R.obj.obj V] y) ⊗ₜ[R.obj.obj V] z)))) = _
  rw [← he]
  change (((SheafOfModules.tensorObjIsoSheafification M N).inv ⊗ₘ 𝟙 T).val.app V)
      (CochainPullback.moduleTmul (R := R) (S.obj E) T V
        ((adj.unit.app E).app V (x ⊗ₜ[R.obj.obj V] y)) z) = _
  erw [CochainPullback.moduleTmul_map (R := R)]
  rfl

/-- Local pure triples determine the total-complex associator.
Source: Stacks Project, Tags 03EK and 06YN.
(blueprint: lem-sf-ringed-tensor-associator-detection)

Proof: maps out of the iterated sheaf tensor are detected on local pure triples.
Indeed, tensor the inner sheafification unit with the third factor and sheafify;
this is invertible because tensor preserves local equivalences. Cancel it and the
two tensor/sheafification isomorphisms. The sheafification adjunction and sectionwise
threefold tensor extensionality now give the detection criterion. Restrict a map
of total complexes to each triple coproduct summand and use that criterion. The
given generator formula and the native associator formula agree, so coproduct and
degreewise extensionality identify the maps. -/
theorem coefficientAssociator_eq_native
    (P Q N : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (a : (coefficientTotalTensor.{r, c, v} J R).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q), N) ≅
      (coefficientTotalTensor.{r, c, v} J R).obj
        (P, (coefficientTotalTensor.{r, c, v} J R).obj (Q, N)))
    (ha : ∀ (p q t pq qt n : ℤ) (hpq : p + q = pq) (hqt : q + t = qt)
      (hn : pq + t = n) (hn' : p + qt = n) (V : Cᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) (z : (N.X t).val.obj V),
      (a.hom.f n).val.app V
        (coefficientTensorGenerator.{r, c, v} J R
          ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) N pq t n hn V
          (coefficientTensorGenerator.{r, c, v} J R P Q p q pq hpq V x y) z) =
      coefficientTensorGenerator.{r, c, v} J R P
        ((coefficientTotalTensor.{r, c, v} J R).obj (Q, N)) p qt n hn' V x
        (coefficientTensorGenerator.{r, c, v} J R Q N q t qt hqt V y z)) :
    let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
    let := SheafOfModules.monoidalCategory R
    a.hom = (α_ P Q N).hom := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  let := SheafOfModules.monoidalCategory R
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q t h
  have hn : p + q + t = n := h
  rw [CochainComplex.Monoidal.ι₁₂_eq P Q N p q t (p + q) n rfl hn]
  apply pure_ext₃.{c, v, r} J R (P.X p) (Q.X q) (N.X t) _
  intro V x y z
  have hn' : p + (q + t) = n := by omega
  have hb := ha p q t (p + q) (q + t) n rfl rfl hn hn' V x y z
  have hc := (RingedDerivedNative.complexConstraints.{c, v, r} J R).associator
    P Q N p q t (p + q) (q + t) n rfl rfl hn hn' V x y z
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    ← tensorHom_id, CochainPullback.moduleTmul_map]
  exact hb.trans hc.symm

end CategoryTheory.RingedForgetTensorTransposition
