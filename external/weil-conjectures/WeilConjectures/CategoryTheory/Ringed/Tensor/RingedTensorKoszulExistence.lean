/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
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
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import Mathlib.CategoryTheory.Localization.Prod

/-! # Koszul exchange for any normalized tensor presentation

Source: Stacks Project, Tags 06YU and 0FPQ; descent of signed total-tensor exchange.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe c v u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory

namespace CategoryTheory

attribute [local irreducible] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [local irreducible] RingedDerivedNative.monoidal RingedDerivedNative.symmetric
  SheafOfModules.cochainModulesSymmetric

/-- The generic preimage equation avoids unfolding a concrete comparison isomorphism. -/
private theorem whisker_preimageIso {B D E : Type*}
    [Category* B] [Category* D] [Category* E] (L : B ⥤ D)
    (FF : ((Functor.whiskeringLeft B D E).obj L).FullyFaithful)
    {G H : D ⥤ E} (e : L ⋙ G ≅ L ⋙ H) :
    Functor.isoWhiskerLeft L (FF.preimageIso e) = e := by
  apply Iso.ext
  exact FF.map_preimage e.hom

attribute [local irreducible] Localization.fullyFaithfulWhiskeringLeft
  Functor.FullyFaithful.preimageIso

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
    CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

/-- The signed exchange descends to every specified K-flat tensor presentation.
Source: Stacks Project, Tags 06YU and 0FPQ
(blueprint: lem-weil-pbc-ringed-tensor-koszul-existence).

Proof: the full subcategory of K-flat complexes presents the derived category.
Compare the specified natural tensor model with the native localized tensor model,
then descend this natural isomorphism through the product localization. Conjugate
native symmetry by this comparison. On K-flat representatives the descended
comparison is the original comparison, so the native symmetry square and its
pure-section formula give the asserted square and the sign (-1)^(pq). -/
theorem ringedTensor_koszul_exists
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S) :
    ∃ σ : S.tensor ≅ (Prod.swap _ _) ⋙ S.tensor,
      ∀ (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
        CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q),
      ∃ β : (coefficientTotalTensor.{u, c, v} J A).obj (P, Q) ≅
          (coefficientTotalTensor.{u, c, v} J A).obj (Q, P),
        (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (V : Cᵒᵖ)
          (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
          (β.hom.f k).val.app V
            (coefficientTensorGenerator.{u, c, v} J A P Q p q k h V x y) =
          (p * q).negOnePow •
            coefficientTensorGenerator.{u, c, v} J A Q P q p k h' V y x) ∧
        (T.iso J A S P Q hP hQ).hom ≫
          σ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        DerivedCategory.Q.map β.hom ≫ (T.iso J A S Q P hQ hP).hom := by
  let D := DerivedCategory (RingedDerivedNative.Modules.{c, v, u} J A)
  let L := coefficientKFlatInclusion.{u, c, v} J A ⋙ DerivedCategory.Q.{w}
  let W := (HomologicalComplex.quasiIso (RingedDerivedNative.Modules.{c, v, u} J A)
    (.up ℤ)).inverseImage (coefficientKFlatInclusion.{u, c, v} J A)
  have : L.IsLocalization W := RingedDerivedNative.kFlatLocalization.{c, v, u, w} J A
  let : MonoidalCategory D := RingedDerivedNative.monoidal.{c, v, u, w} J A
  let : SymmetricCategory D := RingedDerivedNative.symmetric.{c, v, u, w} J A
  let N : D × D ⥤ D := MonoidalCategory.tensor D
  let F := Localization.fullyFaithfulWhiskeringLeft (L.prod L) (W.prod W) D
  let e₀ : (L.prod L) ⋙ S.tensor ≅ (L.prod L) ⋙ N :=
    T.comparison.symm ≪≫ RingedDerivedNative.comparison.{c, v, u, w} J A
  let e : S.tensor ≅ N := F.preimageIso (X := S.tensor) (Y := N) e₀
  have he : Functor.isoWhiskerLeft (L.prod L) e = e₀ :=
    whisker_preimageIso (L.prod L) F e₀
  let b : N ≅ Prod.swap D D ⋙ N := NatIso.ofComponents
    (fun X : D × D ↦ β_ X.1 X.2)
    (fun f ↦ BraidedCategory.braiding_naturality f.1 f.2)
  let σ : S.tensor ≅ (Prod.swap D D) ⋙ S.tensor :=
    e ≪≫ b ≪≫ Functor.isoWhiskerLeft (Prod.swap D D) e.symm
  refine ⟨σ, ?_⟩
  intro P Q hP hQ
  let : MonoidalCategory (RingedDerivedNative.Modules.{c, v, u} J A) :=
    SheafOfModules.cochainModulesMonoidal A
  let : SymmetricCategory (RingedDerivedNative.Modules.{c, v, u} J A) :=
    SheafOfModules.cochainModulesSymmetric A
  let β : (coefficientTotalTensor.{u, c, v} J A).obj (P, Q) ≅
      (coefficientTotalTensor.{u, c, v} J A).obj (Q, P) :=
    β_ P Q
  refine ⟨β, ?_, ?_⟩
  · exact (RingedDerivedNative.complexConstraints.{c, v, u} J A).symmetry P Q
  · have hePQ := congrArg (fun i ↦ i.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) he
    have heQP := congrArg (fun i ↦ i.hom.app (⟨Q, hQ⟩, ⟨P, hP⟩)) he
    change e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      (T.iso J A S P Q hP hQ).inv ≫
        (RingedDerivedNative.tensorIso.{c, v, u, w} J A P Q (Or.inl hP)).hom at hePQ
    change e.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) =
      (T.iso J A S Q P hQ hP).inv ≫
        (RingedDerivedNative.tensorIso.{c, v, u, w} J A Q P (Or.inl hQ)).hom at heQP
    apply (cancel_mono (e.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))).mp
    dsimp only [σ, b, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      NatIso.ofComponents_hom_app, Iso.symm_hom, Functor.comp_obj, Prod.swap_obj,
      NatTrans.comp_app]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [hePQ, heQP]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact RingedDerivedNative.symmetry_square.{c, v, u, w} J A P Q hP hQ

end CategoryTheory
