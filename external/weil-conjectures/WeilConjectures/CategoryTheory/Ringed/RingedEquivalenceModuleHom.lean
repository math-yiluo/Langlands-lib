/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedPresentationData

import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.ProperBaseChange.AlgebraicInverseImageOfTransport
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
import all WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Auxiliary ringed presentation comparisons -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

open SheafOfModules
open SheafOfModules.GeometricConstruction

private theorem equivalence_of_underlying_adjunction
    {A B X Y : Type*} [Category* A] [Category* B] [Category* X] [Category* Y]
    (L : X ⥤ Y) (V : Y ⥤ X) (a : L ⊣ V) [L.IsEquivalence]
    (F : A ⥤ B) (G : B ⥤ A) (b : F ⊣ G)
    (U : A ⥤ X) (W : B ⥤ Y) [U.ReflectsIsomorphisms] [W.ReflectsIsomorphisms]
    (i : F ⋙ W ≅ U ⋙ L) (j : G ⋙ U ≅ W ⋙ V)
    (h : ∀ M N f, U.map (b.homEquiv M N f) ≫ j.hom.app N =
      a.homEquiv _ _ (i.inv.app M ≫ W.map f)) : F.IsEquivalence := by
  have hu (M : A) : IsIso (b.unit.app M) := by
    have he := h M (F.obj M) (𝟙 _)
    simp only [b.homEquiv_id, W.map_id] at he
    change U.map (b.unit.app M) ≫ j.hom.app (F.obj M) =
      a.homEquiv _ _ (i.inv.app M ≫ 𝟙 _) at he
    rw [Category.comp_id, a.homEquiv_unit] at he
    have : IsIso (U.map (b.unit.app M) ≫ j.hom.app (F.obj M)) := by
      rw [he]
      infer_instance
    have : IsIso (U.map (b.unit.app M)) :=
      IsIso.of_isIso_comp_right (U.map (b.unit.app M)) (j.hom.app (F.obj M))
    exact isIso_of_reflects_iso _ U
  have hc (N : B) : IsIso (b.counit.app N) := by
    have he := h (G.obj N) N (b.counit.app N)
    have hb : b.homEquiv (G.obj N) N (b.counit.app N) = 𝟙 _ := by
      rw [← b.homEquiv_symm_id, Equiv.apply_symm_apply]
    rw [hb, U.map_id, Category.id_comp] at he
    have he' : i.inv.app (G.obj N) ≫ W.map (b.counit.app N) =
        (a.homEquiv _ _).symm (j.hom.app N) := by
      exact (a.homEquiv (U.obj (G.obj N)) (W.obj N)).eq_symm_apply.mpr he.symm
    have : IsIso (i.inv.app (G.obj N) ≫ W.map (b.counit.app N)) := by
      rw [he', Adjunction.homEquiv_counit]
      infer_instance
    have : IsIso (W.map (b.counit.app N)) :=
      IsIso.of_isIso_comp_left (i.inv.app (G.obj N)) (W.map (b.counit.app N))
    exact isIso_of_reflects_iso _ W
  have := hu
  have := hc
  exact b.toEquivalence.isEquivalence_functor

-- Elaborate the transported operation comparisons and the two lifted adjunctions.
private theorem inverse_image_equivalence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap] :
    ∃ I : AlgebraicInverseImage e.inverse S R,
      I.ringUnderlying.hom = e.ringMap ∧ I.modules.IsEquivalence ∧
        Nonempty (I.modules ⊣ e.modules) := by
  have := e.leftExact
  let er := (asIso e.ringMap).symm
  have ha : e.inverse.map (radd S) ≫ e.ringMap =
      prodComparison e.inverse (rset S) (rset S) ≫
        prod.map e.ringMap e.ringMap ≫ radd R :=
    binary_of_graph e.inverse e.ringMap e.ringMap e.ringMap (radd S) (radd R)
      (fun U x y ↦ @Add.add (S.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add (R.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) e.ring_add
  have hm : e.inverse.map (rmul S) ≫ e.ringMap =
      prodComparison e.inverse (rset S) (rset S) ≫
        prod.map e.ringMap e.ringMap ≫ rmul R :=
    binary_of_graph e.inverse e.ringMap e.ringMap e.ringMap (rmul S) (rmul R)
      (fun U x y ↦ @Mul.mul (S.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Mul.mul (R.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) e.ring_mul
  have ha' : e.inverse.map (radd S) =
      prodComparison e.inverse (rset S) (rset S) ≫
        prod.map er.inv er.inv ≫ radd R ≫ er.hom := by
    apply (cancel_mono e.ringMap).mp
    change e.inverse.map (radd S) ≫ e.ringMap =
      (prodComparison e.inverse (rset S) (rset S) ≫
        prod.map e.ringMap e.ringMap ≫ radd R ≫ inv e.ringMap) ≫ e.ringMap
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using ha
  have hm' : e.inverse.map (rmul S) =
      prodComparison e.inverse (rset S) (rset S) ≫
        prod.map er.inv er.inv ≫ rmul R ≫ er.hom := by
    apply (cancel_mono e.ringMap).mp
    change e.inverse.map (rmul S) ≫ e.ringMap =
      (prodComparison e.inverse (rset S) (rset S) ≫
        prod.map e.ringMap e.ringMap ≫ rmul R ≫ inv e.ringMap) ≫ e.ringMap
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hm
  obtain ⟨F, G, i, j, hF, hG, B, hBL, hBR, hB⟩ :=
    geometric_module_transport K J e.inverse e.direct e.adj S R R er
      (radd S) (rmul S) (radd R) (rmul R)
      ⟨(fun _ _ ↦ rfl), (fun _ _ ↦ rfl), (fun _ _ ↦ rfl),
        (fun _ _ ↦ rfl), ha', hm'⟩ (𝟙 R)
  have hr : restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map (𝟙 R)) =
      𝟭 (PresentationModules R) := by
    rw [Functor.map_id]
    rfl
  let B' (M) (H) : (F.obj M ⟶ H) ≃ (M ⟶ G.obj H) := B M H
  have hbL {M N} (f : M ⟶ N) (H) (g : F.obj N ⟶ H) :
      B' M H (F.map f ≫ g) = f ≫ B' N H g := hBL f H g
  have hbR (M) {H H'} (f : F.obj M ⟶ H) (g : H ⟶ H') :
      B' M H' (f ≫ g) = B' M H f ≫ G.map g := hBR M f g
  let b : F ⊣ G := Adjunction.mkOfHomEquiv {
    homEquiv := B'
    homEquiv_naturality_left_symm := by
      intro M N H f g
      apply (B' M H).injective
      rw [Equiv.apply_symm_apply, hbL, Equiv.apply_symm_apply]
    homEquiv_naturality_right := fun f g ↦ hbR _ f g }
  have hb (M N) (f : F.obj M ⟶ N) :
      (presentationForget S).map (b.homEquiv M N f) ≫ j.hom.app N =
        e.adj.homEquiv _ _ (i.inv.app M ≫ (presentationForget R).map f) := by
    rw [show b.homEquiv M N = B' M N by
      simp only [b, Adjunction.mkOfHomEquiv_homEquiv]]
    have hh := hB M N f
    change (presentationForget S).map (B' M N f) ≫ j.hom.app N =
      e.adj.homEquiv _ _ (i.inv.app M ≫ (presentationForget R).map f) at hh
    exact hh
  have hEquiv : F.IsEquivalence :=
    equivalence_of_underlying_adjunction e.inverse e.direct e.adj F G b
      (presentationForget S) (presentationForget R) i j hb
  obtain ⟨I, hIF, hIr, hIi⟩ :=
    algebraicInverseImage_of_module_transport K J e.inverse S R er F i hF
  have hI : I.modules.IsEquivalence := by rw [hIF]; exact hEquiv
  have hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map (𝟙 R) =
      I.ringUnderlying.inv ≫ e.ringMap := by
    rw [hIr]
    change 𝟙 _ = inv e.ringMap ≫ e.ringMap
    simp
  obtain ⟨a⟩ := supplied_adjunction e R I (𝟙 R) hc
  let t : tensorFunctor (𝟙 R) ≅ 𝟭 (PresentationModules R) :=
    ((tensorAdjunction (𝟙 R)).ofNatIsoRight (eqToIso hr)).leftAdjointUniq Adjunction.id
  let q : I.modules ⋙ tensorFunctor (𝟙 R) ≅ I.modules :=
    Functor.isoWhiskerLeft I.modules t ≪≫ Functor.rightUnitor _
  exact ⟨I, by rw [hIr]; rfl, hI, ⟨a.ofNatIsoLeft q⟩⟩

private theorem closed_hom_equivalence
    {A B : Type*} [Category* A] [Category* B]
    {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
    (S : WeilConjectures.CoefficientClosedStructure H)
    (T : WeilConjectures.CoefficientClosedStructure I)
    (E : A ≌ B) (μ : S.tensor ⋙ E.functor ≅
      (E.functor.prod E.functor) ⋙ T.tensor) :
    Nonempty (H ⋙ E.functor ≅ (E.functor.op.prod E.functor) ⋙ I) := by
  let p := (𝟭 Aᵒᵖ).prod E.functor
  let d : (E.functor.op.prod E.functor) ⋙ I ⋙ E.inverse ≅
      (𝟭 Aᵒᵖ).prod (E.functor ⋙ E.inverse) ⋙ H :=
    Functor.isoWhiskerLeft p (ClosedScalarHom.iso S T E.toAdjunction μ)
  let t : H ≅ (𝟭 Aᵒᵖ).prod (E.functor ⋙ E.inverse) ⋙ H :=
    (Functor.leftUnitor H).symm ≪≫ Functor.isoWhiskerRight
      (NatIso.prod (Iso.refl (𝟭 Aᵒᵖ)) E.unitIso) H
  let q : H ≅ ((E.functor.op.prod E.functor) ⋙ I) ⋙ E.inverse := t ≪≫ d.symm
  exact ⟨Functor.isoWhiskerRight q E.functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ E.counitIso ≪≫ Functor.rightUnitor _⟩

private def flat_representatives
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    ObjectProperty (CochainComplex (PresentationModules R) ℤ) :=
  fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ n, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)

private def flat_tensor_representative
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{u + 1} (PresentationModules R)]
    (S : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u, u, u, u + 1} J R))
    (T : WeilConjectures.CoefficientTensorModels.{u, u, u, u + 1} J R S)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{u, u, u, u + 1} J R S T β) :
    ((flat_representatives R).ι.prod (flat_representatives R).ι) ⋙
        WeilConjectures.coefficientTotalTensor.{u, u, u} J R ⋙ DerivedCategory.Q ≅
      (((flat_representatives R).ι ⋙ DerivedCategory.Q).prod
        ((flat_representatives R).ι ⋙ DerivedCategory.Q)) ⋙ S.tensor :=
  NatIso.ofComponents (fun P ↦ hc.tensorIso P.1.obj P.2.obj
    (Or.inl ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2
      P.1.property.1))) (by
        intro P Q f
        exact hc.tensorIso_naturality _ _ _ _ _ _ f.1.hom f.2.hom)

/-- The module adjunction of a ringed equivalence is an equivalence, with its
underlying inverse image, structural rank-one map and forward internal Hom comparison.

Source: Stacks Project, sites-modules.tex, Tags 03CR and 03D7;
sites-cohomology.tex, Tags 07A4 and 08J9.
(blueprint: lem-weil-pbc-ringed-equivalence-module-hom).

Proof: transport the zero, addition, inverse and scalar-action maps along the
finite-product-preserving equivalence of set sheaves. Its unit and counit
commute with these operations, hence lift to linear isomorphisms. The specified
module direct image agrees with this lift: its generalized-element linearity
identity fixes its action, and the underlying natural comparison fixes its maps.
This gives the module equivalence and the displayed structural equation. Both
functors are additive and preserve all limits and colimits. Localizing their
termwise functors gives the unbounded derived equivalence. Tensor is preserved, since
transport preserves balanced bilinear maps. Apply the closed tensor-Hom
adjunction: maps C → F RHom(L,M) identify successively with maps G C → RHom(L,M),
G C tensor L → M, C tensor F L → F M, and C → RHom(F L,F M).
These identifications are natural in all three objects, so Yoneda produces the
required forward natural isomorphism. The reverse comparison is a formal
consequence of equivalence and is constructed in the parent proof. -/
theorem ringed_equivalence_module_hom
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap] :
    ∃ T : RingedPresentationEquivalenceCore S R,
      Nonempty (T.modules.inverse ≅ e.modules) ∧
      ∃ a : T.modules.functor ⋙ presentationForget R ≅
          presentationForget S ⋙ e.inverse,
        (presentationForget R).map T.forwardUnit.hom =
          a.hom.app (SheafOfModules.unit (localCoefficientRings S)) ≫ e.ringMap := by
  classical
  obtain ⟨I, hIr, hI, ⟨b⟩⟩ := inverse_image_equivalence e
  have := hI
  have := e.leftExact
  have hr : restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map (𝟙 R)) =
      𝟭 (PresentationModules R) := by
    rw [Functor.map_id]
    rfl
  let t : tensorFunctor (𝟙 R) ≅ 𝟭 (PresentationModules R) :=
    ((tensorAdjunction (𝟙 R)).ofNatIsoRight (eqToIso hr)).leftAdjointUniq Adjunction.id
  let F := I.modules ⋙ tensorFunctor (𝟙 R)
  let q : F ≅ I.modules :=
    Functor.isoWhiskerLeft I.modules t ≪≫ Functor.rightUnitor _
  have : F.IsEquivalence := Functor.isEquivalence_of_iso q.symm
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let E := F.asEquivalence
  let am : F ⊣ e.modules := b.ofNatIsoLeft q.symm
  obtain ⟨v, hv⟩ := inverseImage_unit_iso S R e.inverse I
  let a : F ⋙ presentationForget R ≅ presentationForget S ⋙ e.inverse :=
    Functor.isoWhiskerRight q (presentationForget R) ≪≫ I.moduleUnderlying
  let unitF : F.obj (SheafOfModules.unit (localCoefficientRings S)) ≅
      SheafOfModules.unit (localCoefficientRings R) := q.app _ ≪≫ v.symm
  have hunit : (presentationForget R).map unitF.hom =
      a.hom.app (SheafOfModules.unit (localCoefficientRings S)) ≫ e.ringMap := by
    have hi : (presentationForget R).map v.inv =
        I.moduleUnderlying.hom.app (SheafOfModules.unit (localCoefficientRings S)) ≫
          I.ringUnderlying.hom := by
      apply (cancel_epi ((presentationForget R).map v.hom)).mp
      rw [← Functor.map_comp, v.hom_inv_id, Functor.map_id, hv]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id]
    dsimp only [unitF, Iso.trans_hom, Iso.symm_hom]
    rw [Functor.map_comp, hi, hIr]
    rfl
  let := HasDerivedCategory.standard (PresentationModules S)
  let := HasDerivedCategory.standard (PresentationModules R)
  obtain ⟨SS, TS, βS, ⟨hS⟩⟩ := ringedDerived_closed_symmetric_monoidal.{u, u, u, u + 1} K S
  obtain ⟨SR, TR, βR, ⟨hR⟩⟩ := ringedDerived_closed_symmetric_monoidal.{u, u, u, u + 1} J R
  have hobj (M) : F.obj M = changeOfRings (𝟙 R) (I.modules.obj M) := rfl
  have hmap {M N} (f : M ⟶ N) : F.map f = eqToHom (hobj M) ≫
      changeOfRingsHom (𝟙 R) (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨⟨k⟩, _⟩ :=
    CanonicalTensorPullbackOfUniverses.canonicalRingedTensorComparison_existsUnique
      S R R e.inverse I (𝟙 R) F hobj e.direct e.adj hmap
  have hLF : F.mapDerivedCategory.IsLeftDerivedFunctor
      F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (PresentationModules S) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  obtain ⟨μ, _, _⟩ :=
    (CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback
      e.inverse e.direct e.adj I (𝟙 R) F hobj hmap F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh.hom hLF
      (flat_representatives S) (flat_representatives R)
      (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl) SS.tensor SR.tensor
      (flat_tensor_representative S SS TS βS hS)
      (flat_tensor_representative R SR TR βR hR) k e.modules am).2
  obtain ⟨hHom⟩ := closed_hom_equivalence SS SR F.mapDerivedCategory.asEquivalence μ
  let T : RingedPresentationEquivalenceCore S R := {
    modules := E
    forwardUnit := unitF
    forwardHom := ⟨hHom⟩ }
  exact ⟨T, ⟨E.toAdjunction.rightAdjointUniq am⟩, a, hunit⟩

end CategoryTheory
