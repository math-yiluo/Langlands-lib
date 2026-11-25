/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.QuotientPullbackTensorCoherence
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-! # Reduction of the actual integral projection morphism

The scalar tensor comparison is specified by its computation counits and the signed
ordinary balancing map. Unlike the exact-scalar interface, this applies to reduction
modulo a uniformizer. Positive levels are indexed by n + 1, as in the dependency.

## References

* Stacks 07A4, change-of-rings specialization
* Stacks 07A4, identity-topos scalar extension
* Stacks 0B56, 07A4, 07A6, 0D6D
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.all false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.ProEtale.QuotientChange
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The signed total of the canonical ordinary scalar tensor balancing map. Its
scalar-unit normalization sends (u tensor v) tensor s to
(u tensor 1) tensor (v tensor s), equivalently moving s to the first factor. -/
def scalarTensorTotal (n : ℕ) (T : Scheme.{u})
    (P Q : CochainComplex (Modules (integral l E) T) ℤ) :
    ((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ⟶
      ((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj Q :=
  letI := CondensedRing.internalScalarMonoidal (reduction l E n) T
  ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (extension (reduction l E n) T)).app P).app Q

/-- The type of the scalar tensor balancing isomorphism, natural in both inputs. -/
abbrev ScalarTensorIso (n : ℕ) (T : Scheme.{u}) :=
  (Functor.postcompose₂.obj (D (reduction l E n) T)).obj
      (CondensedRing.derivedTensor (integral l E) T) ≅
    (((Functor.whiskeringLeft₂ _).obj (D (reduction l E n) T)).obj
      (D (reduction l E n) T)).obj (CondensedRing.derivedTensor (finite l E n) T)

/-- Universal computation-counit normalization of the scalar tensor comparison.
On flat-term K-flat representatives all computation maps are invertible, and this
is exactly the specified pure-tensor balancing formula. It also fixes the comparison
on every derived object by the K-flat localization property. -/
def ScalarTensorNormalized (n : ℕ) (T : Scheme.{u})
    (b : ScalarTensorIso l E n T) : Prop :=
  ∀ P Q : CochainComplex (Modules (integral l E) T) ℤ,
    (b.hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
        (compute (reduction l E n) T P ⊗ₘ compute (reduction l E n) T Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          (((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj P)
          (((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj Q) =
      (D (reduction l E n) T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        compute (reduction l E n) T (P ⊗ Q) ≫
        DerivedCategory.Q.map (scalarTensorTotal l E n T P Q)

attribute [local irreducible] ScalarTensorNormalized

section GenericComputations

section CachedGenericStructures
variable {C : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
private noncomputable abbrev cachedComplexMonoidal :
    MonoidalCategory (CochainComplex C ℤ) := inferInstance
private noncomputable abbrev cachedHomotopyMonoidal :
    MonoidalCategory (HomotopyCategory C (.up ℤ)) := inferInstance
private noncomputable abbrev cachedDerivedMonoidal :
    MonoidalCategory (DerivedCategory C) := inferInstance
end CachedGenericStructures
attribute [local instance 2000] cachedComplexMonoidal cachedHomotopyMonoidal
  cachedDerivedMonoidal

private theorem tensorator_Q_generic
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (P Q : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      ((DerivedCategory.quotientCompQhIso C).inv.app P ⊗ₘ
        (DerivedCategory.quotientCompQhIso C).inv.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Q) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app (P ⊗ Q) := by
  unfold Functor.LaxMonoidal.μ
  unfold DerivedCategory.laxMonoidalQ
  unfold inferInstance
  unfold DerivedCategory.instLaxMonoidalQ
  unfold Functor.LaxMonoidal.ofIso
  dsimp only
  rw [Functor.LaxMonoidal.comp_μ]
  change (_ ⊗ₘ _) ≫ (_ ≫ (DerivedCategory.Qh (C := C)).map (𝟙 _)) ≫ _ = _
  rw [(DerivedCategory.Qh (C := C)).map_id, Category.comp_id]
  rfl

@[irreducible] private def canonicalScalarTensorIso (n : ℕ) (T : Scheme.{u}) :
    ScalarTensorIso l E n T := by
  let m := CondensedRing.internalScalarMonoidal (reduction l E n) T
  unfold ScalarTensorIso D CondensedRing.derivedTensor
  exact asIso (extension (reduction l E n) T).leftDerivedTensorComparison

private theorem tensorator_Q_strict {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (P Q : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj P)
        ((HomotopyCategory.quotient _ _).obj Q) := by
  rw [tensorator_Q_generic]
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫ _ ≫ 𝟙 _ = _
  simp only [id_tensorHom_id, Category.id_comp, Category.comp_id]

private theorem cochain_tensor_comparison
    {C₁ C₂ : Type*} [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    [Abelian C₁] [Abelian C₂]
    [IsGrothendieckAbelian.{u + 1} C₁] [IsGrothendieckAbelian.{u + 1} C₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalPreadditive C₁] [MonoidalPreadditive C₂]
    [MonoidalClosed C₁] [MonoidalClosed C₂] [BraidedCategory C₁] [BraidedCategory C₂]
    [Abelian.HasFunctorialFlatResolution C₁] [Abelian.HasFunctorialFlatResolution C₂]
    (G : C₁ ⥤ C₂) [G.Additive] [G.PreservesKFlatQuasiIso]
    [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]
    (P Q : CochainComplex C₁ ℤ) :
    ((G.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q)) ≫
      (G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P) ⊗ₘ
        G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj Q)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
    G.leftDerivedFunctor.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj (P ⊗ Q)) ≫
      DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app P).app Q) := by
  erw [tensorator_Q_strict ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q),
    tensorator_Q_strict P Q]
  let δ := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app P).app Q
  have hδ := DerivedCategory.quotientCompQhIso_hom_naturality δ
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map δ) ≫ 𝟙 _ =
    𝟙 _ ≫ DerivedCategory.Q.map δ at hδ
  simp only [Category.comp_id, Category.id_comp] at hδ
  have h := G.leftDerivedTensorComparison_app_app_comp_tensorHom
    ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj Q)
  rw [Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app] at h
  rw [hδ] at h
  exact h

private def cochainCompute
    {C₁ C₂ : Type*} [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    [Abelian C₁] [Abelian C₂]
    [IsGrothendieckAbelian.{u + 1} C₁] [IsGrothendieckAbelian.{u + 1} C₂]
    [MonoidalCategory C₁] [MonoidalPreadditive C₁] [MonoidalClosed C₁]
    [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
    (G : C₁ ⥤ C₂) [G.Additive] [G.PreservesKFlatQuasiIso]
    (P : CochainComplex C₁ ℤ) :
    G.leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P) :=
  G.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C₁).inv.app P) ≫
    G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso C₂).hom.app
      ((G.mapHomologicalComplex (.up ℤ)).obj P)

attribute [local irreducible] cochainCompute

private theorem cochainCompute_eq
    {C₁ C₂ : Type*} [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    [Abelian C₁] [Abelian C₂]
    [IsGrothendieckAbelian.{u + 1} C₁] [IsGrothendieckAbelian.{u + 1} C₂]
    [MonoidalCategory C₁] [MonoidalPreadditive C₁] [MonoidalClosed C₁]
    [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
    (G : C₁ ⥤ C₂) [G.Additive] [G.PreservesKFlatQuasiIso]
    (P : CochainComplex C₁ ℤ) :
    cochainCompute.{u} G P =
      G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P) := by
  unfold cochainCompute
  change G.leftDerivedFunctor.map (𝟙 _) ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  rw [G.leftDerivedFunctor.map_id, DerivedCategory.Qh.map_id]
  simp only [Category.id_comp, Category.comp_id]

private theorem cochainCompute_tensor_comparison
    {C₁ C₂ : Type*} [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    [Abelian C₁] [Abelian C₂]
    [IsGrothendieckAbelian.{u + 1} C₁] [IsGrothendieckAbelian.{u + 1} C₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalPreadditive C₁] [MonoidalPreadditive C₂]
    [MonoidalClosed C₁] [MonoidalClosed C₂] [BraidedCategory C₁] [BraidedCategory C₂]
    [Abelian.HasFunctorialFlatResolution C₁] [Abelian.HasFunctorialFlatResolution C₂]
    (G : C₁ ⥤ C₂) [G.Additive] [G.PreservesKFlatQuasiIso]
    [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]
    (P Q : CochainComplex C₁ ℤ) :
    ((G.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q)) ≫
      (cochainCompute.{u} G P ⊗ₘ cochainCompute.{u} G Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
    G.leftDerivedFunctor.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      cochainCompute.{u} G (P ⊗ Q) ≫ DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app P).app Q) := by
  have h := cochain_tensor_comparison.{u} G P Q
  have ht : cochainCompute.{u} G P ⊗ₘ cochainCompute.{u} G Q =
      G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P) ⊗ₘ
        G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj Q) :=
    congrArg₂ (fun p q ↦ p ⊗ₘ q) (cochainCompute_eq.{u} G P) (cochainCompute_eq.{u} G Q)
  have hr := cochainCompute_eq.{u} G (P ⊗ Q)
  convert h using 1
  · congr 2
  · congr 1
    congr 1 <;> assumption

private theorem canonicalScalarTensorIso_normalized (n : ℕ) (T : Scheme.{u}) :
    ScalarTensorNormalized l E n T (canonicalScalarTensorIso l E n T) := by
  unfold ScalarTensorNormalized
  intro P Q
  let m := CondensedRing.internalScalarMonoidal (reduction l E n) T
  let h := cochainCompute_tensor_comparison.{u} (extension (reduction l E n) T) P Q
  unfold cochainCompute at h
  unfold canonicalScalarTensorIso compute scalarCounit D scalarTensorTotal
  dsimp only [_root_.id, asIso_hom]
  convert h using 1 <;> rfl

end GenericComputations

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

private def uncurryTensorIso
    {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    (G : C₁ ⥤ C₂) (T₁ : C₁ ⥤ C₁ ⥤ C₁) (T₂ : C₂ ⥤ C₂ ⥤ C₂)
    (b : (Functor.postcompose₂.obj G).obj T₁ ≅
      (((Functor.whiskeringLeft₂ _).obj G).obj G).obj T₂) :
    Functor.uncurry.obj T₁ ⋙ G ≅ (G.prod G) ⋙ Functor.uncurry.obj T₂ :=
  NatIso.ofComponents (fun Z ↦ (b.app Z.1).app Z.2) (by
    rintro ⟨U, V⟩ ⟨U', V'⟩ ⟨g, h⟩
    have h₁ := NatTrans.congr_app (b.hom.naturality g) V
    have h₂ := (b.hom.app U').naturality h
    dsimp at h₁ h₂ ⊢
    rw [Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁])

private theorem fiber_unique {I : Type*} {A : I → Type*}
    (P : ∀ i, A i → Prop) (h : ∃! f : ∀ i, A i, ∀ i, P i (f i))
    (i : I) (x y : A i) (hx : P i x) (hy : P i y) : x = y := by
  classical
  obtain ⟨f, hf, hu⟩ := h
  have he (z : A i) (hz : P i z) : z = f i := by
    have hg : ∀ j, P j (Function.update f i z j) := by
      intro j
      by_cases hj : j = i
      · subst j
        simpa only [Function.update_self] using hz
      · simpa only [Function.update_of_ne hj] using hf j
    have := congrFun (hu (Function.update f i z) hg) i
    simpa only [Function.update_self] using this
  exact (he x hx).trans (he y hy).symm

private theorem uncurry_normalized (n : ℕ) (T : Scheme.{u})
    (b : ScalarTensorIso l E n T) (hb : ScalarTensorNormalized l E n T b) :
    QuotientSectionTensor.TensorNormalized (reduction l E n) T
      (uncurryTensorIso (D (reduction l E n) T)
        (CondensedRing.derivedTensor (integral l E) T)
        (CondensedRing.derivedTensor (finite l E n) T) b) := by
  unfold ScalarTensorNormalized at hb
  intro P Q _ _ _ _
  simp only [uncurryTensorIso, NatIso.ofComponents_hom_app, Iso.app_hom,
    scalarTensorTotal, QuotientSectionTensor.totalScalar,
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app] at hb ⊢
  convert hb P Q using 1

private theorem scalarTensor_unique (n : ℕ) (T : Scheme.{u})
    (b : ScalarTensorIso l E n T) (hb : ScalarTensorNormalized l E n T b) :
    b = canonicalScalarTensorIso l E n T := by
  let : ∀ U : Scheme.{u}, IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules (integral l E) U) :=
    fun U ↦ IsGrothendieckAbelian.of_equivalence
      (ModuleRingedComparison.equivalence (integral l E) U)
  let : ∀ U : Scheme.{u}, IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules (finite l E n) U) :=
    fun U ↦ IsGrothendieckAbelian.of_equivalence
      (ModuleRingedComparison.equivalence (finite l E n) U)
  let : ∀ U : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules (integral l E) U) :=
    fun _ ↦ HasDerivedCategory.ofIsGrothendieckAbelian _
  let : ∀ U : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules (finite l E n) U) :=
    fun _ ↦ HasDerivedCategory.ofIsGrothendieckAbelian _
  have hu := (QuotientSectionTensor.quotient_section_tensor_normalization l E n).1
  have he := fiber_unique _ hu T
    (uncurryTensorIso (D (reduction l E n) T)
      (CondensedRing.derivedTensor (integral l E) T)
      (CondensedRing.derivedTensor (finite l E n) T) b)
    (uncurryTensorIso (D (reduction l E n) T)
      (CondensedRing.derivedTensor (integral l E) T)
      (CondensedRing.derivedTensor (finite l E n) T) (canonicalScalarTensorIso l E n T))
    (uncurry_normalized l E n T b hb)
    (uncurry_normalized l E n T _ (canonicalScalarTensorIso_normalized l E n T))
  apply Iso.ext
  ext U V
  exact congrArg (fun e ↦ e.hom.app (U, V)) he

/-- The canonical scalar tensor isomorphism exists and is uniquely determined by
its balancing normalization, without flatness of the quotient ring over the integers. -/
theorem scalarTensorIso_existsUnique (n : ℕ) (T : Scheme.{u}) :
    ∃! b : ScalarTensorIso l E n T, ScalarTensorNormalized l E n T b := by
  refine ⟨canonicalScalarTensorIso l E n T, canonicalScalarTensorIso_normalized l E n T, ?_⟩
  intro b hb
  exact scalarTensor_unique l E n T b hb

/-- The uniquely normalized scalar tensor balancing isomorphism. The existence
statement determines the whole natural isomorphism, rather than an arbitrary map. -/
@[irreducible] def scalarTensorIso (n : ℕ) (T : Scheme.{u}) :
    ScalarTensorIso l E n T :=
  (scalarTensorIso_existsUnique l E n T).exists.choose

/-- The existing pullback tensor comparison with its named pullback functor. -/
@[irreducible] def actualTensorPull
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.postcompose₂.obj (L Λ f)).obj (CondensedRing.derivedTensor Λ Y) ⟶
      (((Functor.whiskeringLeft₂ _).obj (L Λ f)).obj (L Λ f)).obj
        (CondensedRing.derivedTensor Λ X) := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarTensor Λ f

/-- The actual projection bifunctor transformation, using the existing adjunction
and its actual tensor comparison. This is the recorded moduleObjectProjectionMap
before evaluating its two components, with only its functor names made explicit. -/
@[irreducible] def actualProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    F Λ f ⋙ CondensedRing.derivedTensor Λ Y ⟶
      (Functor.postcompose₂.obj (F Λ f)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 (DerivedCategory (Modules Λ X)))).obj
          (L Λ f)).obj (CondensedRing.derivedTensor Λ X)) :=
  (adj Λ f).rightAdjointProjectionMap (actualTensorPull Λ f)

/-- The displayed projection comparison equation, with the coefficient parameters
shared explicitly. This is an equality of actual arrows in the quotient module
category; it neither forgets the scalar action nor asserts only cohomological equality. -/
@[irreducible] def ProjectionComparisonEquation
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : D a Y ⋙ L S f ≅ L R f ⋙ D a X)
    (bX : (Functor.postcompose₂.obj (D a X)).obj (CondensedRing.derivedTensor R X) ≅
      (((Functor.whiskeringLeft₂ _).obj (D a X)).obj (D a X)).obj
        (CondensedRing.derivedTensor S X))
    (bY : (Functor.postcompose₂.obj (D a Y)).obj (CondensedRing.derivedTensor R Y) ≅
      (((Functor.whiskeringLeft₂ _).obj (D a Y)).obj (D a Y)).obj
        (CondensedRing.derivedTensor S Y))
    (K : DerivedCategory (Modules R X)) (M : DerivedCategory (Modules R Y)) : Prop :=
  (bY.hom.app ((F R f).obj K)).app M ≫
      ((CondensedRing.derivedTensor S Y).map ((rho a f c).app K)).app ((D a Y).obj M) ≫
      ((actualProjection S f).app ((D a X).obj K)).app ((D a Y).obj M) =
    (D a Y).map (((actualProjection R f).app K).app M) ≫
      (rho a f c).app (((CondensedRing.derivedTensor R X).obj K).obj ((L R f).obj M)) ≫
      (F S f).map
        ((bX.hom.app K).app ((L R f).obj M) ≫
          ((CondensedRing.derivedTensor S X).obj ((D a X).obj K)).map (c.inv.app M))

private theorem actualTensorPull_eq_quotientTensorPull
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    actualTensorPull B f = quotientTensorPull B f := by
  unfold actualTensorPull quotientTensorPull
  rfl

@[irreducible] private def uncurriedScalarTensor (n : ℕ) (T : Scheme.{u})
    (b : ScalarTensorIso l E n T) :
    QuotientSectionTensor.TensorIso (reduction l E n) T :=
  uncurryTensorIso (D (reduction l E n) T)
    (CondensedRing.derivedTensor (integral l E) T)
    (CondensedRing.derivedTensor (finite l E n) T) b

private theorem uncurriedScalarTensor_normalized (n : ℕ) (T : Scheme.{u}) :
    QuotientSectionTensor.TensorNormalized (reduction l E n) T
      (uncurriedScalarTensor l E n T (scalarTensorIso l E n T)) := by
  unfold uncurriedScalarTensor
  apply uncurry_normalized
  unfold scalarTensorIso
  exact (scalarTensorIso_existsUnique l E n T).exists.choose_spec

private theorem compatible_of_tensor_equation
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄]
    {F₁ : C₁ ⥤ C₂} {F₂ : C₃ ⥤ C₄} {N₁ : C₁ ⥤ C₃} {N₂ : C₂ ⥤ C₄}
    {T₁ : C₁ ⥤ C₁ ⥤ C₁} {T₂ : C₂ ⥤ C₂ ⥤ C₂}
    {T₃ : C₃ ⥤ C₃ ⥤ C₃} {T₄ : C₄ ⥤ C₄ ⥤ C₄}
    (c : N₁ ⋙ F₂ ≅ F₁ ⋙ N₂)
    (p₁ : (Functor.postcompose₂.obj F₁).obj T₁ ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₁).obj T₂)
    (p₂ : (Functor.postcompose₂.obj F₂).obj T₃ ⟶
      (((Functor.whiskeringLeft₂ _).obj F₂).obj F₂).obj T₄)
    (b₁ : (Functor.postcompose₂.obj N₁).obj T₁ ≅
      (((Functor.whiskeringLeft₂ _).obj N₁).obj N₁).obj T₃)
    (b₂ : (Functor.postcompose₂.obj N₂).obj T₂ ≅
      (((Functor.whiskeringLeft₂ _).obj N₂).obj N₂).obj T₄)
    (h : ∀ U V, c.hom.app ((T₁.obj U).obj V) ≫
        N₂.map ((p₁.app U).app V) ≫ (b₂.hom.app (F₁.obj U)).app (F₁.obj V) =
      F₂.map ((b₁.hom.app U).app V) ≫ (p₂.app (N₁.obj U)).app (N₁.obj V) ≫
        (T₄.map (c.hom.app U)).app _ ≫ (T₄.obj _).map (c.hom.app V)) :
    Adjunction.ComparisonCompatible c p₁ p₂ b₂ b₁ := by
  intro U V
  apply (cancel_epi (c.hom.app ((T₁.obj U).obj V))).1
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using h U V

private theorem compatible_of_tensorHom_equation
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄]
    {F₁ : C₁ ⥤ C₂} {F₂ : C₃ ⥤ C₄} {N₁ : C₁ ⥤ C₃} {N₂ : C₂ ⥤ C₄}
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalCategory C₃] [MonoidalCategory C₄]
    (c : N₁ ⋙ F₂ ≅ F₁ ⋙ N₂)
    (p₁ : (Functor.postcompose₂.obj F₁).obj (curriedTensor C₁) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₁).obj (curriedTensor C₂))
    (p₂ : (Functor.postcompose₂.obj F₂).obj (curriedTensor C₃) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₂).obj F₂).obj (curriedTensor C₄))
    (b₁ : (Functor.postcompose₂.obj N₁).obj (curriedTensor C₁) ≅
      (((Functor.whiskeringLeft₂ _).obj N₁).obj N₁).obj (curriedTensor C₃))
    (b₂ : (Functor.postcompose₂.obj N₂).obj (curriedTensor C₂) ≅
      (((Functor.whiskeringLeft₂ _).obj N₂).obj N₂).obj (curriedTensor C₄))
    (h : ∀ U V, c.hom.app (U ⊗ V) ≫
        N₂.map ((p₁.app U).app V) ≫ (b₂.hom.app (F₁.obj U)).app (F₁.obj V) =
      F₂.map ((b₁.hom.app U).app V) ≫ (p₂.app (N₁.obj U)).app (N₁.obj V) ≫
        (c.hom.app U ⊗ₘ c.hom.app V)) :
    Adjunction.ComparisonCompatible c p₁ p₂ b₂ b₁ := by
  apply compatible_of_tensor_equation
  intro U V
  simpa only [curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    MonoidalCategory.tensorHom_def, Category.assoc] using h U V

private theorem actual_tensor_compatible
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (c : D (reduction l E n) Y ⋙ L (finite l E n) f ≅
      L (integral l E) f ⋙ D (reduction l E n) X)
    (hc : PullNormalized (reduction l E n) f c) :
    Adjunction.ComparisonCompatible c
      (actualTensorPull (integral l E) f) (actualTensorPull (finite l E n) f)
      (scalarTensorIso l E n X) (scalarTensorIso l E n Y) := by
  let : ∀ T : Scheme.{u}, IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules (integral l E) T) :=
    fun T ↦ IsGrothendieckAbelian.of_equivalence
      (ModuleRingedComparison.equivalence (integral l E) T)
  let : ∀ T : Scheme.{u}, IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules (finite l E n) T) :=
    fun T ↦ IsGrothendieckAbelian.of_equivalence
      (ModuleRingedComparison.equivalence (finite l E n) T)
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules (integral l E) T) :=
    fun _ ↦ HasDerivedCategory.ofIsGrothendieckAbelian _
  let : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules (finite l E n) T) :=
    fun _ ↦ HasDerivedCategory.ofIsGrothendieckAbelian _
  let b := fun T ↦ uncurriedScalarTensor l E n T (scalarTensorIso l E n T)
  have hc := (quotient_pullback_tensor_coherence l E n b
    (uncurriedScalarTensor_normalized l E n) f c hc).2.2
  have hh : Adjunction.ComparisonCompatible c
      (quotientTensorPull (integral l E) f) (quotientTensorPull (finite l E n) f)
      (scalarTensorIso l E n X) (scalarTensorIso l E n Y) := by
    apply compatible_of_tensorHom_equation
    intro U V
    simpa only [b, uncurriedScalarTensor, uncurryTensorIso, NatIso.ofComponents_hom_app,
      Iso.app_hom] using hc U V
  simpa only [actualTensorPull_eq_quotientTensorPull] using hh

private theorem projectionComparison_of_compatible
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : D a Y ⋙ L S f ≅ L R f ⋙ D a X)
    (bX : (Functor.postcompose₂.obj (D a X)).obj (CondensedRing.derivedTensor R X) ≅
      (((Functor.whiskeringLeft₂ _).obj (D a X)).obj (D a X)).obj
        (CondensedRing.derivedTensor S X))
    (bY : (Functor.postcompose₂.obj (D a Y)).obj (CondensedRing.derivedTensor R Y) ≅
      (((Functor.whiskeringLeft₂ _).obj (D a Y)).obj (D a Y)).obj
        (CondensedRing.derivedTensor S Y))
    (h : Adjunction.ComparisonCompatible c (actualTensorPull R f) (actualTensorPull S f)
      bX bY)
    (K : DerivedCategory (Modules R X)) (M : DerivedCategory (Modules R Y)) :
    ProjectionComparisonEquation a f c bX bY K M := by
  unfold ProjectionComparisonEquation actualProjection rho
  exact (Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv
    (adj R f) (adj S f) h K M).symm

/-- Reduction of the actual integral projection morphism is the actual quotient
projection morphism under the specified scalar tensor, pullback and direct-image
comparisons. The pullback comparison is fixed by exactly the normalization in the
direct-image dependency; that dependency supplies its existence. Both sides are
natural in K and M and are arrows in the quotient-coefficient derived category. -/
theorem integral_quotient_projection_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (c : D (reduction l E n) Y ⋙ L (finite l E n) f ≅
      L (integral l E) f ⋙ D (reduction l E n) X)
    (_hc : PullNormalized (reduction l E n) f c)
    (K : DerivedCategory (Modules (integral l E) X))
    (M : DerivedCategory (Modules (integral l E) Y)) :
    ProjectionComparisonEquation (reduction l E n) f c
      (scalarTensorIso l E n X) (scalarTensorIso l E n Y) K M := by
  exact projectionComparison_of_compatible (reduction l E n) f c
    (scalarTensorIso l E n X) (scalarTensorIso l E n Y)
    (actual_tensor_compatible l E f n c _hc) K M

end AlgebraicGeometry.ProEtale.IntegralQuotient
