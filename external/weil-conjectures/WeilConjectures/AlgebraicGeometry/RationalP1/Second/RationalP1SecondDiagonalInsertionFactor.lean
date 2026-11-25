/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullSection
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1ProjectionNaturality
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveSupportedSectionProjection

/-! # Factoring the second diagonal insertion before any trace
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] projectionMap

private theorem insert_class
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (R : D ⥤ C) (M : C) {A B V S T Z H : D}
    (s : V ≅ S) (d : Z ≅ A ⊗ V) (t : B ⟶ A) (r : B ⊗ V ⟶ Z)
    (a : 𝟙_ C ⟶ R.obj S) (b : 𝟙_ C ⟶ R.obj T)
    (f : S ⟶ T) (z : A ⊗ T ⟶ H)
    (πS : M ⊗ R.obj S ⟶ R.obj (B ⊗ S))
    (πT : M ⊗ R.obj T ⟶ R.obj (B ⊗ T))
    (σ : M ⟶ R.obj Z)
    (hc : tensorHom t (𝟙 V) ≫ d.inv = r)
    (hs : (ρ_ M).inv ≫ (M ◁ a) ≫ πS ≫ R.map ((B ◁ s.inv) ≫ r) = σ)
    (hn : (M ◁ R.map f) ≫ πT = πS ≫ R.map (B ◁ f))
    (ha : a ≫ R.map f = b) :
    σ ≫ R.map (d.hom ≫ (A ◁ (s.hom ≫ f)) ≫ z) =
      (ρ_ M).inv ≫ (M ◁ b) ≫ πT ≫ R.map (tensorHom t (𝟙 T) ≫ z) := by
  have hi : ((B ◁ s.inv) ≫ r) ≫ (d.hom ≫ (A ◁ (s.hom ≫ f)) ≫ z) =
      (B ◁ f) ≫ tensorHom t (𝟙 T) ≫ z := by
    rw [← hc]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [← hs]
  simp only [Category.assoc]
  rw [← R.map_comp, hi, R.map_comp, R.map_comp, ← reassoc_of% hn]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ha]

private theorem compose_three_squares
    {C : Type*} [Category C] {A A' B B' E E' D D' : C}
    {a : A ⟶ A'} {b : B ⟶ B'} {c : E ⟶ E'} {d : D ⟶ D'}
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : B ⟶ E} {g' : B' ⟶ E'}
    {h : E ⟶ D} {h' : E' ⟶ D'}
    (h₁ : a ≫ f' = f ≫ b) (h₂ : b ≫ g' = g ≫ c)
    (h₃ : c ≫ h' = h ≫ d) :
    a ≫ (f' ≫ g' ≫ h') = (f ≫ g ≫ h) ≫ d := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

private theorem map_square
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A A' B B' : C} {a : A ⟶ A'} {b : B ⟶ B'}
    {f : A ⟶ B} {f' : A' ⟶ B'} (h : a ≫ f' = f ≫ b) :
    R.map a ≫ R.map f' = R.map f ≫ R.map b := by
  rw [← R.map_comp, h, R.map_comp]

private theorem replace_square
    {C : Type*} [Category C] {A B D E : C}
    {a : A ⟶ B} {b : D ⟶ E} {f F : B ⟶ E} {g G : A ⟶ D}
    (hf : f = F) (hg : g = G) (h : a ≫ F = G ≫ b) : a ≫ f = g ≫ b := by
  rw [hf, hg]
  exact h

section NativeBraiding
universe v w
variable {C : Type v} [Category.{w} C] [Abelian C]
  [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

local instance instHasColimitsOfSize_rationalP1SecondDiagonalInsertionFactor
    : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

private theorem native_braiding_naturality_right
    (A : DerivedCategory C) {B B' : DerivedCategory C} (b : B ⟶ B') :
    (A ◁ b) ≫ (traceDerivedBraiding A B').hom =
      (traceDerivedBraiding A B).hom ≫ (b ▷ A) := by
  unfold traceDerivedBraiding
  exact DerivedMonoidal.braiding_naturality_right (DerivedCategory.Qh (C := C))
      (HomotopyCategory.quasiIso C (.up ℤ)) A b

private theorem native_braiding_naturality_left
    {A A' : DerivedCategory C} (a : A ⟶ A') (B : DerivedCategory C) :
    (a ▷ B) ≫ (traceDerivedBraiding A' B).hom =
      (traceDerivedBraiding A B).hom ≫ (B ◁ a) := by
  unfold traceDerivedBraiding
  exact DerivedMonoidal.braiding_naturality_left (DerivedCategory.Qh (C := C))
      (HomotopyCategory.quasiIso C (.up ℤ)) a B
end NativeBraiding

section NativeProjection
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
-- These wrappers present the same sheaf braiding to the module tensor instances.
attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory

attribute [local instance 3000] projectionDerivedMonoidal
attribute [local instance 4000] projectionModuleAbelian projectionModuleMonoidal
  projectionModuleHasDerived
attribute [local instance 5000] projectionSheafMonoidal projectionCoefficientMonObj
  projectionModuleCategory

@[instance_reducible]
private def native_sheaf_symmetric (Z : Scheme.{u}) :
    SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
  { sheafSymmetricCategory Z with toBraidedCategory := sheafBraidedCategory Ab Z }
attribute [local instance 20001] native_sheaf_symmetric

-- The native braidings compare the fixed module-site instances.
attribute [-instance] internalMonoidal in
private theorem trace_projection_naturality_right
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (g : X ⟶ S)
    (K : DerivedCategory (Modules Λ S))
    {N N' : DerivedCategory (Modules Λ X)} (n : N ⟶ N') :
    (K ◁ (moduleObjectDerivedPushforward Λ g).map n) ≫ traceProjection Λ g K N' =
      traceProjection Λ g K N ≫
        (moduleObjectDerivedPushforward Λ g).map
          (((moduleObjectDerivedPullback Λ g).obj K) ◁ n) := by
  have hbS : (K ◁ (moduleObjectDerivedPushforward Λ g).map n) ≫
      (traceBraiding Λ S K ((moduleObjectDerivedPushforward Λ g).obj N')).hom =
      (traceBraiding Λ S K ((moduleObjectDerivedPushforward Λ g).obj N)).hom ≫
        ((moduleObjectDerivedPushforward Λ g).map n ▷ K) := by
    unfold traceBraiding
    exact native_braiding_naturality_right K
        ((moduleObjectDerivedPushforward Λ g).map n)
  have hbX : (n ▷ ((moduleObjectDerivedPullback Λ g).obj K)) ≫
      (traceBraiding Λ X N' ((moduleObjectDerivedPullback Λ g).obj K)).hom =
      (traceBraiding Λ X N ((moduleObjectDerivedPullback Λ g).obj K)).hom ≫
        (((moduleObjectDerivedPullback Λ g).obj K) ◁ n) := by
    unfold traceBraiding
    exact native_braiding_naturality_left n ((moduleObjectDerivedPullback Λ g).obj K)
  have hm := NatTrans.congr_app
    (((CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).rightAdjointProjectionMap
      (moduleObjectDerivedTensorComparison Λ g)).naturality n) K
  change ((moduleObjectDerivedPushforward Λ g).map n ▷ K) ≫
      moduleObjectProjectionMate Λ g N' K =
    moduleObjectProjectionMate Λ g N K ≫
      (moduleObjectDerivedPushforward Λ g).map
        (n ▷ ((moduleObjectDerivedPullback Λ g).obj K)) at hm
  unfold traceProjection tracePush tracePull
  exact compose_three_squares hbS hm
    (map_square (moduleObjectDerivedPushforward Λ g) hbX)
end NativeProjection

private theorem normalized_projection_naturality_right
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (a : ProjectionFamily Λ) (ha : ProjectionNormalized Λ a) :
    ∀ {X S : Scheme.{u}} (g : X ⟶ S) (K : DerivedCategory (Modules Λ S))
      {N N' : DerivedCategory (Modules Λ X)} (n : N ⟶ N'),
      (K ◁ (moduleObjectDerivedPushforward Λ g).map n) ≫ a g K N' =
        a g K N ≫ (moduleObjectDerivedPushforward Λ g).map
          (((moduleObjectDerivedPullback Λ g).obj K) ◁ n) := by
  unfold ProjectionFamily ProjectionNormalized internalMonoidal internalTensorBundle
    nativeTensorBundle at *
  intro X S g K N N' n
  exact replace_square (eq_of_heq (ha g K N')) (eq_of_heq (ha g K N))
    (trace_projection_naturality_right Λ g K n)

private theorem projection_naturality_right
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (g : X ⟶ S)
    (K : DerivedCategory (Modules Λ S))
    {N N' : DerivedCategory (Modules Λ X)} (n : N ⟶ N') :
    (K ◁ (moduleObjectDerivedPushforward Λ g).map n) ≫ projectionMap Λ g K N' =
      projectionMap Λ g K N ≫
        (moduleObjectDerivedPushforward Λ g).map
          (((moduleObjectDerivedPullback Λ g).obj K) ◁ n) := by
  unfold projectionMap
  exact normalized_projection_naturality_right Λ
    (projection_existsUnique Λ).exists.choose
    (projection_existsUnique Λ).exists.choose_spec g K n

attribute [local instance] internalMonoidal

attribute [local irreducible] unitComponent counitComponent twistProjectionMap
attribute [local irreducible] coefficient line diagram secondLineComparison
attribute [local irreducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] twist singleUnitIso
attribute [local irreducible] condensedAmbientExchange

private theorem section_tensor_change
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}}
    (g : X ⟶ S) (p₁ p₂ : S ⟶ X)
    (s₁ : moduleObjectDerivedPullback Λ p₁ ⋙ moduleObjectDerivedPullback Λ g ≅
      𝟭 (DerivedCategory (Modules Λ X)))
    (s₂ : moduleObjectDerivedPullback Λ p₂ ⋙ moduleObjectDerivedPullback Λ g ≅
      𝟭 (DerivedCategory (Modules Λ X)))
    (U : DerivedCategory (Modules Λ X))
    (e : U ≅ 𝟙_ (DerivedCategory (Modules Λ X)))
    (M : DerivedCategory (Modules Λ X))
    (t : (moduleObjectDerivedPullback Λ p₂).obj M ⟶
      (moduleObjectDerivedPullback Λ p₁).obj M)
    (ht : (moduleObjectDerivedPullback Λ g).map t ≫ s₁.hom.app M = s₂.hom.app M) :
    tensorHom t (𝟙 ((moduleObjectDerivedPushforward Λ g).obj U)) ≫
        sectionTensorMap Λ g p₁ s₁ U e M = sectionTensorMap Λ g p₂ s₂ U e M := by
  unfold sectionTensorMap
  rw [reassoc_of% (projectionMap_naturality Λ g t U)]
  rw [← Functor.map_comp]
  congr 2
  rw [tensorHom_comp_tensorHom_assoc, Category.id_comp, ht]

attribute [local implicit_reducible] firstProjection in
private theorem diagonal_tensor_inverse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (diagonalTensorIso Λ Y M).inv =
      sectionTensorMap Λ (diagonalImmersion Y) (firstProjection Y)
        (pullSectionIso Λ Y (firstProjection Y)
          (by unfold firstProjection; exact pullback.diagonal_fst _))
        (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M := by
  simp only [diagonalTensorIso, Iso.symm_inv, asIso_hom, diagonalTensorMap]

attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] supportedUnitIso pushSectionIso
attribute [local irreducible] tensorShiftIso diagonalClassMap

-- Keep the fixed derived tensor interfaces folded in the categorical calculation.
private theorem diagonal_insertion_from_section
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (t : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj M ⟶
      (moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)
    (ht : PullSectionCompatibility
      (moduleObjectDerivedPullback Λ (firstProjection Y))
      (moduleObjectDerivedPullback Λ (secondProjection Y))
      (moduleObjectDerivedPullback Λ (diagonalImmersion Y))
      (pullSectionIso Λ Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _))
      (pullSectionIso Λ Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _)) M t) :
    (pushSectionIso Λ Y).hom.app M ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (diagonalClassMap Λ Y L d M) =
    (ρ_ M).inv ≫
      (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
        d.support₂.hom ≫ d.R₂.R.map d.delta ≫
        (secondDiagramPushIso Λ Y L d).hom.app
          (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧))) ≫
      projectionMap Λ (secondProjection Y) M
        (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (tensorHom t (𝟙 _) ≫
          (tensorShiftIso Λ (diagonalSurface Y) (L (diagonalSurface Y))
            ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)).hom) := by
  let R := moduleObjectDerivedPushforward Λ (secondProjection Y)
  let A := (moduleObjectDerivedPullback Λ (firstProjection Y)).obj M
  let V := (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
    (unit Λ (ProjectiveLine Y))
  let S := (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
    (source Λ Y)
  let T := ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
    (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧
  let r := sectionTensorMap Λ (diagonalImmersion Y) (secondProjection Y)
    (pullSectionIso Λ Y (secondProjection Y)
      (by unfold secondProjection; exact pullback.diagonal_snd _))
    (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M
  let a := (singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₂.hom ≫
    (secondDiagramPushIso Λ Y L d).hom.app S
  let b := (singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₂.hom ≫
    d.R₂.R.map d.delta ≫ (secondDiagramPushIso Λ Y L d).hom.app T
  have hc₀ := section_tensor_change Λ (diagonalImmersion Y)
    (firstProjection Y) (secondProjection Y)
    (pullSectionIso Λ Y (firstProjection Y)
      (by unfold firstProjection; exact pullback.diagonal_fst _))
    (pullSectionIso Λ Y (secondProjection Y)
      (by unfold secondProjection; exact pullback.diagonal_snd _))
    (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M
    t ht.comm
  have hc := (congrArg (fun f ↦
    tensorHom t (𝟙 V) ≫ f)
      (diagonal_tensor_inverse Λ Y M)).trans hc₀
  have hs := supported_section_projection Λ Y L d M
  have hn := projection_naturality_right Λ (secondProjection Y) M d.delta
  have ha : a ≫ R.map d.delta = b := by
    dsimp only [a, b]
    simp only [Category.assoc]
    rw [← (secondDiagramPushIso Λ Y L d).hom.naturality d.delta]
  have h := insert_class R M (supportedUnitIso Λ Y) (diagonalTensorIso Λ Y M)
    t r a b d.delta
    (tensorShiftIso Λ (diagonalSurface Y) (L (diagonalSurface Y)) A).hom
    (projectionMap Λ (secondProjection Y) M S)
    (projectionMap Λ (secondProjection Y) M T)
    ((pushSectionIso Λ Y).hom.app M) hc hs hn ha
  simpa only [b, diagonalClassMap,
    MonoidalCategory.whiskerLeft_comp, Functor.map_comp, Category.assoc] using h

-- The statement compares several fixed derived pullback and tensor interfaces.
/-- The section/projection factorization of the insertion, before applying any trace.
No trace, counit, exchange inverse, projection inverse, localizing hypothesis or completed
reference occurs in this equation. The diagram is used only for its class, full derived
unit, and supported-source normalization. -/
theorem second_diagonal_insertion_factor
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (d : Diagram (coefficient l c).X Y (line l c))
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    (pushSectionIso (coefficient l c).X Y).hom.app
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
        (diagonalClassMap (coefficient l c).X Y (line l c) d
          ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))) =
    (ρ_ ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))).inv ≫
      (((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)) ◁
        ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫
          d.support₂.hom ≫ d.R₂.R.map d.delta ≫
          (secondDiagramPushIso (coefficient l c).X Y (line l c) d).hom.app
            (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧))) ≫
      secondForwardProjection l c k p hpl Y K := by
  unfold secondForwardProjection
  exact diagonal_insertion_from_section (coefficient l c).X Y (line l c) d
    ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
    (secondPullComparison l c k p hpl Y K).inv (second_pull_section l c k p hpl Y K)

end AlgebraicGeometry.ProEtale.RationalP1
