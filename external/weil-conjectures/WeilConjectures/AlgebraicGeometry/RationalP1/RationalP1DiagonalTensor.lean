/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalComposition

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ProEtaleProjectionExchangeMaps
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

/-! # The canonical diagonal tensor comparison
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The actual canonical self-square. -/
def square (Y : Scheme.{u}) :
    ChosenCartesianSquare (firstProjection Y) (secondProjection Y)
      (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) where
  w := pullback.condition
  isoPullback := Iso.refl _
  hom_fst := Category.id_comp _
  hom_snd := Category.id_comp _

/-- The projection mate followed by a specified section and unit comparison.
Keeping this construction over arbitrary schemes prevents specialization from
unfolding the concrete projective-line site when checking its naturality. -/
@[irreducible]
def sectionTensorMap {X S : Scheme.{u}} (g : X ⟶ S) (p : S ⟶ X)
    (s : moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPullback Λ g ≅
      𝟭 (DerivedCategory (Modules Λ X)))
    (U : DerivedCategory (Modules Λ X)) (e : U ≅ 𝟙_ (DerivedCategory (Modules Λ X)))
    (M : DerivedCategory (Modules Λ X)) :
    (moduleObjectDerivedPullback Λ p).obj M ⊗
      (moduleObjectDerivedPushforward Λ g).obj U ⟶
        (moduleObjectDerivedPushforward Λ g).obj M :=
  projectionMap Λ g _ _ ≫ (moduleObjectDerivedPushforward Λ g).map
    (tensorHom (s.hom.app M) e.hom ≫ (ρ_ M).hom)

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The closed projection mate, followed by the section comparison and coefficient unitor. -/
@[irreducible]
def diagonalTensorMap (Y : Scheme.{u}) (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗
      (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
        (unit Λ (ProjectiveLine Y)) ⟶
      (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj M :=
  sectionTensorMap Λ (diagonalImmersion Y) (firstProjection Y)
    (pullSectionIso Λ Y (firstProjection Y) (pullback.diagonal_fst _))
    (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M

attribute [-instance] internalMonoidal in
private theorem closed_projection_isIso {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (N : DerivedCategory (Modules Λ Z)) (K : DerivedCategory (Modules Λ X)) :
    IsIso (moduleObjectProjectionMate Λ i N K) := by
  let := closedSupport_lowerStarExact Λ i j hij
  let eR := (CondensedRing.lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
  let eF := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ i ≪≫
    (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ i)).symm
  let ad := CondensedRing.derivedUpperStarLowerStarAdjunction Λ i
  have hc := (condensedSupportDerivedLocalization Λ i j hij).2.1
  have : IsIso (closedPullbackDerivedAdjunction Λ i).counit :=
    NatIso.isIso_of_isIso_app _
  let ff := ad.fullyFaithfulROfCompIsoId
    (Functor.isoWhiskerRight eR _ ≪≫ Functor.isoWhiskerLeft _ eF ≪≫
      asIso (closedPullbackDerivedAdjunction Λ i).counit)
  have := ff.full
  have := ff.faithful
  have hcounit : IsIso ad.counit := inferInstance
  dsimp only [ad] at hcounit
  have hp := (openClosedSupportProjectionFormula Λ i j hij).1 N K
  let T := ((CondensedRing.derivedTensor Λ Z).obj N).obj
    ((supportPullback Λ i).mapDerivedCategory.obj K)
  let e : (moduleObjectDerivedPushforward Λ i).obj N ⊗ K ≅
      (moduleObjectDerivedPushforward Λ i).obj T :=
    tensorIso (eR.app N) (Iso.refl K) ≪≫
      asIso (closedSupportProjection Λ i N K) ≪≫ (eR.app T).symm
  have hunit : IsIso (ad.unit.app ((moduleObjectDerivedPushforward Λ i).obj N ⊗ K)) :=
    ad.isIso_unit_app_iff_mem_essImage.2 ⟨T, ⟨e.symm⟩⟩
  dsimp only [ad, moduleObjectDerivedPushforward] at hunit
  have := (moduleObjectDerivedTensorComparison_normalized Λ i).2
  unfold moduleObjectProjectionMate
  rw [Adjunction.rightAdjointProjectionMap_app_app, Adjunction.homEquiv_unit]
  refine IsIso.comp_isIso' hunit ?_
  apply Functor.map_isIso

private theorem cartier_complement_affine {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : I.IsInvertible) : IsAffineHom (Scheme.Opens.ι I.support.compl) := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  obtain ⟨U, hx, r, _, hr⟩ := hI x
  refine ⟨U.1, hx, U.2, ?_⟩
  rw [← (Scheme.Opens.ι I.support.compl).isAffineOpen_iff_of_isOpenImmersion,
    Scheme.Hom.image_preimage_eq_opensRange_inf]
  have he : I.support.compl ⊓ U.1 = X.basicOpen r := by
    ext y
    change (y ∉ I.support ∧ y ∈ U.1) ↔ y ∈ X.basicOpen r
    constructor
    · rintro ⟨hy, hU⟩
      have hs := I.mem_support_iff_of_mem hU
      rw [hr, X.zeroLocus_span, X.zeroLocus_singleton] at hs
      exact Classical.not_not.mp ((not_congr hs).mp hy)
    · intro hy
      have hU := X.basicOpen_le r hy
      refine ⟨?_, hU⟩
      have hs := I.mem_support_iff_of_mem hU
      rw [hr, X.zeroLocus_span, X.zeroLocus_singleton] at hs
      exact fun hi ↦ hs.mp hi hy
  rw [Scheme.Opens.opensRange_ι, he]
  exact U.2.basicOpen r

private theorem normalized_projection_isIso
    (a : ProjectionFamily Λ) (ha : ProjectionNormalized Λ a)
    {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory (Modules Λ X)) (N : DerivedCategory (Modules Λ Z)) :
    IsIso (a i K N) := by
  unfold ProjectionNormalized ProjectionFamily internalMonoidal internalTensorBundle
    nativeTensorBundle at *
  have he : a i K N = traceProjection Λ i K N := eq_of_heq (ha i K N)
  rw [he]
  unfold traceProjection
  have := closed_projection_isIso Λ i j hij N K
  infer_instance

private theorem sectionTensorMap_isIso {Z U X : Scheme.{u}}
    (g : Z ⟶ X) (p : X ⟶ Z)
    (j : U ⟶ X) [IsClosedImmersion g] [IsOpenImmersion j] [QuasiCompact j]
    (hgj : Set.range g.base = (Set.range j.base)ᶜ)
    (s : moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPullback Λ g ≅
      𝟭 (DerivedCategory (Modules Λ Z)))
    (A : DerivedCategory (Modules Λ Z)) (e : A ≅ 𝟙_ (DerivedCategory (Modules Λ Z)))
    (M : DerivedCategory (Modules Λ Z)) :
    IsIso (sectionTensorMap Λ g p s A e M) := by
  have : IsIso (projectionMap Λ g ((moduleObjectDerivedPullback Λ p).obj M) A) :=
    normalized_projection_isIso Λ
      (projection_existsUnique Λ).exists.choose
      (projection_existsUnique Λ).exists.choose_spec g j hgj
      ((moduleObjectDerivedPullback Λ p).obj M) A
  unfold sectionTensorMap
  infer_instance

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The diagonal tensor map is invertible on every unbounded internal module. -/
theorem diagonalTensorMap_isIso (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    IsIso (diagonalTensorMap Λ Y M) := by
  let I := (diagonalImmersion Y).ker
  let V : (diagonalSurface Y).Opens := I.support.compl
  have hI : I.IsInvertible := Etale.projectiveLine_diagonal_ker_isInvertible Y
  have : IsAffineHom V.ι := cartier_complement_affine I hI
  have hij : Set.range (diagonalImmersion Y).base = (Set.range V.ι.base)ᶜ := by
    simp only [Scheme.Opens.range_ι, V, TopologicalSpace.Closeds.coe_compl,
      compl_compl, I, Scheme.Hom.support_ker,
      (diagonalImmersion Y).isClosedEmbedding.isClosed_range.closure_eq]
  unfold diagonalTensorMap
  exact sectionTensorMap_isIso Λ (diagonalImmersion Y) (firstProjection Y) V.ι hij
    (pullSectionIso Λ Y (firstProjection Y) (pullback.diagonal_fst _))
    (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The inverse of the canonical diagonal comparison. -/
@[irreducible]
def diagonalTensorIso (Y : Scheme.{u}) (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj M ≅
      (moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗
        (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
          (unit Λ (ProjectiveLine Y)) :=
  haveI := diagonalTensorMap_isIso Λ Y M
  (asIso (diagonalTensorMap Λ Y M)).symm

-- Elaborating the native braidings compares the fixed module-site instances.
attribute [-instance] internalMonoidal in
private theorem trace_projection_naturality {X S : Scheme.{u}} (g : X ⟶ S)
    {K K' : DerivedCategory (Modules Λ S)} (k : K ⟶ K')
    (N : DerivedCategory (Modules Λ X)) :
    tensorHom k (𝟙 _) ≫ traceProjection Λ g K' N =
      traceProjection Λ g K N ≫
        (moduleObjectDerivedPushforward Λ g).map
          (tensorHom ((moduleObjectDerivedPullback Λ g).map k) (𝟙 N)) := by
  have hbS : tensorHom k (𝟙 _) ≫ (traceBraiding Λ S K'
        ((moduleObjectDerivedPushforward Λ g).obj N)).hom =
      (traceBraiding Λ S K ((moduleObjectDerivedPushforward Λ g).obj N)).hom ≫
        tensorHom (𝟙 _) k := by
    simpa only [traceBraiding, traceDerivedBraiding, tensorHom_id, id_tensorHom] using
      DerivedMonoidal.braiding_naturality_left
        (DerivedCategory.Qh (C := Modules Λ S))
        (HomotopyCategory.quasiIso (Modules Λ S) (.up ℤ)) k
        ((moduleObjectDerivedPushforward Λ g).obj N)
  have hbX : tensorHom (𝟙 N) ((moduleObjectDerivedPullback Λ g).map k) ≫
        (traceBraiding Λ X N ((CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K')).hom =
      (traceBraiding Λ X N ((CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K)).hom ≫
        tensorHom ((moduleObjectDerivedPullback Λ g).map k) (𝟙 N) := by
    simpa only [traceBraiding, traceDerivedBraiding, tensorHom_id, id_tensorHom,
      moduleObjectDerivedPullback] using
      DerivedMonoidal.braiding_naturality_right
        (DerivedCategory.Qh (C := Modules Λ X))
        (HomotopyCategory.quasiIso (Modules Λ X) (.up ℤ)) N
        ((moduleObjectDerivedPullback Λ g).map k)
  have hm := (((CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).rightAdjointProjectionMap
    (moduleObjectDerivedTensorComparison Λ g)).app N).naturality k
  change (moduleObjectDerivedPushforward Λ g).obj N ◁ k ≫
      moduleObjectProjectionMate Λ g N K' =
    moduleObjectProjectionMate Λ g N K ≫
      (moduleObjectDerivedPushforward Λ g).map
        (N ◁ (moduleObjectDerivedPullback Λ g).map k) at hm
  simp only [← id_tensorHom] at hm
  dsimp only [traceProjection, tracePush, tracePull]
  simp only [Category.assoc]
  rw [reassoc_of% hbS, reassoc_of% hm, ← Functor.map_comp,
    hbX, Functor.map_comp]

private def ProjectionNatural (a : ProjectionFamily Λ) : Prop :=
  ∀ {X S : Scheme.{u}} (g : X ⟶ S)
    {K K' : DerivedCategory (Modules Λ S)} (k : K ⟶ K')
    (N : DerivedCategory (Modules Λ X)),
    tensorHom k (𝟙 _) ≫ a g K' N = a g K N ≫
      (moduleObjectDerivedPushforward Λ g).map
        (tensorHom ((moduleObjectDerivedPullback Λ g).map k) (𝟙 N))

private theorem normalized_projection_naturality
    (a : ProjectionFamily Λ) (ha : ProjectionNormalized Λ a) : ProjectionNatural Λ a := by
  unfold ProjectionNatural ProjectionNormalized ProjectionFamily internalMonoidal
    internalTensorBundle nativeTensorBundle at *
  intro X S g K K' k N
  rw [eq_of_heq (ha g K' N), eq_of_heq (ha g K N)]
  exact trace_projection_naturality Λ g k N

private theorem native_projection_naturality {X S : Scheme.{u}} (g : X ⟶ S)
    {K K' : DerivedCategory (Modules Λ S)} (k : K ⟶ K')
    (N : DerivedCategory (Modules Λ X)) :
    tensorHom k (𝟙 _) ≫ projectionMap Λ g K' N =
      projectionMap Λ g K N ≫
        (moduleObjectDerivedPushforward Λ g).map
          (tensorHom ((moduleObjectDerivedPullback Λ g).map k) (𝟙 N)) := by
  exact normalized_projection_naturality Λ
    (projection_existsUnique Λ).exists.choose
    (projection_existsUnique Λ).exists.choose_spec g k N

private theorem section_tensor_naturality {X S : Scheme.{u}}
    (g : X ⟶ S) (p : S ⟶ X)
    (s : moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPullback Λ g ≅
      𝟭 (DerivedCategory (Modules Λ X)))
    (U : DerivedCategory (Modules Λ X)) (e : U ≅ 𝟙_ (DerivedCategory (Modules Λ X)))
    {M N : DerivedCategory (Modules Λ X)} (f : M ⟶ N) :
    tensorHom ((moduleObjectDerivedPullback Λ g).map
        ((moduleObjectDerivedPullback Λ p).map f)) (𝟙 U) ≫
        tensorHom (s.hom.app N) e.hom ≫ (ρ_ N).hom =
      (tensorHom (s.hom.app M) e.hom ≫ (ρ_ M).hom) ≫ f := by
  have hs := s.hom.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hs
  rw [tensorHom_comp_tensorHom_assoc, Category.id_comp, hs]
  rw [← Category.comp_id e.hom, ← tensorHom_comp_tensorHom_assoc,
    tensorHom_id, rightUnitor_naturality]
  simp only [Category.comp_id, Functor.id_obj, Category.assoc]

private theorem compose_naturality_square {D : Type*} [Category* D]
    {A A' B B' C C' : D}
    {a : A ⟶ A'} {b : B ⟶ B'} {c : C ⟶ C'}
    {p : A ⟶ B} {p' : A' ⟶ B'} {q : B ⟶ C} {q' : B' ⟶ C'}
    (hp : a ≫ p' = p ≫ b) (hq : b ≫ q' = q ≫ c) :
    a ≫ (p' ≫ q') = (p ≫ q) ≫ c := by
  rw [← Category.assoc, hp, Category.assoc, hq, Category.assoc]

private theorem map_naturality_square {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) {A A' B B' : C}
    {a : A ⟶ A'} {b : B ⟶ B'} {q : A ⟶ B} {q' : A' ⟶ B'}
    (h : a ≫ q' = q ≫ b) :
    G.map a ≫ G.map q' = G.map q ≫ G.map b := by
  rw [← G.map_comp, h, G.map_comp]

private theorem section_comparison_naturality {X S : Scheme.{u}}
    (g : X ⟶ S) (p : S ⟶ X)
    (s : moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPullback Λ g ≅
      𝟭 (DerivedCategory (Modules Λ X)))
    (U : DerivedCategory (Modules Λ X)) (e : U ≅ 𝟙_ (DerivedCategory (Modules Λ X)))
    {M N : DerivedCategory (Modules Λ X)} (f : M ⟶ N) :
    tensorHom ((moduleObjectDerivedPullback Λ p).map f)
        (𝟙 ((moduleObjectDerivedPushforward Λ g).obj U)) ≫
        (projectionMap Λ g ((moduleObjectDerivedPullback Λ p).obj N) U ≫
          (moduleObjectDerivedPushforward Λ g).map
            (tensorHom (s.hom.app N) e.hom ≫ (ρ_ N).hom)) =
      (projectionMap Λ g ((moduleObjectDerivedPullback Λ p).obj M) U ≫
          (moduleObjectDerivedPushforward Λ g).map
            (tensorHom (s.hom.app M) e.hom ≫ (ρ_ M).hom)) ≫
        (moduleObjectDerivedPushforward Λ g).map f := by
  have hp := native_projection_naturality Λ g
    (K := (moduleObjectDerivedPullback Λ p).obj M)
    (K' := (moduleObjectDerivedPullback Λ p).obj N)
    ((moduleObjectDerivedPullback Λ p).map f) U
  have hq := map_naturality_square (moduleObjectDerivedPushforward Λ g)
    (section_tensor_naturality Λ g p s U e f)
  exact compose_naturality_square hp hq

private theorem sectionTensorMap_naturality {X S : Scheme.{u}}
    (g : X ⟶ S) (p : S ⟶ X)
    (s : moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPullback Λ g ≅
      𝟭 (DerivedCategory (Modules Λ X)))
    (U : DerivedCategory (Modules Λ X)) (e : U ≅ 𝟙_ (DerivedCategory (Modules Λ X)))
    {M N : DerivedCategory (Modules Λ X)} (f : M ⟶ N) :
    tensorHom ((moduleObjectDerivedPullback Λ p).map f)
        (𝟙 ((moduleObjectDerivedPushforward Λ g).obj U)) ≫
          sectionTensorMap Λ g p s U e N =
      sectionTensorMap Λ g p s U e M ≫
        (moduleObjectDerivedPushforward Λ g).map f := by
  unfold sectionTensorMap
  exact section_comparison_naturality Λ g p s U e f

private theorem diagonalTensorMap_naturality (Y : Scheme.{u})
    {M N : DerivedCategory (Modules Λ (ProjectiveLine Y))} (f : M ⟶ N) :
    tensorHom ((moduleObjectDerivedPullback Λ (firstProjection Y)).map f)
        (𝟙 ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
          (unit Λ (ProjectiveLine Y)))) ≫ diagonalTensorMap Λ Y N =
      diagonalTensorMap Λ Y M ≫
        (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).map f := by
  unfold diagonalTensorMap
  exact sectionTensorMap_naturality Λ (diagonalImmersion Y) (firstProjection Y)
    (pullSectionIso Λ Y (firstProjection Y) (pullback.diagonal_fst _))
    (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) f

private lemma diagonalTensorIso_hom_eq_inv (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    [IsIso (diagonalTensorMap Λ Y M)] :
    (diagonalTensorIso Λ Y M).hom = inv (diagonalTensorMap Λ Y M) := by
  simp only [diagonalTensorIso, Iso.symm_hom, asIso_inv]

/-- Naturality of the inverse canonical diagonal tensor comparison. -/
theorem diagonalTensorIso_naturality (Y : Scheme.{u})
    {M N : DerivedCategory (Modules Λ (ProjectiveLine Y))} (f : M ⟶ N) :
    (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).map f ≫
        (diagonalTensorIso Λ Y N).hom =
      (diagonalTensorIso Λ Y M).hom ≫
        tensorHom ((moduleObjectDerivedPullback Λ (firstProjection Y)).map f)
          (𝟙 ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
            (unit Λ (ProjectiveLine Y)))) := by
  have hM : IsIso (diagonalTensorMap Λ Y M) := diagonalTensorMap_isIso Λ Y M
  have hN : IsIso (diagonalTensorMap Λ Y N) := diagonalTensorMap_isIso Λ Y N
  rw [diagonalTensorIso_hom_eq_inv, diagonalTensorIso_hom_eq_inv]
  apply (cancel_mono (diagonalTensorMap Λ Y N)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have h := diagonalTensorMap_naturality Λ Y f
  have hh := congrArg (fun k ↦ inv (diagonalTensorMap Λ Y M) ≫ k) h
  simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hh.symm

end AlgebraicGeometry.ProEtale.RationalP1
