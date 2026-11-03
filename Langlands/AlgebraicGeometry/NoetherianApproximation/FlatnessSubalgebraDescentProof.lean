import Langlands.AlgebraicGeometry.NoetherianApproximation.FlatnessDescentStatements
import Langlands.AlgebraicGeometry.Modules.AffineRelativeFlatness
import Langlands.AlgebraicGeometry.Modules.FinitePresentation
import Langlands.AlgebraicGeometry.Modules.FinitePresentationPullback
import Langlands.AlgebraicGeometry.Modules.PullbackQuasicoherent
import Langlands.Algebra.FiniteTypeModuleFlatnessDescent
import Mathlib.AlgebraicGeometry.Morphisms.Affine

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

open Modules

/-- Relative flatness on an open chart may use ordinary pullback or restriction. -/
lemma isFlatOver_pullback_open_iff {X Y S : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (f : Y ⟶ S) (M : Y.Modules) :
    IsFlatOver (g ≫ f) ((Scheme.Modules.pullback g).obj M) ↔
      IsFlatOver (g ≫ f) (M.restrict g) :=
  isFlatOver_iff_of_iso _ ((Scheme.Modules.restrictFunctorIsoPullback g).app M).symm

/-- Local finite type on an affine scheme gives finite type for the relative section ring. -/
lemma finiteType_relativeSectionRing {R : CommRingCat.{u}} {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec R) [LocallyOfFiniteType f] :
    let := (DerivedSections.structureRingHom f).hom.toAlgebra
    Algebra.FiniteType R Γ(X, ⊤) := by
  let := (DerivedSections.structureRingHom f).hom.toAlgebra
  apply RingHom.finiteType_algebraMap.mp
  change (DerivedSections.structureRingHom f).hom.FiniteType
  exact (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance).comp
    (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso R).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).surjective)

/-- Scalar sections on any Cartesian affine square detect relative flatness. -/
lemma isFlatOver_pullback_iff_flat_tensor_sections
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
    (g : Y ⟶ X) (h : IsPullback g f' f (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] :
    let := φ.hom.toAlgebra
    IsFlatOver f' ((Scheme.Modules.pullback g).obj M) ↔
      Module.Flat S (S ⊗[R] ((DerivedSections.relativeGlobalSections f).obj M)) := by
  let := φ.hom.toAlgebra
  let e := DerivedSections.affineCartesianScalarSectionsIso φ f f' g h.w h M
  exact (isFlatOver_iff_flat_relativeGlobalSections f'
    ((Scheme.Modules.pullback g).obj M)).trans (Module.Flat.equiv_iff e.toLinearEquiv).symm

/-- A Cartesian base change is relatively flat exactly when all the scalar-extended
section modules on an affine open cover are flat. -/
lemma isFlatOver_pullback_iff_forall_flat_tensor_sections
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X₀ X : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec R) (a : X ⟶ X₀) (f : X ⟶ Spec S)
    (h : IsPullback a f f₀ (Spec.map φ))
    (M : X₀.Modules) [M.IsQuasicoherent] (𝒰 : X₀.OpenCover)
    [∀ i, IsAffine (𝒰.X i)] :
    let := φ.hom.toAlgebra
    IsFlatOver f ((Scheme.Modules.pullback a).obj M) ↔
      ∀ i, Module.Flat S (S ⊗[R]
        ((DerivedSections.relativeGlobalSections (𝒰.f i ≫ f₀)).obj
          ((Scheme.Modules.pullback (𝒰.f i)).obj M))) := by
  let := φ.hom.toAlgebra
  let 𝒱 : X.OpenCover := 𝒰.pullback₁ a
  rw [isFlatOver_iff_openCover f ((Scheme.Modules.pullback a).obj M)
    𝒱.X 𝒱.f (Scheme.Cover.exists_eq 𝒱)]
  apply forall_congr'
  intro i
  have hp : IsPullback (𝒰.pullbackHom a i) (𝒱.f i ≫ f)
      (𝒰.f i ≫ f₀) (Spec.map φ) :=
    (IsPullback.of_hasPullback a (𝒰.f i)).flip.paste_vert h
  have : IsAffine (𝒱.X i) := IsAffine.of_isPullback hp
  let e :
      (Scheme.Modules.pullback (𝒱.f i)).obj ((Scheme.Modules.pullback a).obj M) ≅
        (Scheme.Modules.pullback (𝒰.pullbackHom a i)).obj
          ((Scheme.Modules.pullback (𝒰.f i)).obj M) :=
    (Scheme.Modules.pullbackComp (𝒱.f i) a).app M ≪≫
      (Scheme.Modules.pullbackCongr (𝒰.pullbackHom_map a i).symm).app M ≪≫
      ((Scheme.Modules.pullbackComp (𝒰.pullbackHom a i) (𝒰.f i)).app M).symm
  exact (isFlatOver_pullback_open_iff (𝒱.f i) f
      ((Scheme.Modules.pullback a).obj M)).symm.trans
    ((isFlatOver_iff_of_iso _ e).trans
      (isFlatOver_pullback_iff_flat_tensor_sections φ (𝒰.f i ≫ f₀) (𝒱.f i ≫ f)
        (𝒰.pullbackHom a i) hp ((Scheme.Modules.pullback (𝒰.f i)).obj M)))

/-- Relative flatness of a finitely presented actual module descends to a finite
subalgebra, uniformly for every Cartesian realization of the descended scheme. -/
theorem isFlatOverSubalgebraDescent : IsFlatOverSubalgebraDescentStatement.{u} := by
  intro A₀ _ _ A _ _ X₀ f₀ _ _ M₀ hM X a f h hflat s
  let := hM
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  let 𝒰 := X₀.affineCover.finiteSubcover
  let B (i : 𝒰.I₀) := Γ(𝒰.X i, ⊤)
  let Mi (i : 𝒰.I₀) := (Scheme.Modules.pullback (𝒰.f i)).obj M₀
  let N (i : 𝒰.I₀) :=
    (DerivedSections.relativeGlobalSections (𝒰.f i ≫ f₀)).obj (Mi i)
  let (i : 𝒰.I₀) : Algebra A₀ (B i) :=
    (DerivedSections.structureRingHom (𝒰.f i ≫ f₀)).hom.toAlgebra
  let (i : 𝒰.I₀) : Module (B i) (N i) := by
    change Module Γ(𝒰.X i, ⊤) ((DerivedSections.globalSections (𝒰.X i)).obj (Mi i))
    exact ((DerivedSections.globalSections (𝒰.X i)).obj (Mi i)).isModule
  have (i : 𝒰.I₀) : IsScalarTower A₀ (B i) (N i) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  have (i : 𝒰.I₀) : Algebra.FiniteType A₀ (B i) :=
    finiteType_relativeSectionRing (𝒰.f i ≫ f₀)
  have (i : 𝒰.I₀) : (Mi i).IsFinitePresentation :=
    isFinitePresentation_pullback (𝒰.f i) M₀
  have (i : 𝒰.I₀) : Module.Finite (B i) (N i) :=
    hasFiniteAffineSections_of_isFinitePresentation (Mi i) ⟨⊤, isAffineOpen_top _⟩
  have (i : 𝒰.I₀) : Module.Flat A (A ⊗[A₀] (N i)) := by
    have hh := isFlatOver_pullback_iff_forall_flat_tensor_sections
      (CommRingCat.ofHom (algebraMap A₀ A)) f₀ a f h M₀ 𝒰
    have he : (CommRingCat.ofHom (algebraMap A₀ A)).hom.toAlgebra =
        (inferInstance : Algebra A₀ A) := toAlgebra_algebraMap
    rw [he] at hh
    exact hh.mp hflat i
  obtain ⟨T, hT, hs, hTN⟩ :=
    Langlands.Algebra.exists_fg_subalgebra_forall_flat_module (R₀ := A₀) (R := A)
      (fun i => ↥(B i)) (fun i => ↥(N i)) s
  refine ⟨T, hT, hs, ?_⟩
  intro X' a' f' h'
  have hh := isFlatOver_pullback_iff_forall_flat_tensor_sections
    (CommRingCat.ofHom (algebraMap A₀ T)) f₀ a' f' h' M₀ 𝒰
  have he : (CommRingCat.ofHom (algebraMap A₀ T)).hom.toAlgebra =
      (inferInstance : Algebra A₀ T) := toAlgebra_algebraMap
  rw [he] at hh
  exact hh.mpr hTN

end Langlands.AlgebraicGeometry.NoetherianApproximation
