import Langlands.Geometry.FormalGroup.AtlasTangentTests
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-! # Localization of the overlap tangent module on a finite atlas -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open _root_.CategoryTheory

/-- Localize at a test coefficient and view the result as an algebra over the original atlas base. -/
abbrev awayTangentTest {R : Type v} [CommRing R] (A : CommAlgCat.{v} R) (r : A) :
    CommAlgCat.{v} R := CommAlgCat.of R (Localization.Away r)

/-- The structural map into a principal localization of an arbitrary affine test. -/
def awayTangentTestMap {R : Type v} [CommRing R] (A : CommAlgCat.{v} R) (r : A) :
    A ⟶ awayTangentTest A r := CommAlgCat.ofHom (IsScalarTower.toAlgHom R A (Localization.Away r))

private def furtherAwayMap {A : Type v} [CommRing A] (r s : A) (t : Localization.Away r)
    (h : algebraMap A (Localization.Away r) s = t) :
    Localization.Away s →ₐ[A] Localization.Away t := by
  let B := Localization.Away r
  let T := Localization.Away t
  exact IsLocalization.Away.liftAlgHom s (f := Algebra.ofId A T) (by
    change IsUnit (algebraMap A T s)
    rw [IsScalarTower.algebraMap_apply A B T, h]
    exact IsLocalization.Away.algebraMap_isUnit t)

private theorem furtherAwayMap_isLocalized {A : Type v} [CommRing A] (r s : A)
    (t : Localization.Away r) (h : algebraMap A (Localization.Away r) s = t) :
    IsLocalizedModule (Submonoid.powers r) (furtherAwayMap r s t h).toLinearMap := by
  subst t
  let S := Localization.Away s
  let B := Localization.Away r
  let T := Localization.Away (algebraMap A B s)
  let f : S →ₐ[A] T := furtherAwayMap r s _ rfl
  let : Algebra S T := f.toAlgebra
  have : IsScalarTower A S T := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  have h : IsLocalization.Away (algebraMap A S r) T := IsLocalization.Away.commutes S B T s r
  have : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers r)) T := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using h
  exact (isLocalizedModule_iff_isLocalization (S := Submonoid.powers r)).mpr inferInstance

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {I : Type} [Finite I] (X : BasicAtlas O R I)
variable (A : CommAlgCat.{v} R) (r : A)

local notation "B" => awayTangentTest A r
local notation "φ" => awayTangentTestMap A r

/-- The test coefficient extension, with the target regarded as a module over the original test. -/
def tangentAwayMap : X.tangentSubmodule A →ₗ[A] (X.tangentSubmodule B).restrictScalars A where
  toFun := X.tangentMap φ
  map_add' := (X.tangentMap φ).map_add
  map_smul' c z := by
    change X.tangentMap φ (c • z) = c • X.tangentMap φ z
    exact ((X.tangentMap φ).map_smulₛₗ c z).trans (algebraMap_smul B c _)

@[simp]
theorem tangentAwayMap_apply (z : X.tangentSubmodule A) :
    X.tangentAwayMap A r z = X.tangentMap φ z := rfl

private theorem image_chartElement (a : X.opens) :
    algebraMap A B (algebraMap R A a.val) = algebraMap R B a.val :=
  (IsScalarTower.algebraMap_apply R A B a.val).symm

private theorem image_overlapElement (a b : X.opens) :
    algebraMap A B (algebraMap R A a.val * algebraMap R A b.val) =
      algebraMap R B a.val * algebraMap R B b.val := by
  rw [map_mul, X.image_chartElement A r, X.image_chartElement A r]

private def chartAwayAlg (a : X.opens) : X.localAlgebra A a →ₐ[A] X.localAlgebra B a :=
  furtherAwayMap r (algebraMap R A a.val) (algebraMap R B a.val) (X.image_chartElement A r a)

private def overlapAwayAlg (a b : X.opens) : X.overlapAlgebra A a b →ₐ[A] X.overlapAlgebra B a b :=
  furtherAwayMap r _ _ (X.image_overlapElement A r a b)

private def overlapAwayTestMap (a b : X.opens) : X.overlapAlgebra A a b ⟶ X.overlapAlgebra B a b :=
  X.overlapFactor (φ ≫ X.overlapMap B a b) a b (X.overlapUnitLeft B a b) (X.overlapUnitRight B a b)

private theorem chartAwayAlg_apply (a : X.opens) (x : X.localAlgebra A a) :
    X.chartAwayAlg A r a x = (X.tangentLocalizedTestMap φ a).hom x := by
  have h : (X.chartAwayAlg A r a).toRingHom = (X.tangentLocalizedTestMap φ a).hom.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R A a.val))
    apply RingHom.ext
    intro z
    exact ((X.chartAwayAlg A r a).commutes z).trans
      (congrArg (fun g : A ⟶ X.localAlgebra B a => g.hom z)
        (X.localizationMap_tangentLocalizedTestMap φ a)).symm
  exact RingHom.congr_fun h x

private theorem overlapAwayAlg_apply (a b : X.opens) (x : X.overlapAlgebra A a b) :
    X.overlapAwayAlg A r a b x = (X.overlapAwayTestMap A r a b).hom x := by
  have h : (X.overlapAwayAlg A r a b).toRingHom = (X.overlapAwayTestMap A r a b).hom.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R A a.val * algebraMap R A b.val))
    apply RingHom.ext
    intro z
    exact ((X.overlapAwayAlg A r a b).commutes z).trans
      (congrArg (fun g : A ⟶ X.overlapAlgebra B a b => g.hom z)
        (X.overlapMap_factor (φ ≫ X.overlapMap B a b) a b
          (X.overlapUnitLeft B a b) (X.overlapUnitRight B a b))).symm
  exact RingHom.congr_fun h x

private theorem chartAway_overlap_left (a b : X.opens) :
    X.overlapFromLeft A a b ≫ X.overlapAwayTestMap A r a b =
      X.tangentLocalizedTestMap φ a ≫ X.overlapFromLeft B a b := by
  rw [overlapAwayTestMap, X.overlapFromLeft_factor]
  symm
  let t : X.ChartTest A := ⟨X.localAlgebra B a, φ ≫ X.localizationMap B a, a, X.localUnit B a⟩
  change X.testFactor t ≫ X.overlapFromLeft B a b = _
  rw [X.testFactor_comp t (X.overlapFromLeft B a b) (X.overlapUnitLeft B a b)]
  have h : t.map ≫ X.overlapFromLeft B a b = φ ≫ X.overlapMap B a b := by
    change (φ ≫ X.localizationMap B a) ≫ X.overlapFromLeft B a b = _
    rw [Category.assoc]
    exact congrArg (fun g : B ⟶ X.overlapAlgebra B a b => φ ≫ g)
      (X.localizationMap_testFactor ⟨X.overlapAlgebra B a b, X.overlapMap B a b, a,
        X.overlapUnitLeft B a b⟩)
  rw [h]

private theorem chartAway_overlap_right (a b : X.opens) :
    X.overlapFromRight A a b ≫ X.overlapAwayTestMap A r a b =
      X.tangentLocalizedTestMap φ b ≫ X.overlapFromRight B a b := by
  rw [overlapAwayTestMap, X.overlapFromRight_factor]
  symm
  let t : X.ChartTest A := ⟨X.localAlgebra B b, φ ≫ X.localizationMap B b, b, X.localUnit B b⟩
  change X.testFactor t ≫ X.overlapFromRight B a b = _
  rw [X.testFactor_comp t (X.overlapFromRight B a b) (X.overlapUnitRight B a b)]
  have h : t.map ≫ X.overlapFromRight B a b = φ ≫ X.overlapMap B a b := by
    change (φ ≫ X.localizationMap B b) ≫ X.overlapFromRight B a b = _
    rw [Category.assoc]
    exact congrArg (fun g : B ⟶ X.overlapAlgebra B a b => φ ≫ g)
      (X.localizationMap_testFactor ⟨X.overlapAlgebra B a b, X.overlapMap B a b, b,
        X.overlapUnitRight B a b⟩)
  rw [h]

private def chartProductAwayMap : X.LocalizedTangent A →ₗ[A] X.LocalizedTangent B :=
  LinearMap.piMap fun a => LinearMap.piMap fun _ : I => (X.chartAwayAlg A r a).toLinearMap

private def overlapProductAwayMap :
    ((ab : X.opens × X.opens) → I → X.overlapAlgebra A ab.1 ab.2) →ₗ[A]
      ((ab : X.opens × X.opens) → I → X.overlapAlgebra B ab.1 ab.2) :=
  LinearMap.piMap fun ab => LinearMap.piMap fun _ : I => (X.overlapAwayAlg A r ab.1 ab.2).toLinearMap

private theorem chartProductAwayMap_isLocalized [Finite X.opens] :
    IsLocalizedModule (Submonoid.powers r) (X.chartProductAwayMap A r) := by
  have (a : X.opens) : IsLocalizedModule (Submonoid.powers r)
      (LinearMap.piMap fun _ : I => (X.chartAwayAlg A r a).toLinearMap) := by
    exact @IsLocalizedModule.pi A _ _ I _ _ _ _ _ _ _
      (fun _ => (X.chartAwayAlg A r a).toLinearMap)
      (fun _ => furtherAwayMap_isLocalized r _ _ (X.image_chartElement A r a))
  exact IsLocalizedModule.pi _ _

private theorem overlapProductAwayMap_isLocalized [Finite X.opens] :
    IsLocalizedModule (Submonoid.powers r) (X.overlapProductAwayMap A r) := by
  have (ab : X.opens × X.opens) : IsLocalizedModule (Submonoid.powers r)
      (LinearMap.piMap fun _ : I => (X.overlapAwayAlg A r ab.1 ab.2).toLinearMap) := by
    exact @IsLocalizedModule.pi A _ _ I _ _ _ _ _ _ _
      (fun _ => (X.overlapAwayAlg A r ab.1 ab.2).toLinearMap)
      (fun _ => furtherAwayMap_isLocalized r _ _ (X.image_overlapElement A r ab.1 ab.2))
  exact IsLocalizedModule.pi _ _

private theorem tangentOverlapDifference_away :
    (X.overlapProductAwayMap A r).comp (X.tangentOverlapDifference A) =
      ((X.tangentOverlapDifference B).restrictScalars A).comp (X.chartProductAwayMap A r) := by
  apply LinearMap.ext
  intro z
  funext ab i
  obtain ⟨a, b⟩ := ab
  let S := X.overlapAlgebra A a b
  let T := X.overlapAlgebra B a b
  let f := X.overlapAwayTestMap A r a b
  let l := X.overlapFromLeft A a b
  let g := X.overlapFromRight A a b
  let l' := X.overlapFromLeft B a b
  let g' := X.overlapFromRight B a b
  let x : I → S := fun j => l.hom (z a j)
  let y : I → S := fun j => g.hom (z b j)
  let x' : I → T := fun j => l'.hom (X.chartAwayAlg A r a (z a j))
  let y' : I → T := fun j => g'.hom (X.chartAwayAlg A r b (z b j))
  let H := X.transitionTangent S a b (X.overlapUnitLeft A a b) (X.overlapUnitRight A a b)
  let H' := X.transitionTangent T a b (X.overlapUnitLeft B a b) (X.overlapUnitRight B a b)
  have hl : (fun j => f.hom (x j)) = x' := funext fun j =>
    (congrArg (fun q : X.localAlgebra A a ⟶ T => q.hom (z a j))
      (X.chartAway_overlap_left A r a b)).trans
      (congrArg l'.hom ((X.chartAwayAlg_apply A r a (z a j)).symm))
  have hr : (fun j => f.hom (y j)) = y' := funext fun j =>
    (congrArg (fun q : X.localAlgebra A b ⟶ T => q.hom (z b j))
      (X.chartAway_overlap_right A r a b)).trans
      (congrArg g'.hom ((X.chartAwayAlg_apply A r b (z b j)).symm))
  have h := (X.transitionTangent_natural f a b (X.overlapUnitLeft A a b)
    (X.overlapUnitRight A a b) (X.overlapUnitLeft B a b) (X.overlapUnitRight B a b) x).trans
      (congrArg H' hl)
  change X.overlapAwayAlg A r a b (H x i - y i) = H' x' i - y' i
  rw [map_sub]
  rw [X.overlapAwayAlg_apply, X.overlapAwayAlg_apply]
  exact congrArg₂ (· - ·) (congrFun h i) (congrFun hr i)

attribute [local instance] chartProductAwayMap_isLocalized overlapProductAwayMap_isLocalized

private theorem tangentOverlapDifference_localized [Finite X.opens] :
    IsLocalizedModule.map (Submonoid.powers r) (X.chartProductAwayMap A r)
        (X.overlapProductAwayMap A r) (X.tangentOverlapDifference A) =
      (X.tangentOverlapDifference B).restrictScalars A := by
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers r)
    (X.chartProductAwayMap A r) (X.overlapProductAwayMap A r)
  rw [IsLocalizedModule.map_comp]
  exact X.tangentOverlapDifference_away A r

/-- On a finite atlas the compatible tangent module commutes with every principal localization. -/
theorem tangentAwayMap_isLocalized_of_finite [Finite X.opens] :
    IsLocalizedModule (Submonoid.powers r) (X.tangentAwayMap A r) := by
  let p := Submonoid.powers r
  let f := X.chartProductAwayMap A r
  let g := X.overlapProductAwayMap A r
  let h := X.tangentOverlapDifference A
  let h' := IsLocalizedModule.map p f g h
  let k : X.tangentSubmodule A →ₗ[A] LinearMap.ker h' := LinearMap.toKerIsLocalized p f g h
  have : IsLocalizedModule p k := LinearMap.toKerLocalized_isLocalizedModule B p f g h
  let e : LinearMap.ker h' ≃ₗ[A] (X.tangentSubmodule B).restrictScalars A :=
    LinearEquiv.ofEq _ _ ((congrArg LinearMap.ker (X.tangentOverlapDifference_localized A r)).trans
      (LinearMap.ker_restrictScalars A (X.tangentOverlapDifference B)))
  have he : e.toLinearMap.comp k = X.tangentAwayMap A r := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    funext a i
    exact X.chartAwayAlg_apply A r a (z.val a i)
  rw [← he]
  exact IsLocalizedModule.of_linearEquiv p k e

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
