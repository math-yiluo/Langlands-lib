/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedModulePushforwardMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ModuleRegularUnitIso
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleRegularUnitIso
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleRegularAdjunctionImage
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-! # Descent from Artin–Schreier projector calculations -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option quotPrecheck false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem isIso_of_etale_surjective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : Y ⟶ X)
    [AlgebraicGeometry.Etale p] (hp : Function.Surjective p.base)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : M ⟶ N) [IsIso ((CondensedRing.upperStar Λ p).map f)] : IsIso f := by
  have hc : Presieve.singleton p ∈ Scheme.proetalePrecoverage X :=
    Scheme.etalePrecoverage_le_proetalePrecoverage X
      ((Scheme.singleton_mem_precoverage_iff (P := @AlgebraicGeometry.Etale) p).2
        ⟨hp, inferInstance⟩)
  have hc' : Presieve.ofArrows (fun _ : PUnit.{u + 1} ↦ Y) (fun _ ↦ p) ∈
      Scheme.proetalePrecoverage X := by
    simpa only [Presieve.ofArrows_pUnit] using hc
  let e : CondensedRing.upperStar Λ p ⋙ Mod.forget _ ≅
      Mod.forget (condensedRingObj Λ X) ⋙ upperStar Ab.{u + 1} p :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((upperStar Ab.{u + 1} p).mapMod (condensedRingObj Λ X))
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ p)))
      (Mod.forget _)
  have h' : IsIso ((upperStar Ab.{u + 1} p).map f.hom) :=
    (NatIso.isIso_map_iff e f).1 (by
      change IsIso ((Mod.forget _).map ((CondensedRing.upperStar Λ p).map f))
      infer_instance)
  have : IsIso ((Mod.forget (condensedRingObj Λ X)).map f) :=
    isIso_of_isIso_localizationRestriction Ab.{u + 1} f.hom
      (fun _ : PUnit.{u + 1} ↦ p) hc' (fun _ ↦
        (NatIso.isIso_map_iff
          (upperStarIsoLocalizationRestriction Ab.{u + 1} p inferInstance) f.hom).1 h')
  exact isIso_of_reflects_iso f (Mod.forget _)

private theorem reflects_of_etale_surjective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : Y ⟶ X)
    [AlgebraicGeometry.Etale p] (hp : Function.Surjective p.base) :
    (CondensedRing.upperStar Λ p).ReflectsIsomorphisms := by
  constructor
  intro M N f hf
  exact isIso_of_etale_surjective Λ p hp f

-- Keep the member property abstract while reducing the singleton pullback cover.
private theorem exists_singleton_pullback_property
    {S T X : Scheme.{u}} (p : T ⟶ S) [AlgebraicGeometry.Etale p]
    (hp : Function.Surjective p.base) (b : X ⟶ S)
    (Q : ∀ Z : Scheme.{u}, (Z ⟶ X) → Prop)
    (h : Q (pullback b p) (pullback.fst b p)) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      ∀ i : U.I₀, Q (U.X i) (U.f i) := by
  let U₀ : Scheme.Cover.{u} Scheme.etalePrecoverage S :=
    .singleton p ((Scheme.singleton_mem_precoverage_iff (P := @AlgebraicGeometry.Etale) _).2
      ⟨hp, inferInstance⟩)
  let U : Scheme.Cover.{u} Scheme.proetalePrecoverage S :=
    ⟨U₀.toPreZeroHypercover, Scheme.etalePrecoverage_le_proetalePrecoverage S U₀.mem₀⟩
  exact ⟨U.pullback₁ b, fun _ ↦ h⟩

private theorem flat_of_regularTensorIso
    {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R : C} [MonObj R] [IsCommMonObj R] {M N : Mod C R}
    (e : M ⊗ N ≅ Mod.regular R) : ObjectProperty.flat M := by
  exact ObjectProperty.flat_of_tensorIso e

private theorem free_of_regularIso
    {C : Type*} [Category C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]
    {M : Mod C R} (e : M ≅ Mod.regular R) : Mod.IsFree R M := by
  exact ⟨1, ⟨e ≪≫ (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular R)).symm⟩⟩

private theorem monoidal_tensor_iso
    {C : Type*} {D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    {M N P : C} (h : Nonempty (M ⊗ N ≅ P)) :
    Nonempty (F.obj M ⊗ F.obj N ≅ F.obj P) := by
  obtain ⟨e⟩ := h
  exact ⟨Functor.Monoidal.μIso F _ _ ≪≫ F.mapIso e⟩

private theorem tensor_iso_transport
    {C : Type*} [Category C] [MonoidalCategory C] {M M' N N' P Q : C}
    (e : M ≅ M') (f : N ≅ N') (g : P ≅ Q) (h : Nonempty (M' ⊗ N' ≅ Q)) :
    Nonempty (M ⊗ N ≅ P) := by
  obtain ⟨i⟩ := h
  exact ⟨tensorIso e f ≪≫ i ≪≫ g.symm⟩

private theorem nonempty_iso_trans
    {C : Type*} [Category C] {M N P : C}
    (h : Nonempty (M ≅ N)) (h' : Nonempty (N ≅ P)) : Nonempty (M ≅ P) := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := h'
  exact ⟨e ≪≫ e'⟩

private theorem pullback_regular_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} (b : X ⟶ S)
    {N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)}
    (h : Nonempty (N ≅ Mod.regular (condensedRingObj Λ S))) :
    Nonempty ((CondensedRing.upperStar Λ b).obj N ≅
      Mod.regular (condensedRingObj Λ X)) := by
  obtain ⟨e⟩ := h
  exact ⟨(CondensedRing.upperStar Λ b).mapIso e ≪≫
    Mod.regularMapIso (condensedRingObj Λ S) (CondensedRing.upperStar Λ b)⟩

private theorem rankOne_cover_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N)
    (h : ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : V.I₀,
      Nonempty ((CondensedRing.upperStar Λ (V.f i)).obj N ≅
        Mod.regular (condensedRingObj Λ (V.X i)))) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : V.I₀,
      Nonempty ((CondensedRing.upperStar Λ (V.f i)).obj M ≅
        Mod.regular (condensedRingObj Λ (V.X i))) := by
  obtain ⟨V, hV⟩ := h
  refine ⟨V, fun i ↦ ?_⟩
  obtain ⟨ei⟩ := hV i
  exact ⟨(CondensedRing.upperStar Λ (V.f i)).mapIso e ≪≫ ei⟩

private theorem rankOne_cover_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    (p : T ⟶ S) [AlgebraicGeometry.Etale p] (hp : Function.Surjective p.base)
    (b : X ⟶ S)
    (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (h : Nonempty ((CondensedRing.upperStar Λ p).obj N ≅
      Mod.regular (condensedRingObj Λ T))) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : V.I₀,
      Nonempty ((CondensedRing.upperStar Λ (V.f i)).obj
        ((CondensedRing.upperStar Λ b).obj N) ≅
          Mod.regular (condensedRingObj Λ (V.X i))) := by
  obtain ⟨e⟩ := h
  apply exists_singleton_pullback_property p hp b
    (fun Z g ↦ Nonempty ((CondensedRing.upperStar Λ g).obj
      ((CondensedRing.upperStar Λ b).obj N) ≅ Mod.regular (condensedRingObj Λ Z)))
  exact ⟨(CondensedRing.upperStarComp Λ (pullback.fst b p) b).symm.app N ≪≫
    (CondensedRing.upperStarCongr Λ (pullback.condition (f := b) (g := p))).app N ≪≫
    (CondensedRing.upperStarComp Λ (pullback.snd b p) p).app N ≪≫
    (CondensedRing.upperStar Λ (pullback.snd b p)).mapIso e ≪≫
    Mod.regularMapIso (condensedRingObj Λ T)
      (CondensedRing.upperStar Λ (pullback.snd b p))⟩

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]

local notation "A" => AffineSpace PUnit (Spec (CommRingCat.of k))
local notation "q" => AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)
local notation "F" => CondensedRing.upperStar Λ q
local notation "G" => CondensedRing.lowerStar Λ q
local notation "adj" => CondensedRing.upperStarLowerStarAdjunction Λ q
local notation "e" => condensedArtinSchreierProjector Λ k

/-- The canonical lax monoidal structure on the module pushforward, adjoint to the
strong monoidal pullback. Source: monoidal adjunction and latest blueprint
`prop-kernel-lisse.proof.md` (blueprint: lem-kernel-condensed-projector-descent). -/
abbrev condensedArtinSchreierLowerStarMonoidal : (CondensedRing.lowerStar Λ q).LaxMonoidal :=
  CondensedRing.moduleLowerStarMonoidal Λ q

attribute [local instance] condensedArtinSchreierLowerStarMonoidal

/-- Pullback along the Artin–Schreier cover reflects isomorphisms.
Source: descent along an etale surjection
(blueprint: lem-kernel-condensed-projector-descent). -/
theorem condensedArtinSchreierPullback_reflectsIsomorphisms :
    (CondensedRing.upperStar Λ q).ReflectsIsomorphisms := by
  have : AlgebraicGeometry.Etale q := Etale.etale_artinSchreierMap (k := k)
  exact reflects_of_etale_surjective Λ q (AffineSpace.surjective_artinSchreierMap k)

private theorem images_tensor
    (heval : ∀ ψ : AddChar k (MonObj.Γ Λ),
      IsIso ((CondensedRing.upperStar Λ q).map (image.ι (e ψ).asHom) ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app
          (Mod.regular (condensedRingObj Λ A))))
    (hprod : ∀ ψ ψ' : AddChar k (MonObj.Γ Λ),
      ((image.ι (e ψ).asHom ⊗ₘ image.ι (e ψ').asHom) ≫
        Functor.LaxMonoidal.μ G (Mod.regular (condensedRingObj Λ A))
          (Mod.regular (condensedRingObj Λ A)) ≫
        (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A))) ≫
          (e (ψ * ψ')).asHom =
      (image.ι (e ψ).asHom ⊗ₘ image.ι (e ψ').asHom) ≫
        Functor.LaxMonoidal.μ G (Mod.regular (condensedRingObj Λ A))
          (Mod.regular (condensedRingObj Λ A)) ≫
        (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A)))
    (_hunit : Functor.LaxMonoidal.ε G ≫ (e 1).asHom = Functor.LaxMonoidal.ε G)
    (χ χ' : AddChar k (MonObj.Γ Λ)) :
    Nonempty (condensedArtinSchreierSheaf Λ k χ ⊗
      condensedArtinSchreierSheaf Λ k χ' ≅ condensedArtinSchreierSheaf Λ k (χ * χ')) := by
  let := condensedArtinSchreierPullback_reflectsIsomorphisms Λ k
  have := CondensedRing.moduleAdjunctionIsMonoidal Λ q
  have := heval χ
  have := heval χ'
  have := heval (χ * χ')
  have := (CondensedRing.upperStarLowerStarAdjunction Λ q).image_tensor_regular_isIso
    (e χ) (e χ') (e (χ * χ')) (hprod χ χ')
  exact ⟨asIso (((image.ι (e χ).asHom ⊗ₘ image.ι (e χ').asHom) ≫
    Functor.LaxMonoidal.μ G (Mod.regular (condensedRingObj Λ A))
          (Mod.regular (condensedRingObj Λ A)) ≫
    (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A))) ≫
      factorThruImage (e (χ * χ')).asHom)⟩

private theorem image_unit
    (heval : ∀ ψ : AddChar k (MonObj.Γ Λ),
      IsIso ((CondensedRing.upperStar Λ q).map (image.ι (e ψ).asHom) ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app
          (Mod.regular (condensedRingObj Λ A))))
    (_hprod : ∀ ψ ψ' : AddChar k (MonObj.Γ Λ),
      ((image.ι (e ψ).asHom ⊗ₘ image.ι (e ψ').asHom) ≫
        Functor.LaxMonoidal.μ G (Mod.regular (condensedRingObj Λ A))
          (Mod.regular (condensedRingObj Λ A)) ≫
        (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A))) ≫
          (e (ψ * ψ')).asHom =
      (image.ι (e ψ).asHom ⊗ₘ image.ι (e ψ').asHom) ≫
        Functor.LaxMonoidal.μ G (Mod.regular (condensedRingObj Λ A))
          (Mod.regular (condensedRingObj Λ A)) ≫
        (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A)))
    (hunit : Functor.LaxMonoidal.ε G ≫ (e 1).asHom = Functor.LaxMonoidal.ε G)
    : Nonempty (Mod.regular (condensedRingObj Λ A) ≅
      condensedArtinSchreierSheaf Λ k 1) := by
  let := condensedArtinSchreierPullback_reflectsIsomorphisms Λ k
  have := CondensedRing.moduleAdjunctionIsMonoidal Λ q
  have := heval 1
  have := (CondensedRing.upperStarLowerStarAdjunction Λ q).unit_image_regular_isIso (e 1) hunit
  exact ⟨Mod.regularUnitIso (condensedRingObj Λ A) ≪≫
    asIso (Functor.LaxMonoidal.ε G ≫ factorThruImage (e 1).asHom)⟩

private def sheafOfPullbackIso
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (ψ : AddChar k (MonObj.Γ Λ)) (f : Γ(X, ⊤)) :
    condensedArtinSchreierSheafOf Λ k X ψ f ≅
      (CondensedRing.upperStar Λ (AffineSpace.homOfVector (X ↘ Spec (.of k))
        (fun _ : PUnit.{u + 1} ↦ f))).obj (condensedArtinSchreierSheaf Λ k ψ) :=
  Iso.refl _

private theorem tensor_of_projectors
    (heval : ∀ ψ : AddChar k (MonObj.Γ Λ),
      IsIso ((CondensedRing.upperStar Λ q).map (image.ι (e ψ).asHom) ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app
          (Mod.regular (condensedRingObj Λ A))))
    (hprod : ∀ ψ ψ' : AddChar k (MonObj.Γ Λ),
      ((image.ι (e ψ).asHom ⊗ₘ image.ι (e ψ').asHom) ≫
        Functor.LaxMonoidal.μ G (Mod.regular (condensedRingObj Λ A))
          (Mod.regular (condensedRingObj Λ A)) ≫
        (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A))) ≫
          (e (ψ * ψ')).asHom =
      (image.ι (e ψ).asHom ⊗ₘ image.ι (e ψ').asHom) ≫
        Functor.LaxMonoidal.μ G (Mod.regular (condensedRingObj Λ A))
          (Mod.regular (condensedRingObj Λ A)) ≫
        (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A)))
    (hunit : Functor.LaxMonoidal.ε G ≫ (e 1).asHom = Functor.LaxMonoidal.ε G)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (ψ ψ' : AddChar k (MonObj.Γ Λ)) (f : Γ(X, ⊤)) :
    Nonempty (condensedArtinSchreierSheafOf Λ k X ψ f ⊗
      condensedArtinSchreierSheafOf Λ k X ψ' f ≅
        condensedArtinSchreierSheafOf Λ k X (ψ * ψ') f) := by
  exact tensor_iso_transport (sheafOfPullbackIso Λ k X ψ f)
    (sheafOfPullbackIso Λ k X ψ' f) (sheafOfPullbackIso Λ k X (ψ * ψ') f)
    (monoidal_tensor_iso (CondensedRing.upperStar Λ
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit.{u + 1} ↦ f)))
      (images_tensor Λ k heval hprod hunit ψ ψ'))

private theorem inverse_of_projectors
    (heval : ∀ ψ : AddChar k (MonObj.Γ Λ),
      IsIso ((CondensedRing.upperStar Λ q).map (image.ι (e ψ).asHom) ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app
          (Mod.regular (condensedRingObj Λ A))))
    (hprod : ∀ ψ ψ' : AddChar k (MonObj.Γ Λ),
      ((image.ι (e ψ).asHom ⊗ₘ image.ι (e ψ').asHom) ≫
        Functor.LaxMonoidal.μ G (Mod.regular (condensedRingObj Λ A))
          (Mod.regular (condensedRingObj Λ A)) ≫
        (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A))) ≫
          (e (ψ * ψ')).asHom =
      (image.ι (e ψ).asHom ⊗ₘ image.ι (e ψ').asHom) ≫
        Functor.LaxMonoidal.μ G (Mod.regular (condensedRingObj Λ A))
          (Mod.regular (condensedRingObj Λ A)) ≫
        (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A)))
    (hunit : Functor.LaxMonoidal.ε G ≫ (e 1).asHom = Functor.LaxMonoidal.ε G)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (ψ : AddChar k (MonObj.Γ Λ)) (f : Γ(X, ⊤)) :
    Nonempty (condensedArtinSchreierSheafOf Λ k X ψ f ⊗
      condensedArtinSchreierSheafOf Λ k X ψ⁻¹ f ≅ Mod.regular (condensedRingObj Λ X)) := by
  exact nonempty_iso_trans
    (tensor_of_projectors Λ k heval hprod hunit X ψ ψ⁻¹ f)
    (nonempty_iso_trans ⟨sheafOfPullbackIso Λ k X (ψ * ψ⁻¹) f⟩
      (pullback_regular_iso Λ
        (AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit.{u + 1} ↦ f))
        (by simpa only [mul_inv_cancel] using
          (image_unit Λ k heval hprod hunit).map Iso.symm)))

private theorem cover_of_evaluations
    (heval : ∀ ψ : AddChar k (MonObj.Γ Λ),
      IsIso ((CondensedRing.upperStar Λ q).map (image.ι (e ψ).asHom) ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app
          (Mod.regular (condensedRingObj Λ A))))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (ψ : AddChar k (MonObj.Γ Λ)) (f : Γ(X, ⊤)) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : U.I₀,
      Nonempty ((CondensedRing.upperStar Λ (U.f i)).obj
        (condensedArtinSchreierSheafOf Λ k X ψ f) ≅
          Mod.regular (condensedRingObj Λ (U.X i))) := by
  have : AlgebraicGeometry.Etale q := Etale.etale_artinSchreierMap (k := k)
  have := heval ψ
  exact rankOne_cover_of_iso Λ (sheafOfPullbackIso Λ k X ψ f)
    (rankOne_cover_pullback Λ q (AffineSpace.surjective_artinSchreierMap k)
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit.{u + 1} ↦ f))
      (condensedArtinSchreierSheaf Λ k ψ)
      ⟨asIso ((CondensedRing.upperStar Λ q).map (image.ι (e ψ).asHom) ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app
          (Mod.regular (condensedRingObj Λ A)))⟩)

private theorem lisse_of_rankOne_cover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : V.I₀,
      Nonempty ((CondensedRing.upperStar Λ (V.f i)).obj M ≅
        Mod.regular (condensedRingObj Λ (V.X i)))) : IsLisseCoefficientModule Λ M := by
  obtain ⟨V, hV⟩ := h
  refine ⟨V, fun i ↦ ?_⟩
  obtain ⟨el⟩ := hV i
  exact free_of_regularIso el

/-- Counit trivializations and multiplication fixed by the target projector imply all
local rank-one, character tensor-product, inverse and Tor assertions for every function.

Source: latest blueprint `prop-kernel-lisse.proof.md`, descent and flatness paragraphs
(blueprint: lem-kernel-condensed-projector-descent).

Proof. The Artin–Schreier map is an etale surjection, hence a proetale singleton cover.
Restriction to this cover detects isomorphisms on underlying sheaves, and module
forgetful functors reflect them. The counit identifies each pulled-back image with the
regular module. The monoidal-adjunction argument identifies the pullback of the product
of two image inclusions with the tensor product of these counit identifications, so the
fixed-point equation makes the induced map to the product-character image invertible.
The same argument applied to constant functions gives the trivial-character unit.
Pull these isomorphisms back along the map defined by the function. Pulling the singleton
cover back gives an explicit trivializing cover, and a regular module is free of rank one.
Apply character multiplication to the inverse character and the trivial-character unit
to obtain a tensor inverse. Tensor invertibility implies flatness; a flat object in degree
zero has Tor amplitude [0,0]. Empty schemes and trivial characters are included. -/
theorem condensedArtinSchreier_properties_of_projectors
    (heval : ∀ ψ : AddChar k (MonObj.Γ Λ),
      IsIso ((CondensedRing.upperStar Λ q).map (image.ι (e ψ).asHom) ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app
          (Mod.regular (condensedRingObj Λ A))))
    (hprod : ∀ ψ ψ' : AddChar k (MonObj.Γ Λ),
      ((image.ι (e ψ).asHom ⊗ₘ image.ι (e ψ').asHom) ≫
        Functor.LaxMonoidal.μ G (Mod.regular (condensedRingObj Λ A))
          (Mod.regular (condensedRingObj Λ A)) ≫
        (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A))) ≫
          (e (ψ * ψ')).asHom =
      (image.ι (e ψ).asHom ⊗ₘ image.ι (e ψ').asHom) ≫
        Functor.LaxMonoidal.μ G (Mod.regular (condensedRingObj Λ A))
          (Mod.regular (condensedRingObj Λ A)) ≫
        (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A)))
    (hunit : Functor.LaxMonoidal.ε G ≫ (e 1).asHom = Functor.LaxMonoidal.ε G)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (ψ ψ' : AddChar k (MonObj.Γ Λ)) (f : Γ(X, ⊤)) :
    IsLisseCoefficientModule Λ (condensedArtinSchreierSheafOf Λ k X ψ f) ∧
      (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : U.I₀,
        Nonempty ((CondensedRing.upperStar Λ (U.f i)).obj
          (condensedArtinSchreierSheafOf Λ k X ψ f) ≅
            Mod.regular (condensedRingObj Λ (U.X i)))) ∧
      Nonempty (condensedArtinSchreierSheafOf Λ k X ψ f ⊗
          condensedArtinSchreierSheafOf Λ k X ψ' f ≅
        condensedArtinSchreierSheafOf Λ k X (ψ * ψ') f) ∧
      Nonempty (condensedArtinSchreierSheafOf Λ k X ψ f ⊗
          condensedArtinSchreierSheafOf Λ k X ψ⁻¹ f ≅
        Mod.regular (condensedRingObj Λ X)) ∧
      _root_.DerivedCategory.torAmplitudeIn
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) 0 0
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (condensedArtinSchreierSheafOf Λ k X ψ f)) := by
  have hc := cover_of_evaluations Λ k heval X ψ f
  obtain ⟨ei⟩ := inverse_of_projectors Λ k heval hprod hunit X ψ f
  exact ⟨lisse_of_rankOne_cover Λ _ hc, hc,
    tensor_of_projectors Λ k heval hprod hunit X ψ ψ' f, ⟨ei⟩,
    _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
      (flat_of_regularTensorIso ei)⟩

end AlgebraicGeometry.ProEtale
