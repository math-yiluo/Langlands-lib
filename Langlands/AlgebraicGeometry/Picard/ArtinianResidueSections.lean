import Langlands.AlgebraicGeometry.Picard.ArtinianPicardKernelTensor
import Mathlib.RingTheory.IsTensorProduct

/-! # Actual affine sections of the residue fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianResidueSections

open Langlands.AlgebraicGeometry.Deformation
open ArtinianSquareZeroPicardLifting ArtinianPicardKernelTensor

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual residue-field map to sections on the residue fibre. -/
def residueSectionHom
    (V : ((relativeSpace f).obj (ArtinianTest.residueBase k K)).Opens) :
    K →+* Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), V) :=
  (((relativeProjection f).app (ArtinianTest.residueBase k K)).appLE ⊤ V le_top).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

/-- The actual residue-field algebra on sections of the residue fibre. -/
@[instance_reducible]
def residueSectionAlgebra
    (V : ((relativeSpace f).obj (ArtinianTest.residueBase k K)).Opens) :
    Algebra K Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), V) :=
  (residueSectionHom f V).toAlgebra

attribute [local instance] sectionAlgebra residueSectionAlgebra

/-- The residue-field action commutes with actual restriction of sections. -/
lemma residueSectionHom_res
    {U V : ((relativeSpace f).obj (ArtinianTest.residueBase k K)).Opens} (h : V ≤ U)
    (c : K) :
    ((relativeSpace f).obj (ArtinianTest.residueBase k K)).presheaf.map (homOfLE h).op
      (residueSectionHom f U c) = residueSectionHom f V c := by
  unfold residueSectionHom
  change ((((relativeProjection f).app (ArtinianTest.residueBase k K)).appLE ⊤ U le_top ≫
    ((relativeSpace f).obj (ArtinianTest.residueBase k K)).presheaf.map (homOfLE h).op)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) = _
  rw [Scheme.Hom.appLE_map]
  rfl

/-- Actual restriction on the residue fibre is linear over the residue field. -/
def residueSectionRestriction
    {U V : ((relativeSpace f).obj (ArtinianTest.residueBase k K)).Opens} (h : V ≤ U) :
    Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), U) →ₐ[K]
      Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), V) :=
  { (((relativeSpace f).obj (ArtinianTest.residueBase k K)).presheaf.map
      (homOfLE h).op).hom with
    commutes' := residueSectionHom_res f h }

variable (A : ArtinianTest k K)

local instance : Algebra A.algebra K := A.augmentation.toRingHom.toAlgebra

/-- The actual relative residue immersion. -/
abbrev residueMap :=
  (relativeSpace f).map (ArtinianTest.reduction A)

local notation "i" => residueMap f A

/-- The actual affine section rings form the pushout of the residue augmentation. -/
lemma affineSections_isPushout
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom A.augmentation.toRingHom)
      (CommRingCat.ofHom (testSectionHom f A U))
      (CommRingCat.ofHom (residueSectionHom f (i ⁻¹ᵁ U))) ((i).app U) := by
  let p := (relativeProjection f).app (ArtinianTest.residueBase k K)
  have H := relativeProjection_isPullback f (ArtinianTest.reduction A)
  have hUY : i ⁻¹ᵁ U = i ⁻¹ᵁ U ⊓ p ⁻¹ᵁ ⊤ := by simp
  have h1 := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    le_top le_top hUY
    (isAffineOpen_top (Spec (CommRingCat.of A.algebra)))
    (isAffineOpen_top (Spec (CommRingCat.of K))) hU
  have h2 := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U)
    le_top le_top hUY).mp h1
  apply h2.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of A.algebra))
    (Scheme.ΓSpecIso (CommRingCat.of K)) (Iso.refl _) (Iso.refl _)
  · change (Spec.map (CommRingCat.ofHom A.augmentation.toRingHom)).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom = _
    exact Scheme.ΓSpecIso_naturality _
  · ext a
    change ((relativeProjection f).app (ArtinianTest.base A)).appLE ⊤ U le_top a =
      ((relativeProjection f).app (ArtinianTest.base A)).appLE ⊤ U le_top
        ((Scheme.ΓSpecIso (CommRingCat.of A.algebra)).inv
          ((Scheme.ΓSpecIso (CommRingCat.of A.algebra)).hom a))
    simp
  · ext a
    change p.appLE ⊤ (i ⁻¹ᵁ U) le_top a =
      p.appLE ⊤ (i ⁻¹ᵁ U) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv
          ((Scheme.ΓSpecIso (CommRingCat.of K)).hom a))
    simp
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
      Scheme.Hom.appLE_eq_app]

/-- The algebraic fibre ring is canonically the actual affine residue-fibre section ring. -/
def affineSectionsEquiv
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U) :
    K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), U) ≃ₐ[K]
      Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), i ⁻¹ᵁ U) := by
  let R := Γ((relativeSpace f).obj (ArtinianTest.base A), U)
  let S := Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), i ⁻¹ᵁ U)
  let : Algebra R S := ((i).app U).hom.toAlgebra
  let : Algebra A.algebra S :=
    ((residueSectionHom f (i ⁻¹ᵁ U)).comp A.augmentation.toRingHom).toAlgebra
  let : IsScalarTower A.algebra K S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A.algebra R S :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (affineSections_isPushout f A U hU).w)
  let : Algebra.IsPushout A.algebra K R S :=
    CommRingCat.isPushout_iff_isPushout.mp (affineSections_isPushout f A U hU)
  exact Algebra.IsPushout.equiv A.algebra K R S

@[simp]
lemma affineSectionsEquiv_tmul
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (c : K) (r : Γ((relativeSpace f).obj (ArtinianTest.base A), U)) :
    affineSectionsEquiv f A U hU (c ⊗ₜ[A.algebra] r) =
      residueSectionHom f (i ⁻¹ᵁ U) c * (i).app U r := rfl

@[simp]
lemma affineSectionsEquiv_one_tmul
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (r : Γ((relativeSpace f).obj (ArtinianTest.base A), U)) :
    affineSectionsEquiv f A U hU ((1 : K) ⊗ₜ[A.algebra] r) = (i).app U r := by
  rw [affineSectionsEquiv_tmul, map_one, one_mul]

/-- The affine fibre-section equivalence commutes with actual restriction. -/
lemma affineSectionsEquiv_res
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (t : K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), U)) :
    residueSectionRestriction f
        (((Opens.map (i).base).map (homOfLE h)).le) (affineSectionsEquiv f A U hU t) =
      affineSectionsEquiv f A V hV (fibreRestriction f h t) := by
  induction t using TensorProduct.inductionOn with
  | tmul c r =>
    change ((relativeSpace f).obj (ArtinianTest.residueBase k K)).presheaf.map
        ((Opens.map (i).base).map (homOfLE h)).op
        (affineSectionsEquiv f A U hU (c ⊗ₜ[A.algebra] r)) =
      affineSectionsEquiv f A V hV
        (c ⊗ₜ[A.algebra] (sectionRestriction f A h r))
    rw [affineSectionsEquiv_tmul, affineSectionsEquiv_tmul, map_mul,
      Opens.map_homOfLE, residueSectionHom_res]
    congr 1
    change ((relativeSpace f).obj (ArtinianTest.residueBase k K)).presheaf.map
        (homOfLE _).op ((i).app U r) =
      (i).app V
        (((relativeSpace f).obj (ArtinianTest.base A)).presheaf.map (homOfLE h).op r)
    simpa only [ConcreteCategory.comp_apply, Quiver.Hom.unop_op, Opens.map_homOfLE] using
      (congrArg (fun m => m r) ((i).naturality (homOfLE h).op)).symm
  | add a b ha hb =>
    simpa only [map_add (affineSectionsEquiv f A U hU),
      map_add (affineSectionsEquiv f A V hV), map_add (residueSectionRestriction f _),
      map_add (fibreRestriction f h)] using congrArg₂ (· + ·) ha hb

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianResidueSections
