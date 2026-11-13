import Langlands.AlgebraicGeometry.Picard.ArtinianResidueSheaf
import Langlands.AlgebraicGeometry.Picard.AffineBaseChangeKernel
import Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomologyNaturalityStatement
import Langlands.AlgebraicGeometry.Deformation.ArtinianSurjectionTests

/-! # Residue-product coordinates for the actual elementary ideal sheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology.OriginalResidueProduct

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest ArtinianTest.ElementaryKernel
open PicardGroupoid.ArtinianResidueSheaf
open Langlands.Scheme.Modules.BasisHomGluing
open Langlands.Scheme.Modules.OpenCoverHomGluing

variable {R S : Type u} [CommRing R] [CommRing S]
  (φ : R →+* S) [IsLocalRing S]
  (X : Over (Spec (CommRingCat.of R)))

/-- The actual residue immersion into the original total space. -/
abbrev residueInclusion :
    ((residuePullback φ).obj X).left ⟶ X.left :=
  pullback.fst X.hom (residueBaseMap φ)

/-- The residue structure module on the original total space. -/
abbrev residueStructure : X.left.Modules :=
  (Scheme.Modules.pushforward (residueInclusion φ X)).obj
    (SheafOfModules.unit ((residuePullback φ).obj X).left.ringCatSheaf)

/-- The base ring acts through the actual structure morphism. -/
abbrev sourceSectionHom (U : X.left.Opens) : R →+* Γ(X.left, U) :=
  Langlands.AlgebraicGeometry.Modules.AdicStalkQuotient.baseSectionHom X.hom U

/-- The residue field acts through the actual residue-fibre projection. -/
def residueSectionHom (V : ((residuePullback φ).obj X).left.Opens) :
    IsLocalRing.ResidueField S →+* Γ(((residuePullback φ).obj X).left, V) :=
  ((pullback.snd X.hom (residueBaseMap φ)).appLE ⊤ V le_top).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S))).inv.hom

@[instance_reducible]
def residueSectionAlgebra (V : ((residuePullback φ).obj X).left.Opens) :
    Algebra (IsLocalRing.ResidueField S)
      Γ(((residuePullback φ).obj X).left, V) :=
  (residueSectionHom φ X V).toAlgebra

@[instance_reducible]
def sourceSectionAlgebra (U : X.left.Opens) : Algebra R Γ(X.left, U) :=
  (sourceSectionHom X U).toAlgebra

@[instance_reducible]
def residueSourceAlgebra (U : X.left.Opens) :
    Algebra Γ(X.left, U)
      Γ(((residuePullback φ).obj X).left, residueInclusion φ X ⁻¹ᵁ U) :=
  ((residueInclusion φ X).app U).hom.toAlgebra

attribute [local instance] residueSectionAlgebra sourceSectionAlgebra residueSourceAlgebra

lemma sourceSectionHom_res {U V : X.left.Opens} (h : V ≤ U) (a : R) :
    X.left.presheaf.map (homOfLE h).op (sourceSectionHom X U a) =
      sourceSectionHom X V a := by
  unfold sourceSectionHom Langlands.AlgebraicGeometry.Modules.AdicStalkQuotient.baseSectionHom
  change ((X.hom.appLE ⊤ U le_top ≫ X.left.presheaf.map (homOfLE h).op)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) = _
  rw [Scheme.Hom.appLE_map]
  rfl

lemma residueSectionHom_res
    {U V : ((residuePullback φ).obj X).left.Opens} (h : V ≤ U)
    (c : IsLocalRing.ResidueField S) :
    ((residuePullback φ).obj X).left.presheaf.map (homOfLE h).op
      (residueSectionHom φ X U c) = residueSectionHom φ X V c := by
  unfold residueSectionHom
  change (((pullback.snd X.hom (residueBaseMap φ)).appLE ⊤ U le_top ≫
    (pullback X.hom (residueBaseMap φ)).presheaf.map (homOfLE h).op)
      ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S))).inv c)) = _
  rw [Scheme.Hom.appLE_map]
  rfl

def residueSectionRestriction
    {U V : ((residuePullback φ).obj X).left.Opens} (h : V ≤ U) :
    Γ(((residuePullback φ).obj X).left, U) →ₐ[IsLocalRing.ResidueField S]
      Γ(((residuePullback φ).obj X).left, V) :=
  { (((residuePullback φ).obj X).left.presheaf.map (homOfLE h).op).hom with
    commutes' := residueSectionHom_res φ X h }

/-- Affine residue sections form the actual algebraic pushout. -/
lemma affineSections_isPushout (U : X.left.Opens) (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom ((IsLocalRing.residue S).comp φ))
      (CommRingCat.ofHom (sourceSectionHom X U))
      (CommRingCat.ofHom (residueSectionHom φ X (residueInclusion φ X ⁻¹ᵁ U)))
      ((residueInclusion φ X).app U) := by
  let i := residueInclusion φ X
  let p := pullback.snd X.hom (residueBaseMap φ)
  have H := IsPullback.of_hasPullback X.hom (residueBaseMap φ)
  have hUY : i ⁻¹ᵁ U = i ⁻¹ᵁ U ⊓ p ⁻¹ᵁ ⊤ := by simp
  have h1 := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    le_top le_top hUY (isAffineOpen_top (Spec (CommRingCat.of R)))
    (isAffineOpen_top (Spec (CommRingCat.of (IsLocalRing.ResidueField S)))) hU
  have h2 := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U)
    le_top le_top hUY).mp h1
  apply h2.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of R))
    (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S)))
    (Iso.refl _) (Iso.refl _)
  · change (residueBaseMap φ).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S))).hom = _
    exact Scheme.ΓSpecIso_naturality _
  · ext a
    change X.hom.appLE ⊤ U le_top a =
      X.hom.appLE ⊤ U le_top
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv
          ((Scheme.ΓSpecIso (CommRingCat.of R)).hom a))
    simp
  · ext a
    change p.appLE ⊤ (i ⁻¹ᵁ U) le_top a =
      p.appLE ⊤ (i ⁻¹ᵁ U) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S))).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S))).hom a))
    simp
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (residueInclusion φ X).appLE_eq_app

section Algebra

variable [Algebra R S]

local notation "φ₀" => algebraMap R S

local instance : Module R (IsLocalRing.ResidueField S) :=
  (IsLocalRing.ResidueField.algebra S (R₀ := R)).toModule

/-- The algebraic residue fibre ring is the actual residue-fibre affine section ring. -/
def affineSectionsEquiv (U : X.left.Opens) (hU : IsAffineOpen U) :
    IsLocalRing.ResidueField S ⊗[R] Γ(X.left, U) ≃ₐ[IsLocalRing.ResidueField S]
      Γ(((residuePullback φ₀).obj X).left, residueInclusion φ₀ X ⁻¹ᵁ U) := by
  let T := Γ(X.left, U)
  let V := Γ(((residuePullback φ₀).obj X).left, residueInclusion φ₀ X ⁻¹ᵁ U)
  let : Algebra R V :=
    ((residueSectionHom φ₀ X (residueInclusion φ₀ X ⁻¹ᵁ U)).comp
      ((IsLocalRing.residue S).comp φ₀)).toAlgebra
  let : IsScalarTower R (IsLocalRing.ResidueField S) V :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R T V :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (affineSections_isPushout φ₀ X U hU).w)
  let : Algebra.IsPushout R (IsLocalRing.ResidueField S) T V :=
    CommRingCat.isPushout_iff_isPushout.mp (affineSections_isPushout φ₀ X U hU)
  exact Algebra.IsPushout.equiv R (IsLocalRing.ResidueField S) T V

@[simp]
lemma affineSectionsEquiv_tmul (U : X.left.Opens) (hU : IsAffineOpen U)
    (c : IsLocalRing.ResidueField S) (r : Γ(X.left, U)) :
    affineSectionsEquiv (S := S) X U hU (c ⊗ₜ[R] r) =
      residueSectionHom φ₀ X (residueInclusion φ₀ X ⁻¹ᵁ U) c *
        (residueInclusion φ₀ X).app U r := rfl

@[simp]
lemma affineSectionsEquiv_one_tmul (U : X.left.Opens) (hU : IsAffineOpen U)
    (r : Γ(X.left, U)) :
    affineSectionsEquiv (S := S) X U hU ((1 : IsLocalRing.ResidueField S) ⊗ₜ[R] r) =
      (residueInclusion φ₀ X).app U r := by
  rw [affineSectionsEquiv_tmul, map_one, one_mul]


/-- Restriction as a map of algebras over the original source. -/
def sectionRestriction {U V : X.left.Opens} (h : V ≤ U) :
    Γ(X.left, U) →ₐ[R] Γ(X.left, V) :=
  { (X.left.presheaf.map (homOfLE h).op).hom with
    commutes' := sourceSectionHom_res X h }

local instance (U : X.left.Opens) :
    Algebra Γ(X.left, U) (IsLocalRing.ResidueField S ⊗[R] Γ(X.left, U)) :=
  Algebra.TensorProduct.rightAlgebra

/-- Restriction on the algebraic residue fibre. -/
def fibreRestriction {U V : X.left.Opens} (h : V ≤ U) :
    IsLocalRing.ResidueField S ⊗[R] Γ(X.left, U) →ₐ[IsLocalRing.ResidueField S]
      IsLocalRing.ResidueField S ⊗[R] Γ(X.left, V) :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (sectionRestriction X h)

/-- The affine fibre-section equivalence commutes with actual restriction. -/
lemma affineSectionsEquiv_res
    {U V : X.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (t : IsLocalRing.ResidueField S ⊗[R] Γ(X.left, U)) :
    residueSectionRestriction φ₀ X
        (((Opens.map (residueInclusion φ₀ X).base).map (homOfLE h)).le) (affineSectionsEquiv (S := S) X U hU t) =
      affineSectionsEquiv (S := S) X V hV (fibreRestriction (S := S) X h t) := by
  induction t using TensorProduct.inductionOn with
  | tmul c r =>
    change ((residuePullback φ₀).obj X).left.presheaf.map
        ((Opens.map (residueInclusion φ₀ X).base).map (homOfLE h)).op
        (affineSectionsEquiv (S := S) X U hU (c ⊗ₜ[R] r)) =
      affineSectionsEquiv (S := S) X V hV
        (c ⊗ₜ[R] (sectionRestriction X h r))
    rw [affineSectionsEquiv_tmul, affineSectionsEquiv_tmul, map_mul,
      Opens.map_homOfLE, residueSectionHom_res]
    congr 1
    change ((residuePullback φ₀).obj X).left.presheaf.map
        (homOfLE _).op ((residueInclusion φ₀ X).app U r) =
      (residueInclusion φ₀ X).app V
        (X.left.presheaf.map (homOfLE h).op r)
    simpa only [ConcreteCategory.comp_apply, Quiver.Hom.unop_op, Opens.map_homOfLE] using
      (congrArg (fun m => m r) ((residueInclusion φ₀ X).naturality (homOfLE h).op)).symm
  | add a b ha hb =>
    simpa only [map_add (affineSectionsEquiv (S := S) X U hU),
      map_add (affineSectionsEquiv (S := S) X V hV), map_add (residueSectionRestriction φ₀ X _),
      map_add (fibreRestriction (S := S) X h)] using congrArg₂ (· + ·) ha hb

/-- Flatness of the actual source-ring map on an affine open. -/
lemma sourceSectionHom_flat [Flat X.hom] (U : X.left.Opens) (hU : IsAffineOpen U) :
    (sourceSectionHom X U).Flat := by
  exact (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv)).comp
        (X.hom.flat_appLE (isAffineOpen_top (Spec (CommRingCat.of R))) hU le_top)


/-- The actual elementary kernel with its descended residue-field action. -/
@[instance_reducible]
def kernelResidueModule [IsLocalRing R] [IsArtinianRing R] [IsArtinianRing S]
    [hs : Fact (Function.Surjective (algebraMap R S))]
    [he : Fact (IsLocalRing.maximalIdeal R * RingHom.ker (algebraMap R S) = ⊥)] :
    Module (IsLocalRing.ResidueField S) (RingHom.ker (algebraMap R S)) :=
  ElementaryKernel.residueModule
    (ArtinianSurjectionTests.arrow (R := R) (S := S) hs.out)
    (ArtinianSurjectionTests.arrow_isElementary (R := R) (S := S) hs.out he.out)

attribute [local instance] kernelResidueModule


variable [IsLocalRing R] [IsArtinianRing R] [IsArtinianRing S]
  [hs : Fact (Function.Surjective (algebraMap R S))]
  [he : Fact (IsLocalRing.maximalIdeal R * RingHom.ker (algebraMap R S) = ⊥)]

local notation "K" => IsLocalRing.ResidueField S


local instance : IsScalarTower R K (RingHom.ker φ₀) :=
  IsScalarTower.of_algebraMap_smul
    (ElementaryKernel.augmentation_smul
      (ArtinianSurjectionTests.arrow (R := R) (S := S) hs.out)
      (ArtinianSurjectionTests.arrow_isElementary hs.out he.out))

/-- The affine-section kernel is the fibre coefficient tensor of the actual kernel. -/
def affineKernelEquiv [Flat X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U) :
    (K ⊗[R] Γ(X.left, U)) ⊗[K] (RingHom.ker φ₀)
      ≃ₗ[Γ(X.left, U)] Γ(ideal φ₀ X, U) := by
  let : Module.Flat R Γ(X.left, U) := sourceSectionHom_flat X U hU
  exact (ElementaryKernelTensor.coefficientTensorEquiv (A := R)).trans
    ((ElementaryKernelTensor.idealTensorEquiv (RingHom.ker φ₀)).trans
      (LinearEquiv.ofEq _ _ (AffineBaseChangeKernel.affine_ker φ₀ X.hom hs.out U hU).symm))

@[simp]
lemma affineKernelEquiv_tmul [Flat X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (c : K) (r : Γ(X.left, U)) (x : RingHom.ker φ₀) :
    (affineKernelEquiv (S := S) X U hU ((c ⊗ₜ[R] r) ⊗ₜ[K] x)).val =
      sourceSectionHom X U (c • x).val * r := by
  let : Module.Flat R Γ(X.left, U) := sourceSectionHom_flat X U hU
  change (ElementaryKernelTensor.idealTensorEquiv (RingHom.ker φ₀)
    (r ⊗ₜ[R] (c • x))).val = _
  exact ElementaryKernelTensor.idealTensorEquiv_tmul (RingHom.ker φ₀) r (c • x)

@[simp]
lemma affineKernelEquiv_one_tmul [Flat X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (r : Γ(X.left, U)) (x : (RingHom.ker φ₀)) :
    (affineKernelEquiv (S := S) X U hU ((1 ⊗ₜ[R] r) ⊗ₜ[K] x)).val =
      sourceSectionHom X U x.val * r := by
  simpa only [one_smul] using affineKernelEquiv_tmul (S := S) X U hU (1 : K) r x

/-- The affine tensor comparison commutes with the actual ideal-module restriction. -/
lemma affineKernelEquiv_res [Flat X.hom]
    {U V : X.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (t : (K ⊗[R] Γ(X.left, U)) ⊗[K]
      (RingHom.ker φ₀)) :
    (ideal φ₀ X).presheaf.map (homOfLE h).op (affineKernelEquiv (S := S) X U hU t) =
      affineKernelEquiv (S := S) X V hV
        (TensorProduct.map (fibreRestriction (S := S) X h).toLinearMap LinearMap.id t) := by
  induction t using TensorProduct.inductionOn with
  | tmul y x =>
    induction y using TensorProduct.inductionOn with
    | tmul c r =>
      apply Subtype.ext
      change X.left.presheaf.map (homOfLE h).op
          (affineKernelEquiv (S := S) X U hU ((c ⊗ₜ[R] r) ⊗ₜ[K] x)).val =
        (affineKernelEquiv (S := S) X V hV
          ((c ⊗ₜ[R] (sectionRestriction X h r)) ⊗ₜ[K] x)).val
      rw [affineKernelEquiv_tmul, affineKernelEquiv_tmul, map_mul, sourceSectionHom_res]
      rfl
    | add a b ha hb =>
      simpa only [TensorProduct.add_tmul, LinearEquiv.map_add, LinearMap.map_add,
        map_add ((ideal φ₀ X).presheaf.map (homOfLE h).op).hom]
        using congrArg₂ (· + ·) ha hb
  | add a b ha hb =>
    simpa only [LinearEquiv.map_add, LinearMap.map_add,
      map_add ((ideal φ₀ X).presheaf.map (homOfLE h).op).hom]
      using congrArg₂ (· + ·) ha hb

local notation "i" => residueInclusion φ₀ X

omit [IsLocalRing R] [IsArtinianRing R] [IsArtinianRing S] hs he in
/-- The canonical affine residue-section comparison preserves the actual source action. -/
lemma affineSectionsEquiv_smul
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (r : Γ(X.left, U))
    (t : K ⊗[R] Γ(X.left, U)) :
    affineSectionsEquiv (S := S) X U hU (r • t) = r • affineSectionsEquiv (S := S) X U hU t := by
  change affineSectionsEquiv (S := S) X U hU (((1 : K) ⊗ₜ[R] r) * t) =
    (i).app U r * affineSectionsEquiv (S := S) X U hU t
  rw [map_mul, affineSectionsEquiv_one_tmul]

/-- Tensor the actual affine residue-section equivalence with the unchanged kernel. -/
def coefficientSectionsEquiv
    (U : X.left.Opens) (hU : IsAffineOpen U) :
    (K ⊗[R] Γ(X.left, U)) ⊗[K] (RingHom.ker φ₀)
      ≃ₗ[Γ(X.left, U)]
        Γ(((residuePullback φ₀).obj X).left, i ⁻¹ᵁ U) ⊗[K] (RingHom.ker φ₀) :=
  { (TensorProduct.congr (affineSectionsEquiv (S := S) X U hU).toLinearEquiv
      (LinearEquiv.refl K ((RingHom.ker φ₀)))).toAddEquiv with
    map_smul' := by
      intro r t
      change (TensorProduct.congr (affineSectionsEquiv (S := S) X U hU).toLinearEquiv
          (LinearEquiv.refl K ((RingHom.ker φ₀)))) (r • t) =
        r • (TensorProduct.congr (affineSectionsEquiv (S := S) X U hU).toLinearEquiv
          (LinearEquiv.refl K ((RingHom.ker φ₀)))) t
      induction t using TensorProduct.inductionOn with
      | tmul y x =>
        change affineSectionsEquiv (S := S) X U hU (r • y) ⊗ₜ[K] x =
          (r • affineSectionsEquiv (S := S) X U hU y) ⊗ₜ[K] x
        rw [affineSectionsEquiv_smul]
      | add a b ha hb =>
        simpa only [smul_add, LinearEquiv.map_add] using congrArg₂ (· + ·) ha hb }

@[simp]
lemma coefficientSectionsEquiv_tmul
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (y : K ⊗[R] Γ(X.left, U))
    (x : (RingHom.ker φ₀)) :
    coefficientSectionsEquiv (S := S) X U hU (y ⊗ₜ[K] x) =
      affineSectionsEquiv (S := S) X U hU y ⊗ₜ[K] x := rfl

/-- The coefficient-section comparison commutes with actual restriction. -/
lemma coefficientSectionsEquiv_res
    {U V : X.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (t : (K ⊗[R] Γ(X.left, U)) ⊗[K]
      (RingHom.ker φ₀)) :
    TensorProduct.map
        (residueSectionRestriction φ₀ X
          (((Opens.map (i).base).map (homOfLE h)).le)).toLinearMap LinearMap.id
        (coefficientSectionsEquiv (S := S) X U hU t) =
      coefficientSectionsEquiv (S := S) X V hV
        (TensorProduct.map (fibreRestriction (S := S) X h).toLinearMap LinearMap.id t) := by
  induction t using TensorProduct.inductionOn with
  | tmul y x =>
    change residueSectionRestriction φ₀ X _ (affineSectionsEquiv (S := S) X U hU y) ⊗ₜ[K] x =
      affineSectionsEquiv (S := S) X V hV (fibreRestriction (S := S) X h y) ⊗ₜ[K] x
    rw [affineSectionsEquiv_res]
  | add a b ha hb =>
    simpa only [LinearEquiv.map_add, LinearMap.map_add]
      using congrArg₂ (· + ·) ha hb

/-- Actual residue-fibre coefficients give the actual elementary ideal sections. -/
def affineKernelResidueEquiv [Flat X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U) :
    Γ(((residuePullback φ₀).obj X).left, i ⁻¹ᵁ U) ⊗[K] (RingHom.ker φ₀)
      ≃ₗ[Γ(X.left, U)] Γ(ideal φ₀ X, U) :=
  (coefficientSectionsEquiv (S := S) X U hU).symm.trans (affineKernelEquiv (S := S) X U hU)

@[simp]
lemma affineKernelResidueEquiv_coefficientSectionsEquiv [Flat X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (t : (K ⊗[R] Γ(X.left, U)) ⊗[K]
      (RingHom.ker φ₀)) :
    affineKernelResidueEquiv (S := S) X U hU (coefficientSectionsEquiv (S := S) X U hU t) =
      affineKernelEquiv (S := S) X U hU t := by
  exact congrArg (affineKernelEquiv (S := S) X U hU)
    ((coefficientSectionsEquiv (S := S) X U hU).symm_apply_apply t)

/-- A coefficient from an actual source section has its expected ideal product. -/
@[simp]
lemma affineKernelResidueEquiv_one_tmul [Flat X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (r : Γ(X.left, U)) (x : (RingHom.ker φ₀)) :
    (affineKernelResidueEquiv (S := S) X U hU ((i).app U r ⊗ₜ[K] x)).val =
      sourceSectionHom X U x.val * r := by
  rw [← affineSectionsEquiv_one_tmul (S := S) X U hU r,
    ← coefficientSectionsEquiv_tmul, affineKernelResidueEquiv_coefficientSectionsEquiv]
  exact affineKernelEquiv_one_tmul (S := S) X U hU r x

/-- The actual residue-fibre kernel comparison commutes with ideal restriction. -/
lemma affineKernelResidueEquiv_res [Flat X.hom]
    {U V : X.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (t : Γ(((residuePullback φ₀).obj X).left, i ⁻¹ᵁ U) ⊗[K]
      (RingHom.ker φ₀)) :
    (ideal φ₀ X).presheaf.map (homOfLE h).op (affineKernelResidueEquiv (S := S) X U hU t) =
      affineKernelResidueEquiv (S := S) X V hV
        (TensorProduct.map
          (residueSectionRestriction φ₀ X
            (((Opens.map (i).base).map (homOfLE h)).le)).toLinearMap LinearMap.id t) := by
  obtain ⟨s, rfl⟩ := (coefficientSectionsEquiv (S := S) X U hU).surjective t
  rw [coefficientSectionsEquiv_res (S := S) X h hU hV,
    affineKernelResidueEquiv_coefficientSectionsEquiv,
    affineKernelResidueEquiv_coefficientSectionsEquiv]
  exact affineKernelEquiv_res (S := S) X h hU hV s


/-- A finite product of the actual residue-fibre structure module, pushed to `X_A`. -/
def residueProductModule (ι : Type u) :
    X.left.Modules :=
  ∏ᶜ fun _ : ι => residueStructure φ₀ X

/-- Actual product-sheaf sections are tuples of actual residue sections. -/
def residueProductSectionsEquiv (ι : Type u)
    (U : X.left.Opens) :
    Γ(residueProductModule (S := S) X ι, U)
      ≃ₗ[Γ(X.left, U)]
        (ι → Γ(((residuePullback φ₀).obj X).left, i ⁻¹ᵁ U)) :=
  (productSectionsIso (residueStructure φ₀ X) ι U).toLinearEquiv

omit [IsLocalRing R] [IsArtinianRing R] [IsArtinianRing S] hs he in
lemma residueProductSectionsEquiv_res (ι : Type u)
    {U V : X.left.Opens} (h : V ≤ U)
    (s : Γ(residueProductModule (S := S) X ι, U)) (j : ι) :
    residueProductSectionsEquiv (S := S) X ι V
        ((residueProductModule (S := S) X ι).presheaf.map (homOfLE h).op s) j =
      residueSectionRestriction φ₀ X
        (((Opens.map (i).base).map (homOfLE h)).le)
          (residueProductSectionsEquiv (S := S) X ι U s j) :=
  productSectionsIso_res (residueStructure φ₀ X) ι h s j

variable {ι : Type u} [Finite ι] (b : Module.Basis ι (IsLocalRing.ResidueField S) (RingHom.ker (algebraMap R S)))

/-- Tensor coordinates, retaining the actual source-section scalar action. -/
def residueTensorCoordinates
    (U : X.left.Opens) :
    Γ(((residuePullback φ₀).obj X).left, i ⁻¹ᵁ U) ⊗[K] (RingHom.ker φ₀)
      ≃ₗ[Γ(X.left, U)]
        (ι → Γ(((residuePullback φ₀).obj X).left, i ⁻¹ᵁ U)) :=
  (tensorCoordinates b
    Γ(((residuePullback φ₀).obj X).left, i ⁻¹ᵁ U)).restrictScalars _

/-- The product sheaf presents the actual tensor coefficients on every open. -/
def productTensorEquiv
    (U : X.left.Opens) :
    Γ(residueProductModule (S := S) X ι, U)
      ≃ₗ[Γ(X.left, U)]
        Γ(((residuePullback φ₀).obj X).left, i ⁻¹ᵁ U) ⊗[K] (RingHom.ker φ₀) :=
  (residueProductSectionsEquiv (S := S) X ι U).trans (residueTensorCoordinates (S := S) X b U).symm

@[simp]
lemma residueTensorCoordinates_productTensorEquiv
    (U : X.left.Opens)
    (s : Γ(residueProductModule (S := S) X ι, U)) :
    residueTensorCoordinates (S := S) X b U (productTensorEquiv (S := S) X b U s) =
      residueProductSectionsEquiv (S := S) X ι U s :=
  (residueTensorCoordinates (S := S) X b U).apply_symm_apply _

lemma residueTensorCoordinates_res
    {U V : X.left.Opens} (h : V ≤ U)
    (t : Γ(((residuePullback φ₀).obj X).left, i ⁻¹ᵁ U) ⊗[K] (RingHom.ker φ₀))
    (j : ι) :
    residueTensorCoordinates (S := S) X b V
        (TensorProduct.map
          (residueSectionRestriction φ₀ X
            (((Opens.map (i).base).map (homOfLE h)).le)).toLinearMap LinearMap.id t) j =
      residueSectionRestriction φ₀ X
        (((Opens.map (i).base).map (homOfLE h)).le)
          (residueTensorCoordinates (S := S) X b U t j) :=
  tensorCoordinates_map b _
    (residueSectionRestriction φ₀ X (((Opens.map (i).base).map (homOfLE h)).le)) t j

/-- The tensor presentation respects the actual restriction maps. -/
lemma productTensorEquiv_res
    {U V : X.left.Opens} (h : V ≤ U)
    (s : Γ(residueProductModule (S := S) X ι, U)) :
    TensorProduct.map
        (residueSectionRestriction φ₀ X
          (((Opens.map (i).base).map (homOfLE h)).le)).toLinearMap LinearMap.id
          (productTensorEquiv (S := S) X b U s) =
      productTensorEquiv (S := S) X b V
        ((residueProductModule (S := S) X ι).presheaf.map (homOfLE h).op s) := by
  apply (residueTensorCoordinates (S := S) X b V).injective
  ext j
  rw [residueTensorCoordinates_res (S := S) X b h, residueTensorCoordinates_productTensorEquiv,
    residueTensorCoordinates_productTensorEquiv]
  exact (residueProductSectionsEquiv_res (S := S) X ι h s j).symm

variable [Flat X.hom]

/-- On an affine open the residue product is the actual elementary ideal module. -/
def affineProductIdealEquiv
    (U : X.left.Opens) (hU : IsAffineOpen U) :
    Γ(residueProductModule (S := S) X ι, U)
      ≃ₗ[Γ(X.left, U)] Γ(ideal φ₀ X, U) :=
  (productTensorEquiv (S := S) X b U).trans (affineKernelResidueEquiv (S := S) X U hU)

lemma affineProductIdealEquiv_res
    {U V : X.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (s : Γ(residueProductModule (S := S) X ι, U)) :
    (ideal φ₀ X).presheaf.map (homOfLE h).op
        (affineProductIdealEquiv (S := S) X b U hU s) =
      affineProductIdealEquiv (S := S) X b V hV
        ((residueProductModule (S := S) X ι).presheaf.map (homOfLE h).op s) := by
  simp only [affineProductIdealEquiv, LinearEquiv.trans_apply]
  rw [affineKernelResidueEquiv_res, productTensorEquiv_res]

lemma affineProductIdealEquiv_symm_res
    {U V : X.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (s : Γ(ideal φ₀ X, U)) :
    (residueProductModule (S := S) X ι).presheaf.map (homOfLE h).op
        ((affineProductIdealEquiv (S := S) X b U hU).symm s) =
      (affineProductIdealEquiv (S := S) X b V hV).symm
        ((ideal φ₀ X).presheaf.map (homOfLE h).op s) := by
  apply (affineProductIdealEquiv (S := S) X b V hV).injective
  rw [← affineProductIdealEquiv_res (S := S) X b h hU hV, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

omit [Flat X.hom] [IsLocalRing R] [IsArtinianRing R] in
private lemma affineBasis
    (y : X.left)
    (U : X.left.Opens) (hy : y ∈ U) :
    ∃ V, IsAffineOpen V ∧ y ∈ V ∧ V ≤ U :=
  exists_isAffineOpen_mem_and_subset hy

/-- Glue the affine coefficient maps into a morphism of actual module sheaves. -/
def productToIdeal : residueProductModule (S := S) X ι ⟶ ideal φ₀ X :=
  Langlands.Scheme.Modules.BasisHomGluing.hom (affineBasis X)
    (fun U hU => (affineProductIdealEquiv (S := S) X b U hU).toLinearMap)
    (fun _ _ hU hV h s => affineProductIdealEquiv_res (S := S) X b h hU hV s)

/-- Glue the inverse affine coefficient maps. -/
def idealToProduct : ideal φ₀ X ⟶ residueProductModule (S := S) X ι :=
  Langlands.Scheme.Modules.BasisHomGluing.hom (affineBasis X)
    (fun U hU => (affineProductIdealEquiv (S := S) X b U hU).symm.toLinearMap)
    (fun _ _ hU hV h s => affineProductIdealEquiv_symm_res (S := S) X b h hU hV s)

lemma productToIdeal_app
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (s : Γ(residueProductModule (S := S) X ι, U)) :
    (productToIdeal (S := S) X b).app U s = affineProductIdealEquiv (S := S) X b U hU s :=
  hom_app_basis (affineBasis X) _ _ U hU s

lemma idealToProduct_app
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (s : Γ(ideal φ₀ X, U)) :
    (idealToProduct (S := S) X b).app U s = (affineProductIdealEquiv (S := S) X b U hU).symm s :=
  hom_app_basis (affineBasis X) _ _ U hU s

/-- A chosen finite kernel basis identifies the actual ideal sheaf with residue products. -/
def residueProductIdealIso : residueProductModule (S := S) X ι ≅ ideal φ₀ X where
  hom := productToIdeal (S := S) X b
  inv := idealToProduct (S := S) X b
  hom_inv_id := by
    apply hom_ext_of_basis (affineBasis X)
    intro U hU
    ext s
    change (idealToProduct (S := S) X b).app U ((productToIdeal (S := S) X b).app U s) = s
    rw [productToIdeal_app (S := S) X b U hU, idealToProduct_app (S := S) X b U hU]
    exact (affineProductIdealEquiv (S := S) X b U hU).symm_apply_apply s
  inv_hom_id := by
    apply hom_ext_of_basis (affineBasis X)
    intro U hU
    ext s
    change (productToIdeal (S := S) X b).app U ((idealToProduct (S := S) X b).app U s) = s
    rw [idealToProduct_app (S := S) X b U hU, productToIdeal_app (S := S) X b U hU]
    exact (affineProductIdealEquiv (S := S) X b U hU).apply_symm_apply s


section LiftFormula

variable [Fintype ι]

omit [Flat X.hom] in
/-- Tensor coefficients are the finite sum given by the fixed kernel basis. -/
lemma productTensorEquiv_eq_sum
    (U : X.left.Opens) (s : Γ(residueProductModule (S := S) X ι, U)) :
    productTensorEquiv (S := S) X b U s =
      ∑ j, residueProductSectionsEquiv (S := S) X ι U s j ⊗ₜ[K] b j := by
  change (b.baseChange Γ(((residuePullback φ₀).obj X).left, i ⁻¹ᵁ U)).equivFun.symm
    (residueProductSectionsEquiv (S := S) X ι U s) = _
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- On affine opens a tuple of lifted coefficients gives the expected ideal sum. -/
lemma productToIdeal_app_lift_affine
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (r : ι → Γ(X.left, U)) (s : Γ(residueProductModule (S := S) X ι, U))
    (hlift : ∀ j, (Pi.π (fun _ : ι => residueStructure φ₀ X) j).app U s =
      (residueInclusion φ₀ X).app U (r j)) :
    ((productToIdeal (S := S) X b).app U s).val =
      ∑ j, sourceSectionHom X U (b j).val * r j := by
  classical
  have hj (j : ι) : residueProductSectionsEquiv (S := S) X ι U s j =
      (residueInclusion φ₀ X).app U (r j) := by
    change (productSectionsIso (residueStructure φ₀ X) ι U).hom s j = _
    rw [productSectionsIso_apply]
    exact hlift j
  rw [productToIdeal_app (S := S) X b U hU]
  change (affineKernelResidueEquiv (S := S) X U hU
    (productTensorEquiv (S := S) X b U s)).val = _
  rw [productTensorEquiv_eq_sum]
  have hsum (t : Finset ι) :
      (affineKernelResidueEquiv (S := S) X U hU
        (∑ j ∈ t, residueProductSectionsEquiv (S := S) X ι U s j ⊗ₜ[K] b j)).val =
      ∑ j ∈ t, sourceSectionHom X U (b j).val * r j := by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, LinearEquiv.map_zero]
      rfl
    | @insert j t hnot ht =>
      rw [Finset.sum_insert hnot, Finset.sum_insert hnot, LinearEquiv.map_add]
      change (affineKernelResidueEquiv (S := S) X U hU
        (residueProductSectionsEquiv (S := S) X ι U s j ⊗ₜ[K] b j)).val +
        (affineKernelResidueEquiv (S := S) X U hU
          (∑ j ∈ t, residueProductSectionsEquiv (S := S) X ι U s j ⊗ₜ[K] b j)).val = _
      rw [ht, hj, affineKernelResidueEquiv_one_tmul]
  exact hsum Finset.univ

/-- On every open, a tuple of lifted coefficients gives the expected ideal sum. -/
lemma productToIdeal_app_lift
    (U : X.left.Opens)
    (r : ι → Γ(X.left, U)) (s : Γ(residueProductModule (S := S) X ι, U))
    (hlift : ∀ j, (Pi.π (fun _ : ι => residueStructure φ₀ X) j).app U s =
      (residueInclusion φ₀ X).app U (r j)) :
    ((productToIdeal (S := S) X b).app U s).val =
      ∑ j, sourceSectionHom X U (b j).val * r j := by
  apply eq_of_basis (affineBasis X) (N := Langlands.SchemeModule.structureModule X.left)
  intro V hV hVU
  change (Langlands.SchemeModule.structureModule X.left).presheaf.map (homOfLE hVU).op
    (((productToIdeal (S := S) X b) ≫
      StructureKernelModule.kernelModuleι
        (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ₀)))).app U s) = _
  rw [hom_map_app]
  change ((productToIdeal (S := S) X b).app V
      ((residueProductModule (S := S) X ι).presheaf.map (homOfLE hVU).op s)).val =
    X.left.presheaf.map (homOfLE hVU).op
      (∑ j, sourceSectionHom X U (b j).val * r j)
  rw [productToIdeal_app_lift_affine (S := S) X b V hV
    (fun j => X.left.presheaf.map (homOfLE hVU).op (r j)) _ ?_]
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, sourceSectionHom_res]
  · intro j
    exact (hom_map_app (Pi.π (fun _ : ι => residueStructure φ₀ X) j) hVU s).symm.trans
      ((congrArg (fun t => (residueStructure φ₀ X).presheaf.map (homOfLE hVU).op t)
        (hlift j)).trans
          (hom_map_app (Langlands.Scheme.Modules.unitToPushforwardUnit
            (residueInclusion φ₀ X)) hVU (r j)))

end LiftFormula

end Algebra

end Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology.OriginalResidueProduct
