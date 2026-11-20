import Langlands.AbelianScheme.Lie
import Langlands.RingTheory.Smooth.SectionJetFiltration
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # The actual identity jet module of a group scheme -/

noncomputable section

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- The ideal power defining the identity's order-`n` neighborhood. -/
def ideal (n : ℕ) : G.X.left.IdealSheafData := G.identitySection.ker ^ (n + 1)

/-- The actual infinitesimal neighborhood of the identity. -/
def scheme (n : ℕ) : Scheme.{u} := (ideal G n).subscheme

/-- The closed immersion of the actual jet neighborhood into the group. -/
def inclusion (n : ℕ) : scheme G n ⟶ G.X.left := (ideal G n).subschemeι

/-- The structure morphism of the actual jet neighborhood. -/
def projection (n : ℕ) : scheme G n ⟶ S := inclusion G n ≫ G.X.hom

/-- Functions on the actual identity neighborhood, pushed forward to the base. -/
def module (n : ℕ) : S.Modules :=
  (Scheme.Modules.pushforward (projection G n)).obj
    (Langlands.SchemeModule.structureModule (scheme G n))

/-- Restriction of actual functions on the group to its identity neighborhood. -/
def quotientMap (n : ℕ) :
    (Scheme.Modules.pushforward G.X.hom).obj
      (Langlands.SchemeModule.structureModule G.X.left) ⟶ module G n :=
  (Scheme.Modules.pushforward G.X.hom).map
    (SheafOfModules.unitToPushforwardObjUnit (inclusion G n).toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp (inclusion G n) G.X.hom).hom.app
      (Langlands.SchemeModule.structureModule (scheme G n))

@[simp]
theorem quotientMap_app (n : ℕ) (U : S.Opens)
    (a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) :
    (quotientMap G n).app U a = (inclusion G n).app (G.X.hom ⁻¹ᵁ U) a := rfl

@[simp]
theorem identity_preimage (U : S.Opens) :
    G.identitySection ⁻¹ᵁ (G.X.hom ⁻¹ᵁ U) = U := by
  rw [← Scheme.Hom.comp_preimage, G.identitySection_comp]
  rfl

/-- The base algebra structure on functions above an open of the base. -/
abbrev sectionAlgebra (U : S.Opens) : Algebra Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U) :=
  (G.X.hom.app U).hom.toAlgebra

attribute [local instance] sectionAlgebra

/-- Evaluation of functions at the identity over an open of the base. -/
def augmentation (U : S.Opens) :
    Γ(G.X.left, G.X.hom ⁻¹ᵁ U) →ₐ[Γ(S, U)] Γ(S, U) where
  toRingHom := (G.identitySection.appLE (G.X.hom ⁻¹ᵁ U) U
    (le_of_eq (identity_preimage G U).symm)).hom
  commutes' r := by
    have h := Scheme.Hom.comp_appLE G.identitySection G.X.hom U U
      (le_of_eq (identity_preimage G U).symm)
    have hh : G.X.hom.app U ≫ G.identitySection.appLE (G.X.hom ⁻¹ᵁ U) U
        (le_of_eq (identity_preimage G U).symm) = 𝟙 _ := by
      rw [← h]
      simp only [G.identitySection_comp]
      simp [Scheme.Hom.appLE]
      change S.presheaf.map (𝟙 (op U)) = 𝟙 (S.presheaf.obj (op U))
      exact S.presheaf.map_id (op U)
    exact ConcreteCategory.congr_hom hh r

section Separated

variable [IsSeparated G.X.hom]

instance identity_isClosedImmersion : IsClosedImmersion G.identitySection := by
  have : IsClosedImmersion (G.identitySection ≫ G.X.hom) := by
    rw [G.identitySection_comp]
    infer_instance
  exact IsClosedImmersion.of_comp _ G.X.hom

/-- Every positive power defining an identity jet has the same support
as the identity section of the separated group. -/
theorem range_inclusion_eq_range_identitySection (n : ℕ) : Set.range (inclusion G n) = Set.range G.identitySection := by
  change Set.range (ideal G n).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  change ((G.identitySection.ker ^ (n + 1)).support : Set G.X.left) = _
  rw [Scheme.IdealSheafData.support_pow_succ, Scheme.Hom.support_ker,
    G.identitySection.isClosedEmbedding.isClosed_range.closure_eq]

/-- The projection of the identity neighborhood is affine even when the
separated ambient group is not affine over its base. -/
theorem projection_isAffineHom_of_isSeparated (n : ℕ) : IsAffineHom (projection G n) := by
  have : IsClosedImmersion (inclusion G n) :=
    inferInstanceAs (IsClosedImmersion (ideal G n).subschemeι)
  have hfac (x : scheme G n) : G.identitySection (projection G n x) = inclusion G n x := by
    have hx : inclusion G n x ∈ Set.range G.identitySection :=
      range_inclusion_eq_range_identitySection G n ▸ Set.mem_range_self x
    obtain ⟨y, hy⟩ := hx
    have hp : projection G n x = y := by
      change (inclusion G n ≫ G.X.hom) x = y
      rw [Scheme.Hom.comp_apply, ← hy, ← Scheme.Hom.comp_apply, G.identitySection_comp]
      rfl
    exact hp ▸ hy
  have hind : Topology.IsInducing (projection G n) := by
    apply Topology.IsInducing.of_comp (projection G n).continuous G.identitySection.continuous
    have h : (G.identitySection ∘ projection G n : scheme G n → G.X.left) = inclusion G n :=
      funext hfac
    rw [h]
    exact (inclusion G n).isClosedEmbedding.isInducing
  have hsurj : Function.Surjective (projection G n) := by
    intro s
    have hs : G.identitySection s ∈ Set.range (inclusion G n) :=
      (range_inclusion_eq_range_identitySection G n).symm ▸ Set.mem_range_self s
    obtain ⟨x, hx⟩ := hs
    exact ⟨x, G.identitySection.isClosedEmbedding.injective ((hfac x).trans hx)⟩
  exact isAffineHom_of_isInducing _ hind (Set.range_eq_univ.mpr hsurj ▸ isClosed_univ)

end Separated

variable [IsAffineHom G.X.hom]

/-- The affine open of the group above an affine open of the base. -/
def affineOpen (U : S.affineOpens) : G.X.left.affineOpens :=
  ⟨G.X.hom ⁻¹ᵁ U, U.2.preimage G.X.hom⟩

theorem ker_augmentation (U : S.affineOpens) :
    RingHom.ker (augmentation G U) = G.identitySection.ker.ideal (affineOpen G U) := by
  rw [Scheme.Hom.ker_apply]
  change RingHom.ker
    ((S.presheaf.map (homOfLE (le_of_eq (identity_preimage G U).symm)).op).hom.comp
      (G.identitySection.app (G.X.hom ⁻¹ᵁ U)).hom) = _
  apply RingHom.ker_comp_of_injective
  have : IsIso (homOfLE (le_of_eq (identity_preimage G U).symm)) := by
    exact ⟨⟨homOfLE (le_of_eq (identity_preimage G U)), by simp, by simp⟩⟩
  exact (asIso (S.presheaf.map
    (homOfLE (le_of_eq (identity_preimage G U).symm)).op)).commRingCatIsoToRingEquiv.injective

@[simp]
theorem ideal_apply (n : ℕ) (U : S.affineOpens) :
    (ideal G n).ideal (affineOpen G U) = RingHom.ker (augmentation G U) ^ (n + 1) := by
  change G.identitySection.ker.ideal (affineOpen G U) ^ (n + 1) = _
  rw [← ker_augmentation G U]

/-- The actual affine section ring of the jet is the augmentation quotient. -/
def sectionsRingEquiv (n : ℕ) (U : S.affineOpens) :
    Γ(scheme G n, projection G n ⁻¹ᵁ U) ≃+*
      Algebra.SectionJet.Quotient (augmentation G U) n :=
  ((ideal G n).subschemeObjIso (affineOpen G U)).commRingCatIsoToRingEquiv.trans
    (Ideal.quotEquivOfEq (ideal_apply G n U))

@[simp]
theorem sectionsRingEquiv_inclusion_app (n : ℕ) (U : S.affineOpens)
    (a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) :
    sectionsRingEquiv G n U ((inclusion G n).app (G.X.hom ⁻¹ᵁ U) a) =
      Ideal.Quotient.mk (RingHom.ker (augmentation G U) ^ (n + 1)) a := by
  change sectionsRingEquiv G n U ((ideal G n).subschemeι.app (affineOpen G U) a) = _
  rw [Scheme.IdealSheafData.subschemeι_app]
  change Ideal.quotEquivOfEq (ideal_apply G n U)
    (((ideal G n).subschemeObjIso (affineOpen G U)).hom
      (((ideal G n).subschemeObjIso (affineOpen G U)).inv
        (Ideal.Quotient.mk _ a))) = _
  rw [Iso.inv_hom_id_apply]
  rfl

@[simp]
theorem sectionsRingEquiv_projection_app (n : ℕ) (U : S.affineOpens) (r : Γ(S, U)) :
    sectionsRingEquiv G n U ((projection G n).app U r) =
      algebraMap Γ(S, U) (Algebra.SectionJet.Quotient (augmentation G U) n) r := by
  change sectionsRingEquiv G n U
    ((inclusion G n).app (G.X.hom ⁻¹ᵁ U) (G.X.hom.app U r)) = _
  rw [sectionsRingEquiv_inclusion_app]
  rfl

/-- The quotient comparison respects the actual base-module action on the
pushforward, not just the underlying additive groups. -/
def sectionsEquiv (n : ℕ) (U : S.affineOpens) :
    Γ(module G n, U) ≃ₗ[Γ(S, U)] Algebra.SectionJet.Quotient (augmentation G U) n where
  toAddEquiv := (sectionsRingEquiv G n U).toAddEquiv
  map_smul' r x := by
    change sectionsRingEquiv G n U ((projection G n).app U r *
      (show Γ(scheme G n, projection G n ⁻¹ᵁ U) from x)) = _
    rw [map_mul, sectionsRingEquiv_projection_app]
    exact (Algebra.smul_def r
      (sectionsRingEquiv G n U (show Γ(scheme G n, projection G n ⁻¹ᵁ U) from x))).symm

@[simp]
theorem sectionsEquiv_inclusion_app (n : ℕ) (U : S.affineOpens)
    (a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) :
    sectionsEquiv G n U ((inclusion G n).app (G.X.hom ⁻¹ᵁ U) a) =
      Ideal.Quotient.mk (RingHom.ker (augmentation G U) ^ (n + 1)) a :=
  sectionsRingEquiv_inclusion_app G n U a

@[simp]
theorem sectionsEquiv_quotientMap (n : ℕ) (U : S.affineOpens)
    (a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) :
    sectionsEquiv G n U ((quotientMap G n).app U a) =
      Ideal.Quotient.mk (RingHom.ker (augmentation G U) ^ (n + 1)) a :=
  sectionsEquiv_inclusion_app G n U a

variable [Smooth G.X.hom]

instance smooth_sectionAlgebra (U : S.affineOpens) :
    Algebra.Smooth Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U) := by
  change (G.X.hom.app U).hom.Smooth
  simpa only [← Scheme.Hom.app_eq_appLE] using
    G.X.hom.smooth_appLE U.2 (U.2.preimage G.X.hom) le_rfl

/-- The actual affine section module of every identity jet is finite. -/
instance finite_sections (n : ℕ) (U : S.affineOpens) :
    Module.Finite Γ(S, U) Γ(module G n, U) :=
  Module.Finite.equiv (sectionsEquiv G n U).symm

/-- The actual affine section module of every identity jet is projective. -/
instance projective_sections (n : ℕ) (U : S.affineOpens) :
    Module.Projective Γ(S, U) Γ(module G n, U) :=
  Module.Projective.of_equiv (sectionsEquiv G n U).symm

end Langlands.GroupScheme.IdentityJet
