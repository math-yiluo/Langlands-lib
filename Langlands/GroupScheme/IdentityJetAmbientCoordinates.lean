import Langlands.GroupScheme.IdentityJetCoordinates
import Langlands.GroupScheme.SelfNormalizingAmbient.Stabilizer
import Langlands.GroupScheme.AffineCorepresented
import Langlands.AbelianScheme.LieBaseChange

/-! # Ambient coordinates of actual subgroup identity jets -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Corepresented

variable {R : CommRingCat.{u}} (F : CommAlgCat R ⥤ GrpCat.{u})
  {B : CommAlgCat R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- The algebraic counit is the actual identity section's coordinate map. -/
theorem identitySection_eq_specMap_counit :
    (groupScheme F e).identitySection =
      Spec.map (CommRingCat.ofHom (LinearEmbedding.counit e).hom.toRingHom) := by
  have h : (algSpec R).map (LinearEmbedding.counit e).op =
      (1 : (algSpec R).obj (op (LinearEmbedding.base (R := R))) ⟶
        (groupScheme F e).X) := by
    apply (affinePointsEquiv F e _).injective
    rw [affinePointsEquiv_map, map_one]
    exact e.homEquiv.apply_symm_apply 1
  rw [Hom.one_def] at h
  have hh := congrArg (fun a => a.left) h.symm
  change Spec.map (𝟙 R) ≫ (groupScheme F e).identitySection =
    Spec.map (CommRingCat.ofHom (LinearEmbedding.counit e).hom.toRingHom) at hh
  simpa only [Spec.map_id, Category.id_comp] using hh

end Corepresented

namespace IdentityJet

open AffineCoordinates Corepresented

variable {R : CommRingCat.{u}} {S : Scheme.{u}}
  (G : GroupScheme (Spec R)) [IsAffine G.X.left]
  (b : S ⟶ Spec R) {H : GroupScheme S}
  (h : H ⟶ (GroupScheme.baseChange b).obj G)

/-- The actual subgroup's map to the fixed affine coordinates of its ambient group. -/
def ambientProjection : H.X.left ⟶ Spec (CommRingCat.of (algebra G)) :=
  h.hom.hom.left ≫ Limits.pullback.fst G.X.hom b ≫
    (groupSchemeIso G).inv.hom.hom.left

/-- The actual identity maps to the ambient identity in the fixed coordinates. -/
@[reassoc]
theorem identitySection_ambientProjection :
    H.identitySection ≫ ambientProjection G b h =
      b ≫ (groupScheme (functor G) (corepresentation G)).identitySection := by
  simp only [ambientProjection, identitySection_naturality_assoc,
    identitySection_baseChange_fst_assoc, identitySection_naturality]

/-- Ambient augmentation functions vanish on the actual subgroup identity. -/
theorem ambientProjection_vanishesAtIdentity :
    VanishesAtIdentity H (ambientProjection G b h) (augIdeal (corepresentation G)) := by
  intro a ha
  rw [identitySection_ambientProjection, identitySection_eq_specMap_counit,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hh := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (LinearEmbedding.counit (corepresentation G)).hom.toRingHom)) a
  change (Scheme.ΓSpecIso R).inv ((LinearEmbedding.counit (corepresentation G)).hom a) =
    (Spec.map
      (CommRingCat.ofHom (LinearEmbedding.counit (corepresentation G)).hom.toRingHom)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv a) at hh
  calc
    _ = b.appTop ((Scheme.ΓSpecIso R).inv
        ((LinearEmbedding.counit (corepresentation G)).hom a)) :=
      congrArg (fun z => b.appTop z) hh.symm
    _ = 0 := by
      rw [show (LinearEmbedding.counit (corepresentation G)).hom a = 0 from ha,
        map_zero, map_zero]

variable [IsAffineHom H.X.hom]

/-- Actual subgroup jet sections supplied by the fixed ambient jet coordinates. -/
def ambientQuotientCoordinates (n : ℕ) :
    (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)) →+*
      Γ(scheme H n, projection H n ⁻¹ᵁ ⊤) :=
  quotientCoordinates H (ambientProjection G b h) (augIdeal (corepresentation G))
    (ambientProjection_vanishesAtIdentity G b h) n

end IdentityJet
end Langlands.GroupScheme
