import Langlands.GroupScheme.MatrixRepresentation.LocalCentralKernelReduction
import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.CocharacterTransport

/-! # Conjugation preserves identity jets -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- Jet points are stable under restriction along morphisms of test schemes. -/
theorem IsJetPoint.comp {n : ℕ} {V V' : Over S} (c : V' ⟶ V) {x : V ⟶ G.X}
    (hx : IsJetPoint G n x) : IsJetPoint G n (c ≫ x) := by
  obtain ⟨y, hy⟩ := hx
  exact ⟨c.left ≫ y, by rw [Category.assoc, hy]; rfl⟩

/-- A scheme endomorphism of `G` fixing the unit section pulls each jet ideal
back into itself. -/
theorem ideal_comap_le_of_identity (φ : G.X.left ⟶ G.X.left)
    (hφ : G.identitySection ≫ φ = G.identitySection) (n : ℕ) :
    (ideal G n).comap φ ≤ ideal G n := by
  have h₁ : G.identitySection.ker.comap φ ≤ G.identitySection.ker := by
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker, hφ]
  change (G.identitySection.ker ^ (n + 1)).comap φ ≤ G.identitySection.ker ^ (n + 1)
  rw [idealSheaf_comap_pow]
  exact pow_le_pow_left₀ zero_le h₁ (n + 1)

/-- The map of identity jets induced by an endomorphism fixing the unit section. -/
def jetMap (φ : G.X.left ⟶ G.X.left) (hφ : G.identitySection ≫ φ = G.identitySection)
    (n : ℕ) : scheme G n ⟶ scheme G n :=
  Scheme.IdealSheafData.subschemeMap (ideal G n) (ideal G n) φ
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr (ideal_comap_le_of_identity G φ hφ n))

@[reassoc (attr := simp)]
theorem jetMap_inclusion (φ : G.X.left ⟶ G.X.left)
    (hφ : G.identitySection ≫ φ = G.identitySection) (n : ℕ) :
    jetMap G φ hφ n ≫ inclusion G n = inclusion G n ≫ φ :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- An endomorphism fixing the unit section sends jet points to jet points. -/
theorem IsJetPoint.comp_of_identity {n : ℕ} {V : Over S} {x : V ⟶ G.X}
    (hx : IsJetPoint G n x) (φ : G.X ⟶ G.X)
    (hφ : G.identitySection ≫ φ.left = G.identitySection) :
    IsJetPoint G n (x ≫ φ) := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨y ≫ jetMap G φ.left hφ n, ?_⟩
  rw [Category.assoc, jetMap_inclusion, ← Category.assoc, hy]
  rfl

/-- Group-scheme endomorphisms send jet points to jet points. -/
theorem IsJetPoint.comp_hom {n : ℕ} {V : Over S} {x : V ⟶ G.X}
    (hx : IsJetPoint G n x) (f : G ⟶ G) : IsJetPoint G n (x ≫ f.hom.hom) :=
  hx.comp_of_identity G f.hom.hom (identitySection_naturality f)

variable [IsSeparated G.X.hom]

/-- Conjugating a jet point by any point of `G` gives a jet point. -/
theorem IsJetPoint.conj {n : ℕ} {U V : Over S} (g : U ⟶ G.X) (a : V ⟶ U)
    {x : V ⟶ G.X} (hx : IsJetPoint G n x) :
    IsJetPoint G n ((a ≫ g) * x * (a ≫ g)⁻¹) := by
  let b : U.left ⟶ S := U.hom
  let H := (GroupScheme.baseChange b).obj G
  have : IsSeparated H.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom b))
  let g' : Over.mk (𝟙 U.left) ⟶ H.X := (baseChangeBasePointsEquiv b G).symm g
  let VU : Over U.left := Over.mk a.left
  have hV : V.hom = ((Over.map b).obj VU).hom := by
    change V.hom = a.left ≫ U.hom
    exact (Over.w a).symm
  let φ : V ≅ (Over.map b).obj VU := Over.isoMk (Iso.refl _) (by simp [hV])
  let x' : VU ⟶ H.X := (baseChangePointsEquiv b G VU).symm (φ.inv ≫ x)
  have hx' : IsJetPoint H n x' := by
    rw [isJetPoint_baseChange_iff, MulEquiv.apply_symm_apply]
    exact hx.comp G φ.inv
  have hy' : IsJetPoint H n (x' ≫ (H.innerIso g').hom.hom.hom) :=
    hx'.comp_hom H (H.innerIso g').hom
  rw [comp_innerIso_hom, isJetPoint_baseChange_iff, map_mul, map_mul, map_inv,
    MulEquiv.apply_symm_apply] at hy'
  have hc : baseChangePointsEquiv b G VU (H.constantPoint g' VU) = φ.inv ≫ (a ≫ g) := by
    apply Over.OverMorphism.ext
    rw [baseChangePointsEquiv_left]
    change (VU.hom ≫ g'.left) ≫ pullback.fst G.X.hom b = 𝟙 V.left ≫ a.left ≫ g.left
    rw [Category.assoc, ← baseChangeBasePointsEquiv_left, MulEquiv.apply_symm_apply,
      Category.id_comp]
    rfl
  rw [hc, ← GrpObj.comp_inv, ← MonObj.comp_mul, ← MonObj.comp_mul] at hy'
  have := hy'.comp G φ.hom
  rwa [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at this

end Langlands.GroupScheme.IdentityJet
