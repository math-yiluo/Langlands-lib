import Langlands.GroupScheme.IdentityJetOpenBaseChange
import Langlands.AlgebraicGeometry.Modules.AffinePushforwardBaseChange
import Langlands.AlgebraicGeometry.Modules.CechDegreeOne
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le

/-! # Actual identity jets under arbitrary change of base -/

noncomputable section

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityJet

/-- Pullback of ideal sheaves commutes with their powers under every scheme map. -/
theorem idealSheaf_comap_pow {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (f : Y ⟶ X) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  have hlocal : ∀ y : Y, ∃ (U : X.affineOpens) (V : Y.affineOpens),
      y ∈ V.1 ∧ V.1 ≤ f ⁻¹ᵁ U.1 := by
    intro y
    obtain ⟨U, hU, hyU, _⟩ :=
      exists_isAffineOpen_mem_and_subset (show f y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hyV, hVU⟩ :=
      exists_isAffineOpen_mem_and_subset (show y ∈ f ⁻¹ᵁ U from hyU)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hyV, hVU⟩
  choose U V hy hVU using hlocal
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V
    (top_le_iff.mp (fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩))
  intro y
  rw [Scheme.IdealSheafData.ideal_comap_of_le _ f (U y) (V y) (hVU y)]
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  rw [Scheme.IdealSheafData.ideal_comap_of_le _ f (U y) (V y) (hVU y),
    Ideal.map_pow]

variable {S T : Scheme.{u}} (G : GroupScheme S) [IsAffineHom G.X.hom]
  (b : T ⟶ S)

private theorem identity_ker_baseChange :
    G.identitySection.ker.comap (pullback.fst G.X.hom b) =
      ((GroupScheme.baseChange b).obj G).identitySection.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have h := identitySection_isPullback G b
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- Actual jet ideals commute with every base change. -/
theorem ideal_baseChange (n : ℕ) :
    (ideal G n).comap (pullback.fst G.X.hom b) =
      ideal ((GroupScheme.baseChange b).obj G) n := by
  change (G.identitySection.ker ^ (n + 1)).comap (pullback.fst G.X.hom b) = _
  rw [idealSheaf_comap_pow, identity_ker_baseChange]
  rfl

/-- The actual scheme map from a base-changed identity neighborhood. -/
def baseChangeMap (n : ℕ) :
    scheme ((GroupScheme.baseChange b).obj G) n ⟶ scheme G n :=
  Scheme.IdealSheafData.subschemeMap
    (ideal ((GroupScheme.baseChange b).obj G) n) (ideal G n)
    (pullback.fst G.X.hom b)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr (le_of_eq (ideal_baseChange G b n)))

@[reassoc (attr := simp)]
theorem baseChangeMap_inclusion (n : ℕ) :
    baseChangeMap G b n ≫ inclusion G n =
      inclusion ((GroupScheme.baseChange b).obj G) n ≫ pullback.fst G.X.hom b :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The actual identity neighborhoods form the base-change square. -/
theorem baseChange_isPullback (n : ℕ) :
    IsPullback (baseChangeMap G b n) (projection ((GroupScheme.baseChange b).obj G) n)
      (projection G n) b := by
  have : IsClosedImmersion (inclusion G n) :=
    inferInstanceAs (IsClosedImmersion (ideal G n).subschemeι)
  have : IsClosedImmersion (inclusion ((GroupScheme.baseChange b).obj G) n) :=
    inferInstanceAs (IsClosedImmersion (ideal ((GroupScheme.baseChange b).obj G) n).subschemeι)
  have h : IsPullback (inclusion ((GroupScheme.baseChange b).obj G) n)
      (baseChangeMap G b n) (pullback.fst G.X.hom b) (inclusion G n) :=
    isPullback_of_isClosedImmersion _ _ _ _
      (baseChangeMap_inclusion G b n).symm
      (by simpa only [inclusion, Scheme.IdealSheafData.ker_subschemeι] using
        ideal_baseChange G b n)
  exact h.flip.paste_vert (IsPullback.of_hasPullback G.X.hom b)

/-- The actual jet module commutes with every base change. -/
def baseChangeIso (n : ℕ) :
    (Scheme.Modules.pullback b).obj (module G n) ≅
      module ((GroupScheme.baseChange b).obj G) n := by
  have : IsClosedImmersion (inclusion G n) :=
    inferInstanceAs (IsClosedImmersion (ideal G n).subschemeι)
  have : IsAffineHom (projection G n) := by
    change IsAffineHom (inclusion G n ≫ G.X.hom)
    infer_instance
  have : (Langlands.SchemeModule.structureModule (scheme G n)).IsQuasicoherent :=
    Langlands.AlgebraicGeometry.Modules.CechDegreeOne.isQuasicoherent_unit _
  exact
    Langlands.AlgebraicGeometry.Modules.DerivedSections.affinePushforwardBaseChangeIso
      b (projection G n) (projection ((GroupScheme.baseChange b).obj G) n)
      (baseChangeMap G b n) (baseChange_isPullback G b n)
      (Langlands.SchemeModule.structureModule (scheme G n)) ≪≫
        (Scheme.Modules.pushforward (projection ((GroupScheme.baseChange b).obj G) n)).mapIso
          (Langlands.Scheme.Modules.pullbackUnitIso (baseChangeMap G b n))

end Langlands.GroupScheme.IdentityJet
