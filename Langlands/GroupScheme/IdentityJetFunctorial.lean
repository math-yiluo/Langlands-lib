import Langlands.GroupScheme.IdentityJetSeparatedBaseChange

/-! # Functorial maps of actual identity neighborhoods -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} {H G K : GroupScheme S}

@[simp]
theorem map_id (n : ℕ) : map (𝟙 G) n = 𝟙 (scheme G n) := by
  have : Mono (inclusion G n) := inferInstanceAs (Mono (ideal G n).subschemeι)
  apply (cancel_mono (inclusion G n)).mp
  rw [map_inclusion, Grp.id_hom_hom, Over.id_left, Category.comp_id, Category.id_comp]

@[simp]
theorem map_comp (f : H ⟶ G) (g : G ⟶ K) (n : ℕ) : map (f ≫ g) n = map f n ≫ map g n := by
  have : Mono (inclusion K n) := inferInstanceAs (Mono (ideal K n).subschemeι)
  apply (cancel_mono (inclusion K n)).mp
  rw [map_inclusion, Category.assoc, map_inclusion, map_inclusion_assoc,
    Grp.comp_hom_hom, Over.comp_left]

/-- The scheme of identity neighborhoods preserves isomorphisms of groups. -/
def mapIso (e : H ≅ G) (n : ℕ) : scheme H n ≅ scheme G n where
  hom := map e.hom n
  inv := map e.inv n
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

/-- Actual identity jets of an actual closed subgroup are the closed pullbacks
of the corresponding jets of its ambient group. -/
theorem map_isPullback_of_isClosedImmersion [IsSeparated G.X.hom] (f : H ⟶ G)
    [IsClosedImmersion f.hom.hom.left] (n : ℕ) :
    IsPullback (inclusion H n) (map f n) f.hom.hom.left (inclusion G n) := by
  have : IsClosedImmersion (inclusion H n) := inferInstanceAs (IsClosedImmersion (ideal H n).subschemeι)
  have : IsClosedImmersion (inclusion G n) := inferInstanceAs (IsClosedImmersion (ideal G n).subschemeι)
  have he : IsPullback H.identitySection (𝟙 S) f.hom.hom.left G.identitySection :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, identitySection_naturality]⟩
  have hk : G.identitySection.ker.comap f.hom.hom.left = H.identitySection.ker := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ← he.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  apply isPullback_of_isClosedImmersion _ _ _ _ (map_inclusion f n).symm
  simp only [inclusion, Scheme.IdealSheafData.ker_subschemeι, ideal, idealSheaf_comap_pow, hk]

/-- A closed immersion of groups induces closed immersions on all actual identity jets. -/
theorem map_isClosedImmersion (f : H ⟶ G) [IsClosedImmersion f.hom.hom.left] (n : ℕ) :
    IsClosedImmersion (map f n) := by
  have : IsClosedImmersion (inclusion H n) := inferInstanceAs (IsClosedImmersion (ideal H n).subschemeι)
  have : IsClosedImmersion (inclusion G n) := inferInstanceAs (IsClosedImmersion (ideal G n).subschemeι)
  have : IsClosedImmersion (map f n ≫ inclusion G n) := (map_inclusion f n).symm ▸ inferInstance
  exact IsClosedImmersion.of_comp _ (inclusion G n)

/-- The base-change squares for identity jets commute with the actual jet map
of any group homomorphism. -/
@[reassoc]
theorem map_baseChange {T : Scheme.{u}} (b : T ⟶ S) [IsSeparated H.X.hom]
    [IsSeparated G.X.hom] (f : H ⟶ G) (n : ℕ) :
    map ((GroupScheme.baseChange b).map f) n ≫ baseChangeMap G b n =
      baseChangeMap H b n ≫ map f n := by
  have : Mono (inclusion G n) := inferInstanceAs (Mono (ideal G n).subschemeι)
  apply (cancel_mono (inclusion G n)).mp
  rw [Category.assoc, Category.assoc, baseChangeMap_inclusion, map_inclusion,
    map_inclusion_assoc, baseChangeMap_inclusion_assoc]
  congr 1
  exact pullback.lift_fst _ _ _

end Langlands.GroupScheme.IdentityJet
