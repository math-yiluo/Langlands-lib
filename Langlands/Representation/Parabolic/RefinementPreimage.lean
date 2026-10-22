import Langlands.Group.GL.Blocks

/-! Actual ambient preimages of subgroups of a block Levi. -/

namespace Langlands.Parabolic

open GeneralLinear

universe u

variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n)
    (H : Subgroup (B.Levi R))

/-- The inverse image of a Levi subgroup, included as an actual matrix subgroup. -/
def leviPreimage : Subgroup (GeneralLinear n R) :=
  (H.comap (B.leviProjection R)).map (B.parabolic R).subtype

/-- An ambient matrix belongs exactly when it is parabolic and its projection lies in H. -/
theorem mem_leviPreimage_iff (g : GeneralLinear n R) :
    g ∈ leviPreimage R B H ↔
      ∃ hg : g ∈ B.parabolic R, B.leviProjection R ⟨g, hg⟩ ∈ H := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.property, hp⟩
  · rintro ⟨hg, hp⟩
    exact ⟨⟨g, hg⟩, hp, rfl⟩

theorem leviPreimage_le_parabolic : leviPreimage R B H ≤ B.parabolic R := by
  rintro g ⟨p, hp, rfl⟩
  exact p.property

/-- The actual ambient preimage embeds in the original parabolic. -/
def preimageInParabolic : leviPreimage R B H →* B.parabolic R where
  toFun g := ⟨g.val, leviPreimage_le_parabolic R B H g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The restricted diagonal-block projection, with its genuine subgroup codomain. -/
def preimageProjection : leviPreimage R B H →* H where
  toFun g := ⟨B.leviProjection R (preimageInParabolic R B H g), by
    rcases (mem_leviPreimage_iff R B H g.val).mp g.property with ⟨hg, hp⟩
    exact hp⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := by
    apply Subtype.ext
    exact (B.leviProjection R).map_mul
      (preimageInParabolic R B H g) (preimageInParabolic R B H h)

/-- The original block diagonal section restricted to H. -/
def preimageSection : H →* leviPreimage R B H where
  toFun h := ⟨B.leviEmbedding R h.val,
    ⟨B.leviInParabolic R h.val, by
      change B.leviProjection R (B.leviInParabolic R h.val) ∈ H
      simpa only [B.leviProjection_section] using h.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

@[simp]
theorem preimageSection_val (h : H) :
    (preimageSection R B H h).val = B.leviEmbedding R h.val := rfl

@[simp]
theorem preimageInParabolic_section (h : H) :
    preimageInParabolic R B H (preimageSection R B H h) =
      B.leviInParabolic R h.val := rfl

@[simp]
theorem preimageProjection_section (h : H) :
    preimageProjection R B H (preimageSection R B H h) = h :=
  Subtype.ext (B.leviProjection_section R h.val)

theorem preimageProjection_surjective : Function.Surjective (preimageProjection R B H) :=
  fun h => ⟨preimageSection R B H h, preimageProjection_section R B H h⟩

/-- The projection kernel is exactly the original radical inside this ambient subgroup. -/
theorem preimageProjection_ker :
    (preimageProjection R B H).ker =
      (B.unipotentSubgroup R).comap (leviPreimage R B H).subtype := by
  ext g
  change preimageProjection R B H g = 1 ↔ g.val ∈ B.unipotentSubgroup R
  constructor
  · intro hg
    exact ⟨preimageInParabolic R B H g, congrArg Subtype.val hg, rfl⟩
  · rintro ⟨p, hp, hpg⟩
    apply Subtype.ext
    have heq : preimageInParabolic R B H g = p := Subtype.ext hpg.symm
    change B.leviProjection R (preimageInParabolic R B H g) = 1
    rw [heq]
    exact hp

/-- The original radical lies in every Levi preimage. -/
def radicalInPreimage : B.unipotentRadical R →* leviPreimage R B H where
  toFun u := ⟨u.val.val, ⟨u.val, by
    change B.leviProjection R u.val ∈ H
    rw [show B.leviProjection R u.val = 1 from u.property]
    exact H.one_mem, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem preimageProjection_radical (u : B.unipotentRadical R) :
    preimageProjection R B H (radicalInPreimage R B H u) = 1 :=
  Subtype.ext u.property

/-- Remove the diagonal component inside the original parabolic. -/
def preimageUnipotentPart (g : leviPreimage R B H) : B.unipotentRadical R :=
  B.unipotentPart R (preimageInParabolic R B H g)

/-- The actual unique factorization g = u*m, with u in the original radical and m in H. -/
def preimageDecomposition :
    leviPreimage R B H ≃ B.unipotentRadical R × H where
  toFun g := (preimageUnipotentPart R B H g, preimageProjection R B H g)
  invFun um := radicalInPreimage R B H um.1 * preimageSection R B H um.2
  left_inv g := by
    apply Subtype.ext
    change (g.val * (B.leviEmbedding R
      (B.leviProjection R (preimageInParabolic R B H g)))⁻¹) *
        B.leviEmbedding R (B.leviProjection R (preimageInParabolic R B H g)) = g.val
    exact inv_mul_cancel_right _ _
  right_inv um := by
    rcases um with ⟨u, h⟩
    have hp : preimageProjection R B H
        (radicalInPreimage R B H u * preimageSection R B H h) = h := by simp
    apply Prod.ext
    · apply Subtype.ext
      change (u.val * B.leviInParabolic R h.val) *
        (B.leviInParabolic R (B.leviProjection R
          (u.val * B.leviInParabolic R h.val)))⁻¹ = u.val
      have hu : B.leviProjection R u.val = 1 := u.property
      simp [hu]
    · exact hp

/-- Iterated subgroup preimages are compatible with the actual projection to H. -/
theorem preimage_subgroup (K : Subgroup H) :
    ((K.comap (preimageProjection R B H)).map (leviPreimage R B H).subtype) =
      leviPreimage R B (K.map H.subtype) := by
  ext g
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_leviPreimage_iff R B (K.map H.subtype) p.val).mpr
      ⟨(preimageInParabolic R B H p).property,
        ⟨preimageProjection R B H p, hp, rfl⟩⟩
  · intro hg
    rcases (mem_leviPreimage_iff R B (K.map H.subtype) g).mp hg with ⟨hgp, hK⟩
    rcases hK with ⟨h, hh, heq⟩
    let p : leviPreimage R B H :=
      ⟨g, (mem_leviPreimage_iff R B H g).mpr ⟨hgp, heq ▸ h.property⟩⟩
    refine ⟨p, ?_, rfl⟩
    change preimageProjection R B H p ∈ K
    have hp : preimageProjection R B H p = h := Subtype.ext heq.symm
    rw [hp]
    exact hh

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The restricted projection is continuous in the actual subgroup topologies. -/
def preimageProjectionContinuous : ContinuousMonoidHom (leviPreimage R B H) H where
  toMonoidHom := preimageProjection R B H
  continuous_toFun := ((B.leviProjectionContinuous R).continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _

/-- The restricted block diagonal section is continuous. -/
def preimageSectionContinuous : ContinuousMonoidHom H (leviPreimage R B H) where
  toMonoidHom := preimageSection R B H
  continuous_toFun := ((B.leviEmbeddingContinuous R).continuous.comp
    continuous_subtype_val).subtype_mk _

/-- The proved factorization preserves the actual subgroup topologies. -/
def preimageDecompositionHomeomorph :
    leviPreimage R B H ≃ₜ B.unipotentRadical R × H where
  toEquiv := preimageDecomposition R B H
  continuous_toFun :=
    ((B.decompositionHomeomorph R).continuous.fst.comp
      (continuous_subtype_val.subtype_mk _)).prodMk
        (preimageProjectionContinuous R B H).continuous
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).comp
      continuous_fst).mul
        ((B.leviEmbeddingContinuous R).continuous.comp
          (continuous_subtype_val.comp continuous_snd)) |>.subtype_mk _

/-- Closed Levi subgroups have closed ambient preimages. -/
theorem isClosed_leviPreimage [T2Space R]
    (hH : IsClosed (H : Set (B.Levi R))) :
    IsClosed (leviPreimage R B H : Set (GeneralLinear n R)) :=
  (B.isClosed_parabolic R).isClosedMap_subtype_val _
    (hH.preimage (B.leviProjectionContinuous R).continuous)

end Topology

end Langlands.Parabolic
