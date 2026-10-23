import Langlands.Group.GL.OppositeBlocks
import Langlands.Representation.Geometric.RefinementDefinitions

/-! Actual opposite refinement geometry with the existing common refined Levi. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear

universe u
variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The product of the actual opposite parabolics in the outer Levi. -/
def refinedOppositeParabolic : Subgroup (B.Levi R) :=
  Subgroup.pi Set.univ (fun i => (S i).oppositeParabolic R)

/-- The product of the actual opposite radicals in the outer Levi. -/
def refinedOppositeUnipotent : Subgroup (B.Levi R) :=
  Subgroup.pi Set.univ (fun i => (S i).oppositeUnipotentSubgroup R)

@[simp] theorem mem_refinedOppositeParabolic (g : B.Levi R) :
    g ∈ refinedOppositeParabolic R B S ↔ ∀ i, g i ∈ (S i).oppositeParabolic R := by
  simp [refinedOppositeParabolic, Subgroup.mem_pi]

@[simp] theorem mem_refinedOppositeUnipotent (g : B.Levi R) :
    g ∈ refinedOppositeUnipotent R B S ↔ ∀ i, g i ∈ (S i).oppositeUnipotentSubgroup R := by
  simp [refinedOppositeUnipotent, Subgroup.mem_pi]

/-- Evaluate a refined parabolic element in one actual block parabolic. -/
def refinedOppositeParabolicEval (i : Fin B.length) :
    refinedOppositeParabolic R B S →* (S i).oppositeParabolic R where
  toFun g := ⟨g.val i, (mem_refinedOppositeParabolic R B S g.val).mp g.property i⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The projection has the actual refined subgroup as codomain. -/
def refinedOppositeLeviProjection : refinedOppositeParabolic R B S →* refinedLevi R B S :=
  (refinedLeviEquiv R B S).toMonoidHom.comp
    (MonoidHom.pi fun i => ((S i).oppositeLeviProjection R).comp (refinedOppositeParabolicEval R B S i))

/-- The section is the inclusion of the existing diagonal subgroup. -/
def refinedOppositeLeviSection : refinedLevi R B S →* refinedOppositeParabolic R B S where
  toFun m := ⟨m.val, by
    rw [mem_refinedOppositeParabolic]
    intro i
    rcases (mem_refinedLevi R B S m.val).mp m.property i with ⟨mi, hmi⟩
    exact hmi ▸ ((S i).oppositeLeviInParabolic R mi).property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem refinedOppositeLeviSection_val (m : refinedLevi R B S) :
    (refinedOppositeLeviSection R B S m).val = m.val := rfl

@[simp] theorem refinedOppositeLeviProjection_section (m : refinedLevi R B S) :
    refinedOppositeLeviProjection R B S (refinedOppositeLeviSection R B S m) = m := by
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val ((S i).leviEquiv R |>.apply_symm_apply
    (refinedLeviEval R B S i m))

/-- The radical as a normal subgroup of the actual refined parabolic. -/
def refinedOppositeUnipotentRadical : Subgroup (refinedOppositeParabolic R B S) :=
  (refinedOppositeLeviProjection R B S).ker

instance refinedOppositeUnipotentRadical_normal : (refinedOppositeUnipotentRadical R B S).Normal :=
  inferInstanceAs (refinedOppositeLeviProjection R B S).ker.Normal

private theorem block_mem_radical (i : Fin B.length) (g : (S i).oppositeParabolic R) :
    g.val ∈ (S i).oppositeUnipotentSubgroup R ↔ (S i).oppositeLeviProjection R g = 1 := by
  constructor
  · rintro ⟨h, hh, he⟩
    have e : h = g := Subtype.ext he
    subst h
    exact hh
  · intro h
    exact ⟨g, h, rfl⟩

/-- The kernel condition is exactly membership in the published product radical. -/
theorem mem_refinedOppositeUnipotentRadical (g : refinedOppositeParabolic R B S) :
    g ∈ refinedOppositeUnipotentRadical R B S ↔ g.val ∈ refinedOppositeUnipotent R B S := by
  change refinedOppositeLeviProjection R B S g = 1 ↔ _
  rw [mem_refinedOppositeUnipotent]
  constructor
  · intro h i
    apply (block_mem_radical R B S i (refinedOppositeParabolicEval R B S i g)).mpr
    have e := congrArg (fun m => (refinedLeviEquiv R B S).symm m i) h
    simpa [refinedOppositeLeviProjection] using e
  · intro h
    have e : (fun i => (S i).oppositeLeviProjection R (refinedOppositeParabolicEval R B S i g)) = 1 := by
      funext i
      exact (block_mem_radical R B S i (refinedOppositeParabolicEval R B S i g)).mp (h i)
    change refinedLeviEquiv R B S (fun i => (S i).oppositeLeviProjection R
      (refinedOppositeParabolicEval R B S i g)) = 1
    rw [e, map_one]

theorem refinedOppositeUnipotent_le_parabolic :
    refinedOppositeUnipotent R B S ≤ refinedOppositeParabolic R B S := by
  intro g hg
  rw [mem_refinedOppositeParabolic]
  intro i
  rcases (mem_refinedOppositeUnipotent R B S g).mp hg i with ⟨h, _, he⟩
  exact he ▸ h.property

/-- The kernel's ambient image is precisely the previously defined radical. -/
theorem refinedOppositeUnipotentRadical_map :
    (refinedOppositeUnipotentRadical R B S).map (refinedOppositeParabolic R B S).subtype =
      refinedOppositeUnipotent R B S := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (mem_refinedOppositeUnipotentRadical R B S h).mp hh
  · intro hg
    exact ⟨⟨g, refinedOppositeUnipotent_le_parabolic R B S hg⟩,
      (mem_refinedOppositeUnipotentRadical R B S _).mpr hg, rfl⟩

/-- The radical in the parabolic is also its intrinsic subgroup preimage. -/
theorem refinedOppositeLeviProjection_ker :
    (refinedOppositeLeviProjection R B S).ker =
      (refinedOppositeUnipotent R B S).comap (refinedOppositeParabolic R B S).subtype := by
  ext g
  exact mem_refinedOppositeUnipotentRadical R B S g

/-- Every parabolic element normalizes the ambient radical. -/
theorem refinedOppositeParabolic_le_normalizer :
    refinedOppositeParabolic R B S ≤ Subgroup.normalizer (refinedOppositeUnipotent R B S : Set (B.Levi R)) := by
  intro g hg
  rw [← refinedOppositeUnipotentRadical_map R B S]
  apply Subgroup.le_normalizer_map _
  exact ⟨⟨g, hg⟩, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩

/-- The actual Levi inclusion into the normalizer used by Jacquet actions. -/
def refinedOppositeLeviNormalizer :
    refinedLevi R B S →* Subgroup.normalizer (refinedOppositeUnipotent R B S : Set (B.Levi R)) where
  toFun m := ⟨m.val, refinedOppositeParabolic_le_normalizer R B S
    (refinedOppositeLeviSection R B S m).property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem refinedOppositeLeviNormalizer_val (m : refinedLevi R B S) :
    (refinedOppositeLeviNormalizer R B S m).val = m.val := rfl

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
theorem continuous_refinedOppositeParabolicEval (i : Fin B.length) :
    Continuous (refinedOppositeParabolicEval R B S i) :=
  ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

/-- The actual refined Levi projection is continuous. -/
def refinedOppositeLeviProjectionContinuous :
    ContinuousMonoidHom (refinedOppositeParabolic R B S) (refinedLevi R B S) where
  toMonoidHom := refinedOppositeLeviProjection R B S
  continuous_toFun := (refinedLeviEquivContinuous R B S).continuous.comp
    (continuous_pi fun i => ((S i).oppositeLeviProjectionContinuous R).continuous.comp
      (continuous_refinedOppositeParabolicEval R B S i))

/-- The actual inclusion section is continuous. -/
def refinedOppositeLeviSectionContinuous :
    ContinuousMonoidHom (refinedLevi R B S) (refinedOppositeParabolic R B S) where
  toMonoidHom := refinedOppositeLeviSection R B S
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The radical-normalizer inclusion has the subgroup topology. -/
def refinedOppositeLeviNormalizerContinuous :
    ContinuousMonoidHom (refinedLevi R B S)
      (Subgroup.normalizer (refinedOppositeUnipotent R B S : Set (B.Levi R))) where
  toMonoidHom := refinedOppositeLeviNormalizer R B S
  continuous_toFun := continuous_subtype_val.subtype_mk _

end Topology
end Langlands.Geometric

namespace Langlands.Parabolic

open GeneralLinear

universe u

variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n)
    (H : Subgroup (B.Levi R))

/-- The inverse image of a Levi subgroup, included as an actual matrix subgroup. -/
def oppositeLeviPreimage : Subgroup (GeneralLinear n R) :=
  (H.comap (B.oppositeLeviProjection R)).map (B.oppositeParabolic R).subtype

/-- An ambient matrix belongs exactly when it is parabolic and its projection lies in H. -/
theorem mem_oppositeLeviPreimage_iff (g : GeneralLinear n R) :
    g ∈ oppositeLeviPreimage R B H ↔
      ∃ hg : g ∈ B.oppositeParabolic R, B.oppositeLeviProjection R ⟨g, hg⟩ ∈ H := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.property, hp⟩
  · rintro ⟨hg, hp⟩
    exact ⟨⟨g, hg⟩, hp, rfl⟩

theorem oppositeLeviPreimage_le_parabolic : oppositeLeviPreimage R B H ≤ B.oppositeParabolic R := by
  rintro g ⟨p, hp, rfl⟩
  exact p.property

/-- The actual ambient preimage embeds in the original parabolic. -/
def oppositePreimageInParabolic : oppositeLeviPreimage R B H →* B.oppositeParabolic R where
  toFun g := ⟨g.val, oppositeLeviPreimage_le_parabolic R B H g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The restricted diagonal-block projection, with its genuine subgroup codomain. -/
def oppositePreimageProjection : oppositeLeviPreimage R B H →* H where
  toFun g := ⟨B.oppositeLeviProjection R (oppositePreimageInParabolic R B H g), by
    rcases (mem_oppositeLeviPreimage_iff R B H g.val).mp g.property with ⟨hg, hp⟩
    exact hp⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := by
    apply Subtype.ext
    exact (B.oppositeLeviProjection R).map_mul
      (oppositePreimageInParabolic R B H g) (oppositePreimageInParabolic R B H h)

/-- The original block diagonal section restricted to H. -/
def oppositePreimageSection : H →* oppositeLeviPreimage R B H where
  toFun h := ⟨B.leviEmbedding R h.val,
    ⟨B.oppositeLeviInParabolic R h.val, by
      change B.oppositeLeviProjection R (B.oppositeLeviInParabolic R h.val) ∈ H
      simpa only [B.oppositeLeviProjection_section] using h.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

@[simp]
theorem oppositePreimageSection_val (h : H) :
    (oppositePreimageSection R B H h).val = B.leviEmbedding R h.val := rfl

@[simp]
theorem oppositePreimageInParabolic_section (h : H) :
    oppositePreimageInParabolic R B H (oppositePreimageSection R B H h) =
      B.oppositeLeviInParabolic R h.val := rfl

@[simp]
theorem oppositePreimageProjection_section (h : H) :
    oppositePreimageProjection R B H (oppositePreimageSection R B H h) = h :=
  Subtype.ext (B.oppositeLeviProjection_section R h.val)

/-- Iterated subgroup preimages are compatible with the actual projection to H. -/
theorem oppositePreimage_subgroup (K : Subgroup H) :
    ((K.comap (oppositePreimageProjection R B H)).map (oppositeLeviPreimage R B H).subtype) =
      oppositeLeviPreimage R B (K.map H.subtype) := by
  ext g
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_oppositeLeviPreimage_iff R B (K.map H.subtype) p.val).mpr
      ⟨(oppositePreimageInParabolic R B H p).property,
        ⟨oppositePreimageProjection R B H p, hp, rfl⟩⟩
  · intro hg
    rcases (mem_oppositeLeviPreimage_iff R B (K.map H.subtype) g).mp hg with ⟨hgp, hK⟩
    rcases hK with ⟨h, hh, heq⟩
    let p : oppositeLeviPreimage R B H :=
      ⟨g, (mem_oppositeLeviPreimage_iff R B H g).mpr ⟨hgp, heq ▸ h.property⟩⟩
    refine ⟨p, ?_, rfl⟩
    change oppositePreimageProjection R B H p ∈ K
    have hp : oppositePreimageProjection R B H p = h := Subtype.ext heq.symm
    rw [hp]
    exact hh

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The restricted projection is continuous in the actual subgroup topologies. -/
def oppositePreimageProjectionContinuous : ContinuousMonoidHom (oppositeLeviPreimage R B H) H where
  toMonoidHom := oppositePreimageProjection R B H
  continuous_toFun := ((B.oppositeLeviProjectionContinuous R).continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _

/-- The restricted block diagonal section is continuous. -/
def oppositePreimageSectionContinuous : ContinuousMonoidHom H (oppositeLeviPreimage R B H) where
  toMonoidHom := oppositePreimageSection R B H
  continuous_toFun := ((B.leviEmbeddingContinuous R).continuous.comp
    continuous_subtype_val).subtype_mk _

end Topology

end Langlands.Parabolic

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe u
variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The inner parabolic pulled back into the original matrix group. -/
def composedOppositeParabolic : Subgroup (GeneralLinear n R) :=
  oppositeLeviPreimage R B (refinedOppositeParabolic R B S)

/-- The full radical: the outer radical together with the lifted inner radical. -/
def composedOppositeUnipotent : Subgroup (GeneralLinear n R) :=
  oppositeLeviPreimage R B (refinedOppositeUnipotent R B S)

/-- The full radical contains the entire outer opposite radical. -/
theorem oppositeUnipotentSubgroup_le_composedOppositeUnipotent :
    B.oppositeUnipotentSubgroup R ≤ composedOppositeUnipotent R B S := by
  rintro g ⟨p, hp, rfl⟩
  refine (mem_oppositeLeviPreimage_iff R B (refinedOppositeUnipotent R B S) p.val).mpr
    ⟨p.property, ?_⟩
  change B.oppositeLeviProjection R p ∈ refinedOppositeUnipotent R B S
  have hp' : B.oppositeLeviProjection R p = 1 := hp
  rw [hp']
  exact Subgroup.one_mem _

/-- The embedded inner opposite radical also belongs to the full radical. -/
theorem refinedOppositeUnipotent_map_le_composedOppositeUnipotent :
    (refinedOppositeUnipotent R B S).map (B.leviEmbedding R) ≤
      composedOppositeUnipotent R B S := by
  rintro g ⟨m, hm, rfl⟩
  exact (oppositePreimageSection R B (refinedOppositeUnipotent R B S) ⟨m, hm⟩).property

/-- The composite projection, with the actual inner Levi subgroup as codomain. -/
def composedOppositeLeviProjection : composedOppositeParabolic R B S →* refinedLevi R B S :=
  (refinedOppositeLeviProjection R B S).comp
    (oppositePreimageProjection R B (refinedOppositeParabolic R B S))

/-- The composite of the two block diagonal sections. -/
def composedOppositeLeviSection : refinedLevi R B S →* composedOppositeParabolic R B S :=
  (oppositePreimageSection R B (refinedOppositeParabolic R B S)).comp (refinedOppositeLeviSection R B S)

@[simp] theorem composedOppositeLeviSection_val (m : refinedLevi R B S) :
    (composedOppositeLeviSection R B S m).val = B.leviEmbedding R m.val := rfl

@[simp] theorem composedOppositeLeviProjection_section (m : refinedLevi R B S) :
    composedOppositeLeviProjection R B S (composedOppositeLeviSection R B S m) = m := by
  change refinedOppositeLeviProjection R B S
    (oppositePreimageProjection R B (refinedOppositeParabolic R B S)
      (oppositePreimageSection R B (refinedOppositeParabolic R B S) (refinedOppositeLeviSection R B S m))) = m
  rw [oppositePreimageProjection_section, refinedOppositeLeviProjection_section]

theorem composedOppositeLeviProjection_surjective :
    Function.Surjective (composedOppositeLeviProjection R B S) :=
  fun m => ⟨composedOppositeLeviSection R B S m, composedOppositeLeviProjection_section R B S m⟩

/-- The projection kernel maps onto exactly the full ambient radical. -/
theorem composedOppositeLeviProjection_ker_map :
    (composedOppositeLeviProjection R B S).ker.map (composedOppositeParabolic R B S).subtype =
      composedOppositeUnipotent R B S := by
  change (((refinedOppositeLeviProjection R B S).ker.comap
    (oppositePreimageProjection R B (refinedOppositeParabolic R B S))).map
      (oppositeLeviPreimage R B (refinedOppositeParabolic R B S)).subtype) = _
  rw [oppositePreimage_subgroup]
  change oppositeLeviPreimage R B ((refinedOppositeUnipotentRadical R B S).map
    (refinedOppositeParabolic R B S).subtype) = _
  rw [refinedOppositeUnipotentRadical_map]
  rfl

/-- Membership in the composite kernel is membership in the actual ambient radical. -/
theorem composedOppositeLeviProjection_ker :
    (composedOppositeLeviProjection R B S).ker =
      (composedOppositeUnipotent R B S).comap (composedOppositeParabolic R B S).subtype := by
  rw [← composedOppositeLeviProjection_ker_map R B S]
  exact (Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _).symm

theorem composedOppositeUnipotent_le_parabolic :
    composedOppositeUnipotent R B S ≤ composedOppositeParabolic R B S := by
  rw [← composedOppositeLeviProjection_ker_map R B S]
  rintro g ⟨h, _, rfl⟩
  exact h.property

/-- The composite parabolic normalizes its full ambient radical. -/
theorem composedOppositeParabolic_le_normalizer :
    composedOppositeParabolic R B S ≤
      Subgroup.normalizer (composedOppositeUnipotent R B S : Set (GeneralLinear n R)) := by
  rw [← composedOppositeLeviProjection_ker_map R B S]
  intro g hg
  apply Subgroup.le_normalizer_map _
  exact ⟨⟨g, hg⟩, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩

/-- The actual inner Levi acts on ambient radical coinvariants by this map. -/
def composedOppositeLeviNormalizer :
    refinedLevi R B S →*
      Subgroup.normalizer (composedOppositeUnipotent R B S : Set (GeneralLinear n R)) where
  toFun m := ⟨B.leviEmbedding R m.val,
    composedOppositeParabolic_le_normalizer R B S (composedOppositeLeviSection R B S m).property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[simp] theorem composedOppositeLeviNormalizer_val (m : refinedLevi R B S) :
    (composedOppositeLeviNormalizer R B S m).val = B.leviEmbedding R m.val := rfl

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

def composedOppositeLeviProjectionContinuous :
    ContinuousMonoidHom (composedOppositeParabolic R B S) (refinedLevi R B S) where
  toMonoidHom := composedOppositeLeviProjection R B S
  continuous_toFun := (refinedOppositeLeviProjectionContinuous R B S).continuous.comp
    (oppositePreimageProjectionContinuous R B (refinedOppositeParabolic R B S)).continuous

def composedOppositeLeviSectionContinuous :
    ContinuousMonoidHom (refinedLevi R B S) (composedOppositeParabolic R B S) where
  toMonoidHom := composedOppositeLeviSection R B S
  continuous_toFun := (oppositePreimageSectionContinuous R B (refinedOppositeParabolic R B S)).continuous.comp
    (refinedOppositeLeviSectionContinuous R B S).continuous

def composedOppositeLeviNormalizerContinuous :
    ContinuousMonoidHom (refinedLevi R B S)
      (Subgroup.normalizer (composedOppositeUnipotent R B S : Set (GeneralLinear n R))) where
  toMonoidHom := composedOppositeLeviNormalizer R B S
  continuous_toFun := ((B.leviEmbeddingContinuous R).continuous.comp
    continuous_subtype_val).subtype_mk _

end Topology
end Langlands.Parabolic
