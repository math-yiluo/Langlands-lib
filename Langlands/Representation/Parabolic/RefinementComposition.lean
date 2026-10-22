import Langlands.Representation.Parabolic.RefinementPreimage
import Langlands.Representation.Parabolic.RefinementCharacter
import Langlands.Representation.Geometric.RefinementDefinitions

/-! The actual composite parabolic for a refinement of an ordered block shape. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe u
variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The inner parabolic pulled back into the original matrix group. -/
def composedParabolic : Subgroup (GeneralLinear n R) :=
  leviPreimage R B (refinedParabolic R B S)

/-- The full radical: the outer radical together with the lifted inner radical. -/
def composedUnipotent : Subgroup (GeneralLinear n R) :=
  leviPreimage R B (refinedUnipotent R B S)

/-- The composite projection, with the actual inner Levi subgroup as codomain. -/
def composedLeviProjection : composedParabolic R B S →* refinedLevi R B S :=
  (refinedLeviProjection R B S).comp
    (preimageProjection R B (refinedParabolic R B S))

/-- The composite of the two block diagonal sections. -/
def composedLeviSection : refinedLevi R B S →* composedParabolic R B S :=
  (preimageSection R B (refinedParabolic R B S)).comp (refinedLeviSection R B S)

@[simp] theorem composedLeviSection_val (m : refinedLevi R B S) :
    (composedLeviSection R B S m).val = B.leviEmbedding R m.val := rfl

@[simp] theorem composedLeviProjection_section (m : refinedLevi R B S) :
    composedLeviProjection R B S (composedLeviSection R B S m) = m := by
  change refinedLeviProjection R B S
    (preimageProjection R B (refinedParabolic R B S)
      (preimageSection R B (refinedParabolic R B S) (refinedLeviSection R B S m))) = m
  rw [preimageProjection_section, refinedLeviProjection_section]

theorem composedLeviProjection_surjective :
    Function.Surjective (composedLeviProjection R B S) :=
  fun m => ⟨composedLeviSection R B S m, composedLeviProjection_section R B S m⟩

/-- The projection kernel maps onto exactly the full ambient radical. -/
theorem composedLeviProjection_ker_map :
    (composedLeviProjection R B S).ker.map (composedParabolic R B S).subtype =
      composedUnipotent R B S := by
  change (((refinedLeviProjection R B S).ker.comap
    (preimageProjection R B (refinedParabolic R B S))).map
      (leviPreimage R B (refinedParabolic R B S)).subtype) = _
  rw [preimage_subgroup]
  change leviPreimage R B ((refinedUnipotentRadical R B S).map
    (refinedParabolic R B S).subtype) = _
  rw [refinedUnipotentRadical_map]
  rfl

/-- Membership in the composite kernel is membership in the actual ambient radical. -/
theorem composedLeviProjection_ker :
    (composedLeviProjection R B S).ker =
      (composedUnipotent R B S).comap (composedParabolic R B S).subtype := by
  rw [← composedLeviProjection_ker_map R B S]
  exact (Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _).symm

theorem composedUnipotent_le_parabolic :
    composedUnipotent R B S ≤ composedParabolic R B S := by
  rw [← composedLeviProjection_ker_map R B S]
  rintro g ⟨h, _, rfl⟩
  exact h.property

/-- The composite parabolic normalizes its full ambient radical. -/
theorem composedParabolic_le_normalizer :
    composedParabolic R B S ≤
      Subgroup.normalizer (composedUnipotent R B S : Set (GeneralLinear n R)) := by
  rw [← composedLeviProjection_ker_map R B S]
  intro g hg
  apply Subgroup.le_normalizer_map _
  exact ⟨⟨g, hg⟩, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩

/-- The actual inner Levi acts on ambient radical coinvariants by this map. -/
def composedLeviNormalizer :
    refinedLevi R B S →*
      Subgroup.normalizer (composedUnipotent R B S : Set (GeneralLinear n R)) where
  toFun m := ⟨B.leviEmbedding R m.val,
    composedParabolic_le_normalizer R B S (composedLeviSection R B S m).property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[simp] theorem composedLeviNormalizer_val (m : refinedLevi R B S) :
    (composedLeviNormalizer R B S m).val = B.leviEmbedding R m.val := rfl

/-- The radical component obtained by removing the composite diagonal component. -/
def composedUnipotentPart (g : composedParabolic R B S) :
    (composedLeviProjection R B S).ker :=
  ⟨g * (composedLeviSection R B S (composedLeviProjection R B S g))⁻¹, by
    change composedLeviProjection R B S _ = 1
    simp⟩

/-- Unique radical-times-Levi factorization for the actual composite subgroup. -/
def composedDecomposition :
    composedParabolic R B S ≃
      (composedLeviProjection R B S).ker × refinedLevi R B S where
  toFun g := (composedUnipotentPart R B S g, composedLeviProjection R B S g)
  invFun um := um.1.val * composedLeviSection R B S um.2
  left_inv g := inv_mul_cancel_right _ _
  right_inv := by
    rintro ⟨u, m⟩
    have hu : composedLeviProjection R B S u.val = 1 := u.property
    have hp : composedLeviProjection R B S (u.val * composedLeviSection R B S m) = m := by
      simp [hu]
    apply Prod.ext
    · apply Subtype.ext
      change u.val * composedLeviSection R B S m *
        (composedLeviSection R B S (composedLeviProjection R B S
          (u.val * composedLeviSection R B S m)))⁻¹ = u.val
      rw [hp, mul_inv_cancel_right]
    · exact hp

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

def composedLeviProjectionContinuous :
    ContinuousMonoidHom (composedParabolic R B S) (refinedLevi R B S) where
  toMonoidHom := composedLeviProjection R B S
  continuous_toFun := (refinedLeviProjectionContinuous R B S).continuous.comp
    (preimageProjectionContinuous R B (refinedParabolic R B S)).continuous

def composedLeviSectionContinuous :
    ContinuousMonoidHom (refinedLevi R B S) (composedParabolic R B S) where
  toMonoidHom := composedLeviSection R B S
  continuous_toFun := (preimageSectionContinuous R B (refinedParabolic R B S)).continuous.comp
    (refinedLeviSectionContinuous R B S).continuous

def composedLeviNormalizerContinuous :
    ContinuousMonoidHom (refinedLevi R B S)
      (Subgroup.normalizer (composedUnipotent R B S : Set (GeneralLinear n R))) where
  toMonoidHom := composedLeviNormalizer R B S
  continuous_toFun := ((B.leviEmbeddingContinuous R).continuous.comp
    continuous_subtype_val).subtype_mk _

end Topology
end Langlands.Parabolic

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric Parabolic
open scoped NNReal

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
variable (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The outer modulus factors through the actual inner Levi projection. -/
theorem refinedOuterModulus_projection (q : refinedParabolic F.Carrier B S) :
    T.refinedOuterModulus B S (refinedLeviProjection F.Carrier B S q) =
      T.leviModulus B q.val := by
  have hu := T.leviModulus_refinedUnipotent B S
    ⟨(refinedUnipotentPart F.Carrier B S q).val.val,
      (mem_refinedUnipotentRadical F.Carrier B S _).mp
        (refinedUnipotentPart F.Carrier B S q).property⟩
  change T.leviModulus B
    (q.val * (refinedLeviProjection F.Carrier B S q).val⁻¹) = 1 at hu
  rw [map_mul, map_inv, mul_inv_eq_one] at hu
  exact hu.symm

theorem refinedOuterHalfModulus_projection (q : refinedParabolic F.Carrier B S) :
    T.refinedOuterHalfModulus B S (refinedLeviProjection F.Carrier B S q) =
      T.leviHalfModulus B q.val := by
  change Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (T.leviModulus B))
    (refinedLeviProjection F.Carrier B S q).val = _
  change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
    ((Units.map NNReal.sqrtHom.toMonoidHom)
      (T.refinedOuterModulus B S (refinedLeviProjection F.Carrier B S q))) = _
  rw [T.refinedOuterModulus_projection B S]
  rfl

/-- Product of the outer rectangular-block contributions and the inner contributions. -/
def composedLeviModulus : refinedLevi F.Carrier B S →* ℝ≥0ˣ :=
  T.refinedOuterModulus B S * T.refinedLeviModulus B S

/-- The canonical positive half, used for direct normalized induction. -/
def composedLeviHalfModulus : refinedLevi F.Carrier B S →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (T.composedLeviModulus B S))

theorem composedLeviHalfModulus_eq :
    T.composedLeviHalfModulus B S =
      T.refinedOuterHalfModulus B S * T.refinedLeviHalfModulus B S := by
  ext m
  simp [composedLeviHalfModulus, composedLeviModulus, refinedOuterHalfModulus,
    refinedOuterModulus, refinedLeviHalfModulus, leviHalfModulus,
    Jacquet.complexCharacter, Jacquet.positiveHalfCharacter]

/-- The Jacquet inverse half is the product of the two inverse halves. -/
theorem inverseHalf_composedLeviModulus :
    Jacquet.inverseHalfCharacter (T.composedLeviModulus B S) =
      (T.refinedOuterHalfModulus B S)⁻¹ * T.refinedLeviInverseHalfModulus B S := by
  change (T.composedLeviHalfModulus B S)⁻¹ =
    (T.refinedOuterHalfModulus B S)⁻¹ * (T.refinedLeviHalfModulus B S)⁻¹
  rw [T.composedLeviHalfModulus_eq]
  exact _root_.mul_inv (T.refinedOuterHalfModulus B S) (T.refinedLeviHalfModulus B S)

/-- The positive induction character on the actual composite parabolic. -/
def composedParabolicHalfModulus : composedParabolic F.Carrier B S →* ℂˣ :=
  (T.composedLeviHalfModulus B S).comp (composedLeviProjection F.Carrier B S)

theorem isOpen_ker_composedLeviModulus :
    let := T.topology
    IsOpen ((T.composedLeviModulus B S).ker : Set (refinedLevi F.Carrier B S)) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  apply Subgroup.isOpen_mono
    (show (T.refinedOuterModulus B S).ker ⊓ (T.refinedLeviModulus B S).ker ≤
      (T.composedLeviModulus B S).ker from ?_)
    ((T.isOpen_ker_refinedOuterModulus B S).inter (T.isOpen_ker_refinedLeviModulus B S))
  intro m hm
  change T.composedLeviModulus B S m = 1
  change T.refinedOuterModulus B S m * T.refinedLeviModulus B S m = 1
  rw [show T.refinedOuterModulus B S m = 1 from hm.1,
    show T.refinedLeviModulus B S m = 1 from hm.2, mul_one]

theorem isOpen_ker_composedLeviHalfModulus :
    let := T.topology
    IsOpen ((T.composedLeviHalfModulus B S).ker : Set (refinedLevi F.Carrier B S)) := by
  let := T.topology
  have he : (T.composedLeviHalfModulus B S).ker = (T.composedLeviModulus B S).ker := by
    ext m
    simpa only [MonoidHom.mem_ker, Jacquet.inverseHalfCharacter, MonoidHom.inv_apply,
      inv_eq_one, composedLeviHalfModulus] using
      Jacquet.inverseHalfCharacter_eq_one (T.composedLeviModulus B S) m
  rw [he]
  exact T.isOpen_ker_composedLeviModulus B S

theorem isOpen_ker_composedParabolicHalfModulus :
    let := T.topology
    IsOpen ((T.composedParabolicHalfModulus B S).ker :
      Set (composedParabolic F.Carrier B S)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (T.isOpen_ker_composedLeviHalfModulus B S).preimage
    (composedLeviProjectionContinuous F.Carrier B S).continuous

end Langlands.PadicField.TopologicalData
