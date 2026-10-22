import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Group.GL.BlockModulus

/-! Intrinsic projection and explicit modulus for a parabolic in a product Levi. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear

universe u
variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

@[simp] theorem mem_refinedParabolic (g : B.Levi R) :
    g ∈ refinedParabolic R B S ↔ ∀ i, g i ∈ (S i).parabolic R := by
  simp [refinedParabolic, Subgroup.mem_pi]

@[simp] theorem mem_refinedLevi (g : B.Levi R) :
    g ∈ refinedLevi R B S ↔ ∀ i, g i ∈ (S i).leviSubgroup R := by
  simp [refinedLevi, Subgroup.mem_pi]

@[simp] theorem mem_refinedUnipotent (g : B.Levi R) :
    g ∈ refinedUnipotent R B S ↔ ∀ i, g i ∈ (S i).unipotentSubgroup R := by
  simp [refinedUnipotent, Subgroup.mem_pi]

/-- Evaluate a refined parabolic element in one actual block parabolic. -/
def refinedParabolicEval (i : Fin B.length) :
    refinedParabolic R B S →* (S i).parabolic R where
  toFun g := ⟨g.val i, (mem_refinedParabolic R B S g.val).mp g.property i⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Evaluate a refined Levi element in one actual diagonal matrix subgroup. -/
def refinedLeviEval (i : Fin B.length) :
    refinedLevi R B S →* (S i).leviSubgroup R where
  toFun m := ⟨m.val i, (mem_refinedLevi R B S m.val).mp m.property i⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The nested product is explicitly identified with the existing subgroup. -/
def refinedLeviEquiv : (∀ i, (S i).Levi R) ≃* refinedLevi R B S where
  toFun m := ⟨fun i => (S i).leviEmbedding R (m i), by
    simp only [mem_refinedLevi]
    exact fun i => ⟨m i, rfl⟩⟩
  invFun m i := (S i).leviEquiv R |>.symm <| refinedLeviEval R B S i m
  left_inv m := by
    funext i
    exact (S i).leviEquiv R |>.left_inv (m i)
  right_inv m := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val ((S i).leviEquiv R |>.right_inv
      (refinedLeviEval R B S i m))
  map_mul' m m' := by
    apply Subtype.ext
    funext i
    exact (S i).leviEmbedding R |>.map_mul (m i) (m' i)

/-- The projection has the actual refined subgroup as codomain. -/
def refinedLeviProjection : refinedParabolic R B S →* refinedLevi R B S :=
  (refinedLeviEquiv R B S).toMonoidHom.comp
    (MonoidHom.pi fun i => ((S i).leviProjection R).comp (refinedParabolicEval R B S i))

/-- The section is the inclusion of the existing diagonal subgroup. -/
def refinedLeviSection : refinedLevi R B S →* refinedParabolic R B S where
  toFun m := ⟨m.val, by
    rw [mem_refinedParabolic]
    exact fun i => ((S i).leviAsParabolic R (refinedLeviEval R B S i m)).property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem refinedLeviSection_val (m : refinedLevi R B S) :
    (refinedLeviSection R B S m).val = m.val := rfl

@[simp] theorem refinedLeviProjection_section (m : refinedLevi R B S) :
    refinedLeviProjection R B S (refinedLeviSection R B S m) = m := by
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val ((S i).leviEquiv R |>.apply_symm_apply
    (refinedLeviEval R B S i m))

/-- The radical as a normal subgroup of the actual refined parabolic. -/
def refinedUnipotentRadical : Subgroup (refinedParabolic R B S) :=
  (refinedLeviProjection R B S).ker

instance refinedUnipotentRadical_normal : (refinedUnipotentRadical R B S).Normal :=
  inferInstanceAs (refinedLeviProjection R B S).ker.Normal

private theorem block_mem_radical (i : Fin B.length) (g : (S i).parabolic R) :
    g.val ∈ (S i).unipotentSubgroup R ↔ (S i).leviProjection R g = 1 := by
  constructor
  · rintro ⟨h, hh, he⟩
    have e : h = g := Subtype.ext he
    subst h
    exact hh
  · intro h
    exact ⟨g, h, rfl⟩

/-- The kernel condition is exactly membership in the published product radical. -/
theorem mem_refinedUnipotentRadical (g : refinedParabolic R B S) :
    g ∈ refinedUnipotentRadical R B S ↔ g.val ∈ refinedUnipotent R B S := by
  change refinedLeviProjection R B S g = 1 ↔ _
  rw [mem_refinedUnipotent]
  constructor
  · intro h i
    apply (block_mem_radical R B S i (refinedParabolicEval R B S i g)).mpr
    have e := congrArg (fun m => (refinedLeviEquiv R B S).symm m i) h
    simpa [refinedLeviProjection] using e
  · intro h
    have e : (fun i => (S i).leviProjection R (refinedParabolicEval R B S i g)) = 1 := by
      funext i
      exact (block_mem_radical R B S i (refinedParabolicEval R B S i g)).mp (h i)
    change refinedLeviEquiv R B S (fun i => (S i).leviProjection R
      (refinedParabolicEval R B S i g)) = 1
    rw [e, map_one]

theorem refinedUnipotent_le_parabolic :
    refinedUnipotent R B S ≤ refinedParabolic R B S := by
  intro g hg
  rw [mem_refinedParabolic]
  intro i
  rcases (mem_refinedUnipotent R B S g).mp hg i with ⟨h, _, he⟩
  exact he ▸ h.property

/-- The kernel's ambient image is precisely the previously defined radical. -/
theorem refinedUnipotentRadical_map :
    (refinedUnipotentRadical R B S).map (refinedParabolic R B S).subtype =
      refinedUnipotent R B S := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (mem_refinedUnipotentRadical R B S h).mp hh
  · intro hg
    exact ⟨⟨g, refinedUnipotent_le_parabolic R B S hg⟩,
      (mem_refinedUnipotentRadical R B S _).mpr hg, rfl⟩

/-- The radical in the parabolic is also its intrinsic subgroup preimage. -/
theorem refinedLeviProjection_ker :
    (refinedLeviProjection R B S).ker =
      (refinedUnipotent R B S).comap (refinedParabolic R B S).subtype := by
  ext g
  exact mem_refinedUnipotentRadical R B S g

/-- Every parabolic element normalizes the ambient radical. -/
theorem refinedParabolic_le_normalizer :
    refinedParabolic R B S ≤ Subgroup.normalizer (refinedUnipotent R B S : Set (B.Levi R)) := by
  intro g hg
  rw [← refinedUnipotentRadical_map R B S]
  apply Subgroup.le_normalizer_map _
  exact ⟨⟨g, hg⟩, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩

/-- The actual Levi inclusion into the normalizer used by Jacquet actions. -/
def refinedLeviNormalizer :
    refinedLevi R B S →* Subgroup.normalizer (refinedUnipotent R B S : Set (B.Levi R)) where
  toFun m := ⟨m.val, refinedParabolic_le_normalizer R B S
    (refinedLeviSection R B S m).property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem refinedLeviNormalizer_val (m : refinedLevi R B S) :
    (refinedLeviNormalizer R B S m).val = m.val := rfl

/-- Removing the diagonal part on the right leaves an actual radical element. -/
def refinedUnipotentPart (g : refinedParabolic R B S) : refinedUnipotentRadical R B S :=
  ⟨g * (refinedLeviSection R B S (refinedLeviProjection R B S g))⁻¹, by
    change refinedLeviProjection R B S _ = 1
    simp⟩

/-- The unique factorization into a radical element and a refined Levi element. -/
def refinedDecomposition :
    refinedParabolic R B S ≃ refinedUnipotentRadical R B S × refinedLevi R B S where
  toFun g := (refinedUnipotentPart R B S g, refinedLeviProjection R B S g)
  invFun um := um.1.val * refinedLeviSection R B S um.2
  left_inv g := inv_mul_cancel_right _ _
  right_inv := by
    rintro ⟨u, m⟩
    have hu : refinedLeviProjection R B S u.val = 1 := u.property
    have hp : refinedLeviProjection R B S (u.val * refinedLeviSection R B S m) = m := by
      simp [hu]
    apply Prod.ext
    · apply Subtype.ext
      change u.val * refinedLeviSection R B S m *
        (refinedLeviSection R B S (refinedLeviProjection R B S
          (u.val * refinedLeviSection R B S m)))⁻¹ = u.val
      rw [hp, mul_inv_cancel_right]
    · exact hp

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
theorem continuous_refinedParabolicEval (i : Fin B.length) :
    Continuous (refinedParabolicEval R B S i) :=
  ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

omit [IsTopologicalRing R] in
theorem continuous_refinedLeviEval (i : Fin B.length) :
    Continuous (refinedLeviEval R B S i) :=
  ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

/-- The nested product identification respects the actual subgroup topology. -/
def refinedLeviEquivContinuous : (∀ i, (S i).Levi R) ≃ₜ* refinedLevi R B S where
  toMulEquiv := refinedLeviEquiv R B S
  continuous_toFun := (continuous_pi fun i =>
    ((S i).leviEmbeddingContinuous R).continuous.comp (continuous_apply i)).subtype_mk _
  continuous_invFun := continuous_pi fun i =>
    ((S i).leviEquivContinuous R).symm.continuous.comp
      (continuous_refinedLeviEval R B S i)

/-- The actual refined Levi projection is continuous. -/
def refinedLeviProjectionContinuous :
    ContinuousMonoidHom (refinedParabolic R B S) (refinedLevi R B S) where
  toMonoidHom := refinedLeviProjection R B S
  continuous_toFun := (refinedLeviEquivContinuous R B S).continuous.comp
    (continuous_pi fun i => ((S i).leviProjectionContinuous R).continuous.comp
      (continuous_refinedParabolicEval R B S i))

/-- The actual inclusion section is continuous. -/
def refinedLeviSectionContinuous :
    ContinuousMonoidHom (refinedLevi R B S) (refinedParabolic R B S) where
  toMonoidHom := refinedLeviSection R B S
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The radical-normalizer inclusion has the subgroup topology. -/
def refinedLeviNormalizerContinuous :
    ContinuousMonoidHom (refinedLevi R B S)
      (Subgroup.normalizer (refinedUnipotent R B S : Set (B.Levi R))) where
  toMonoidHom := refinedLeviNormalizer R B S
  continuous_toFun := continuous_subtype_val.subtype_mk _

end Topology
end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open Geometric
open scoped BigOperators NNReal

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (S : BlockRefinement B)

/-- The inner block coordinates of one actual refined Levi element. -/
def refinedLeviBlock (i : Fin B.length) :
    refinedLevi F.Carrier B S →* (S i).Levi F.Carrier :=
  ((S i).leviEquiv F.Carrier).symm.toMonoidHom.comp (refinedLeviEval F.Carrier B S i)

/-- Product of the published explicit positive moduli of the inner parabolics. -/
def refinedLeviModulus : refinedLevi F.Carrier B S →* ℝ≥0ˣ :=
  ∏ i : Fin B.length, (T.leviModulus (S i)).comp (refinedLeviBlock B S i)

theorem refinedLeviModulus_apply (m : refinedLevi F.Carrier B S) :
    T.refinedLeviModulus B S m =
      ∏ i : Fin B.length, T.leviModulus (S i) (refinedLeviBlock B S i m) := by
  simp [refinedLeviModulus]

/-- Inflation through the actual subgroup-valued projection. -/
def refinedParabolicModulus : refinedParabolic F.Carrier B S →* ℝ≥0ˣ :=
  (T.refinedLeviModulus B S).comp (refinedLeviProjection F.Carrier B S)

@[simp] theorem refinedParabolicModulus_apply (g : refinedParabolic F.Carrier B S) :
    T.refinedParabolicModulus B S g =
      T.refinedLeviModulus B S (refinedLeviProjection F.Carrier B S g) := rfl

@[simp] theorem refinedParabolicModulus_section (m : refinedLevi F.Carrier B S) :
    T.refinedParabolicModulus B S (refinedLeviSection F.Carrier B S m) =
      T.refinedLeviModulus B S m := by simp

@[simp] theorem refinedParabolicModulus_unipotent
    (u : refinedUnipotentRadical F.Carrier B S) :
    T.refinedParabolicModulus B S u = 1 := by
  have hu : refinedLeviProjection F.Carrier B S u.val = 1 := u.property
  simp [hu]

/-- Positive complex half of the full product modulus, for induction. -/
def refinedLeviHalfModulus : refinedLevi F.Carrier B S →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (T.refinedLeviModulus B S))

/-- Canonical inverse half of the same full modulus, for Jacquet normalization. -/
def refinedLeviInverseHalfModulus : refinedLevi F.Carrier B S →* ℂˣ :=
  Jacquet.inverseHalfCharacter (T.refinedLeviModulus B S)

/-- The positive half on the refined parabolic. -/
def refinedParabolicHalfModulus : refinedParabolic F.Carrier B S →* ℂˣ :=
  (T.refinedLeviHalfModulus B S).comp (refinedLeviProjection F.Carrier B S)

/-- The inverse half on the refined parabolic. -/
def refinedParabolicInverseHalfModulus : refinedParabolic F.Carrier B S →* ℂˣ :=
  (T.refinedLeviInverseHalfModulus B S).comp (refinedLeviProjection F.Carrier B S)

@[simp] theorem refinedLeviHalfModulus_apply (m : refinedLevi F.Carrier B S) :
    (T.refinedLeviHalfModulus B S m : ℂ) =
      ((NNReal.sqrt (T.refinedLeviModulus B S m : ℝ≥0) : ℝ) : ℂ) := rfl

@[simp] theorem refinedLeviInverseHalfModulus_apply (m : refinedLevi F.Carrier B S) :
    (T.refinedLeviInverseHalfModulus B S m : ℂ) =
      (((NNReal.sqrt (T.refinedLeviModulus B S m : ℝ≥0) : ℝ) : ℂ))⁻¹ :=
  Jacquet.inverseHalfCharacter_apply _ _

theorem refinedLeviHalfModulus_sq (m : refinedLevi F.Carrier B S) :
    T.refinedLeviHalfModulus B S m ^ 2 =
      Jacquet.complexCharacter (T.refinedLeviModulus B S) m := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, refinedLeviHalfModulus_apply,
    Jacquet.complexCharacter_apply]
  norm_cast
  exact NNReal.sq_sqrt _

theorem refinedLeviInverseHalfModulus_sq (m : refinedLevi F.Carrier B S) :
    T.refinedLeviInverseHalfModulus B S m ^ 2 =
      (Jacquet.complexCharacter (T.refinedLeviModulus B S) m)⁻¹ :=
  Jacquet.inverseHalfCharacter_sq _ _

theorem refinedLeviInverseHalfModulus_eq_inv :
    T.refinedLeviInverseHalfModulus B S = (T.refinedLeviHalfModulus B S)⁻¹ := rfl

@[simp] theorem refinedParabolicHalfModulus_apply (g : refinedParabolic F.Carrier B S) :
    T.refinedParabolicHalfModulus B S g =
      T.refinedLeviHalfModulus B S (refinedLeviProjection F.Carrier B S g) := rfl

@[simp] theorem refinedParabolicInverseHalfModulus_apply (g : refinedParabolic F.Carrier B S) :
    T.refinedParabolicInverseHalfModulus B S g =
      T.refinedLeviInverseHalfModulus B S (refinedLeviProjection F.Carrier B S g) := rfl

@[simp] theorem refinedParabolicHalfModulus_section (m : refinedLevi F.Carrier B S) :
    T.refinedParabolicHalfModulus B S (refinedLeviSection F.Carrier B S m) =
      T.refinedLeviHalfModulus B S m := by simp

@[simp] theorem refinedParabolicInverseHalfModulus_section (m : refinedLevi F.Carrier B S) :
    T.refinedParabolicInverseHalfModulus B S (refinedLeviSection F.Carrier B S m) =
      T.refinedLeviInverseHalfModulus B S m := by simp

@[simp] theorem refinedParabolicHalfModulus_unipotent
    (u : refinedUnipotentRadical F.Carrier B S) :
    T.refinedParabolicHalfModulus B S u = 1 := by
  have hu : refinedLeviProjection F.Carrier B S u.val = 1 := u.property
  simp [hu]

@[simp] theorem refinedParabolicInverseHalfModulus_unipotent
    (u : refinedUnipotentRadical F.Carrier B S) :
    T.refinedParabolicInverseHalfModulus B S u = 1 := by
  have hu : refinedLeviProjection F.Carrier B S u.val = 1 := u.property
  simp [hu]

theorem refinedLeviHalfModulus_ker :
    (T.refinedLeviHalfModulus B S).ker = (T.refinedLeviModulus B S).ker := by
  ext m
  simpa only [MonoidHom.mem_ker, Jacquet.inverseHalfCharacter, MonoidHom.inv_apply,
    inv_eq_one, refinedLeviHalfModulus] using
    Jacquet.inverseHalfCharacter_eq_one (T.refinedLeviModulus B S) m

theorem refinedLeviInverseHalfModulus_ker :
    (T.refinedLeviInverseHalfModulus B S).ker = (T.refinedLeviModulus B S).ker :=
  Jacquet.inverseHalfCharacter_ker _

/-- The compatible field topology makes inner-block evaluation continuous. -/
theorem continuous_refinedLeviBlock (i : Fin B.length) :
    let := T.topology
    Continuous (refinedLeviBlock (F := F) B S i) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact ((S i).leviEquivContinuous F.Carrier).symm.continuous.comp
    (continuous_refinedLeviEval F.Carrier B S i)

/-- The finite intersection of factor kernels is an open subgroup of the full kernel. -/
theorem isOpen_ker_refinedLeviModulus :
    let := T.topology
    IsOpen ((T.refinedLeviModulus B S).ker : Set (refinedLevi F.Carrier B S)) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let K : Subgroup (refinedLevi F.Carrier B S) :=
    ⨅ i : Fin B.length, ((T.leviModulus (S i)).comp (refinedLeviBlock B S i)).ker
  have hK : IsOpen (K : Set (refinedLevi F.Carrier B S)) := by
    have h : ∀ i : Fin B.length,
        IsOpen {m : refinedLevi F.Carrier B S |
          T.leviModulus (S i) (refinedLeviBlock B S i m) = 1} := fun i =>
      (T.isOpen_ker_leviModulus (S i)).preimage (T.continuous_refinedLeviBlock B S i)
    convert isOpen_iInter_of_finite h using 1
    ext m
    simp [K]
  apply Subgroup.isOpen_mono (show K ≤ (T.refinedLeviModulus B S).ker from ?_) hK
  intro m hm
  have h : ∀ i, T.leviModulus (S i) (refinedLeviBlock B S i m) = 1 := by
    simpa only [K, Subgroup.mem_iInf, MonoidHom.mem_ker, MonoidHom.comp_apply] using hm
  change T.refinedLeviModulus B S m = 1
  simp [T.refinedLeviModulus_apply B S, h]

theorem continuous_refinedLeviModulus :
    let := T.topology
    Continuous (T.refinedLeviModulus B S) := by
  let := T.topology
  change Continuous (fun m => T.refinedLeviModulus B S m)
  simp_rw [T.refinedLeviModulus_apply B S]
  exact continuous_finsetProd _ fun i _ =>
    (T.continuous_leviModulus (S i)).comp (T.continuous_refinedLeviBlock B S i)

theorem isOpen_ker_refinedLeviHalfModulus :
    let := T.topology
    IsOpen ((T.refinedLeviHalfModulus B S).ker : Set (refinedLevi F.Carrier B S)) := by
  let := T.topology
  rw [T.refinedLeviHalfModulus_ker]
  exact T.isOpen_ker_refinedLeviModulus B S

theorem isOpen_ker_refinedLeviInverseHalfModulus :
    let := T.topology
    IsOpen ((T.refinedLeviInverseHalfModulus B S).ker : Set (refinedLevi F.Carrier B S)) := by
  let := T.topology
  rw [T.refinedLeviInverseHalfModulus_ker]
  exact T.isOpen_ker_refinedLeviModulus B S

theorem continuous_refinedLeviHalfModulus :
    let := T.topology
    Continuous (T.refinedLeviHalfModulus B S) := by
  let := T.topology
  exact ((Complex.continuous_ofReal.comp NNReal.continuous_coe).units_map
    (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom).comp
    ((NNReal.continuous_sqrt.units_map NNReal.sqrtHom.toMonoidHom).comp
      (T.continuous_refinedLeviModulus B S))

theorem continuous_refinedLeviInverseHalfModulus :
    let := T.topology
    Continuous (T.refinedLeviInverseHalfModulus B S) := by
  let := T.topology
  exact (T.continuous_refinedLeviHalfModulus B S).inv

theorem isOpen_ker_refinedParabolicModulus :
    let := T.topology
    IsOpen ((T.refinedParabolicModulus B S).ker : Set (refinedParabolic F.Carrier B S)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (T.isOpen_ker_refinedLeviModulus B S).preimage
    (refinedLeviProjectionContinuous F.Carrier B S).continuous

theorem isOpen_ker_refinedParabolicHalfModulus :
    let := T.topology
    IsOpen ((T.refinedParabolicHalfModulus B S).ker : Set (refinedParabolic F.Carrier B S)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (T.isOpen_ker_refinedLeviHalfModulus B S).preimage
    (refinedLeviProjectionContinuous F.Carrier B S).continuous

theorem isOpen_ker_refinedParabolicInverseHalfModulus :
    let := T.topology
    IsOpen ((T.refinedParabolicInverseHalfModulus B S).ker : Set (refinedParabolic F.Carrier B S)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (T.isOpen_ker_refinedLeviInverseHalfModulus B S).preimage
    (refinedLeviProjectionContinuous F.Carrier B S).continuous

theorem continuous_refinedParabolicModulus :
    let := T.topology
    Continuous (T.refinedParabolicModulus B S) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (T.continuous_refinedLeviModulus B S).comp
    (refinedLeviProjectionContinuous F.Carrier B S).continuous

theorem continuous_refinedParabolicHalfModulus :
    let := T.topology
    Continuous (T.refinedParabolicHalfModulus B S) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (T.continuous_refinedLeviHalfModulus B S).comp
    (refinedLeviProjectionContinuous F.Carrier B S).continuous

theorem continuous_refinedParabolicInverseHalfModulus :
    let := T.topology
    Continuous (T.refinedParabolicInverseHalfModulus B S) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (T.continuous_refinedLeviInverseHalfModulus B S).comp
    (refinedLeviProjectionContinuous F.Carrier B S).continuous

/-- Independence of the compatible realization follows from the block formula. -/
theorem refinedLeviModulus_eq (U : F.TopologicalData) :
    T.refinedLeviModulus B S = U.refinedLeviModulus B S := by
  simp only [refinedLeviModulus, T.leviModulus_eq _ U]

end Langlands.PadicField.TopologicalData
