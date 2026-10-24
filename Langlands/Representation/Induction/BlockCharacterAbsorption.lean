import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Twist.AlgebraProof
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Group.GL.UpperUnipotent

/-! # Absorbing the normalizing character into the block factors -/

noncomputable section
open scoped BigOperators

namespace Langlands.Induction.SmoothCharacter

universe uR uI uG uV
variable {R : Type uR} [CommRing R]
variable {ι : Type uI} [DecidableEq ι]
variable {H : ι → Type uG} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]

/-- Restriction of a smooth product character to a single coordinate. -/
def coordinate (χ : SmoothCharacter R (∀ i, H i)) (i : ι) : SmoothCharacter R (H i) where
  toMonoidHom := χ.toMonoidHom.comp (MonoidHom.mulSingle H i)
  isOpen_ker := χ.isOpen_ker.preimage (continuous_mulSingle i)

@[simp] theorem coordinate_apply (χ : SmoothCharacter R (∀ i, H i)) (i : ι) (g : H i) :
    (χ.coordinate i).toMonoidHom g = χ.toMonoidHom (Pi.mulSingle i g) := rfl

/-- Inversion preserves the open kernel. -/
def inverse {G : Type uG} [Group G] [TopologicalSpace G] (χ : SmoothCharacter R G) :
    SmoothCharacter R G where
  toMonoidHom := χ.toMonoidHom⁻¹
  isOpen_ker := by
    have h : χ.toMonoidHom⁻¹.ker = χ.toMonoidHom.ker := by
      ext g
      simp
    rw [h]
    exact χ.isOpen_ker

@[simp] theorem inverse_apply {G : Type uG} [Group G] [TopologicalSpace G]
    (χ : SmoothCharacter R G) (g : G) :
    χ.inverse.toMonoidHom g = (χ.toMonoidHom g)⁻¹ := rfl

variable [Fintype ι]

/-- A character of a finite product factors as the product of its coordinate restrictions.
The component groups need not be commutative. -/
theorem factorization (χ : SmoothCharacter R (∀ i, H i)) (g : ∀ i, H i) :
    χ.toMonoidHom g = ∏ i, (χ.coordinate i).toMonoidHom (g i) := by
  have aux : ∀ (s : Finset ι) (g : ∀ i, H i),
      (∀ i, i ∉ s → g i = 1) →
      χ.toMonoidHom g = ∏ i ∈ s, χ.toMonoidHom (Pi.mulSingle i (g i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have he : g = 1 := funext (fun i => hg i (by simp))
      simp [he]
    | @insert a s ha ih =>
      intro g hg
      let g' := Function.update g a 1
      have he : g = Pi.mulSingle a (g a) * g' := by
        funext i
        by_cases hi : i = a
        · subst i; simp [g']
        · simp [g', hi]
      have hs : ∀ i, i ∉ s → g' i = 1 := by
        intro i hi
        by_cases hia : i = a
        · subst i; simp [g']
        · simpa [g', hia] using hg i (by simp [hia, hi])
      nth_rw 1 [he]
      rw [map_mul, ih g' hs, Finset.prod_insert ha]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      simp [g', hia]
  exact aux Finset.univ g (by simp)

variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- Twisting each tensor factor by its coordinate character absorbs the whole character. -/
theorem external_coordinate_twist (χ : SmoothCharacter R (∀ i, H i))
    (σ : ∀ i, Representation R (H i) (V i)) :
    FiniteTensor.external (fun i => twist (χ.coordinate i).toMonoidHom (σ i)) =
      twist χ.toMonoidHom (FiniteTensor.external σ) := by
  ext g v
  change FiniteTensor.external _ g (PiTensorProduct.tprod R v) =
    (χ.toMonoidHom g : R) • FiniteTensor.external σ g (PiTensorProduct.tprod R v)
  rw [FiniteTensor.external_tprod, FiniteTensor.external_tprod]
  change PiTensorProduct.tprod R (fun i =>
      ((χ.coordinate i).toMonoidHom (g i) : R) • σ i (g i) (v i)) =
    (χ.toMonoidHom g : R) • PiTensorProduct.tprod R (fun i => σ i (g i) (v i))
  rw [(PiTensorProduct.tprod R).map_smul_univ, χ.factorization g]
  simp

end Langlands.Induction.SmoothCharacter

namespace Langlands.PadicField.TopologicalData

universe uF uV
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The positive half Levi modulus restricted to the actual `i`th block. -/
def blockHalfModulus (i : Fin B.length) : GeneralLinear (B.size i) F.Carrier →* ℂˣ :=
  (T.leviHalfModulus B).comp (MonoidHom.mulSingle (fun j => GeneralLinear (B.size j) F.Carrier) i)

/-- The inverse half character on the actual `i`th block. -/
def blockInverseHalfModulus (i : Fin B.length) : GeneralLinear (B.size i) F.Carrier →* ℂˣ :=
  (T.blockHalfModulus B i)⁻¹

/-- Coordinate restriction carries its open-kernel certificate. -/
def blockHalfCharacter (i : Fin B.length) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (GeneralLinear (B.size i) F.Carrier) :=
  letI := T.topology
  (T.leviHalfCharacter B).coordinate i

/-- Inverting the coordinate restriction retains its open-kernel certificate. -/
def blockInverseHalfCharacter (i : Fin B.length) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (GeneralLinear (B.size i) F.Carrier) :=
  letI := T.topology
  (T.blockHalfCharacter B i).inverse

@[simp] theorem blockHalfCharacter_toMonoidHom (i : Fin B.length) :
    letI := T.topology
    (T.blockHalfCharacter B i).toMonoidHom = T.blockHalfModulus B i := rfl

@[simp] theorem blockInverseHalfCharacter_toMonoidHom (i : Fin B.length) :
    letI := T.topology
    (T.blockInverseHalfCharacter B i).toMonoidHom = T.blockInverseHalfModulus B i := rfl

theorem isOpen_ker_blockHalfModulus (i : Fin B.length) :
    letI := T.topology
    IsOpen ((T.blockHalfModulus B i).ker : Set (GeneralLinear (B.size i) F.Carrier)) :=
  letI := T.topology
  (T.blockHalfCharacter B i).isOpen_ker

theorem isOpen_ker_blockInverseHalfModulus (i : Fin B.length) :
    letI := T.topology
    IsOpen ((T.blockInverseHalfModulus B i).ker : Set (GeneralLinear (B.size i) F.Carrier)) :=
  letI := T.topology
  (T.blockInverseHalfCharacter B i).isOpen_ker

@[simp] theorem blockHalfModulus_apply (i : Fin B.length)
    (g : GeneralLinear (B.size i) F.Carrier) :
    T.blockHalfModulus B i g = T.leviHalfModulus B (Pi.mulSingle i g) := rfl

@[simp] theorem blockInverseHalfModulus_apply (i : Fin B.length)
    (g : GeneralLinear (B.size i) F.Carrier) :
    T.blockInverseHalfModulus B i g = (T.blockHalfModulus B i g)⁻¹ := rfl

/-- The product of the canonical block restrictions is the canonical Levi half modulus. -/
theorem blockHalfModulus_factorization (m : B.Levi F.Carrier) :
    T.leviHalfModulus B m = ∏ i, T.blockHalfModulus B i (m i) := by
  let := T.topology
  exact (T.leviHalfCharacter B).factorization m

theorem blockInverseHalfModulus_factorization (m : B.Levi F.Carrier) :
    (T.leviHalfModulus B m)⁻¹ = ∏ i, T.blockInverseHalfModulus B i (m i) := by
  let := T.topology
  exact (T.leviHalfCharacter B).inverse.factorization m

/-- The coordinate half modulus is one on the actual standard upper unipotent subgroup. -/
@[simp] theorem blockHalfModulus_upperUnipotent (i : Fin B.length)
    (u : GeneralLinear.upperUnipotent (B.size i) F.Carrier) :
    T.blockHalfModulus B i u.val = 1 := by
  rw [T.blockHalfModulus_apply, T.leviHalfModulus_eq_one]
  apply T.normOneLevi_le_ker_leviModulus B
  rw [T.mem_normOneLevi]
  intro j
  by_cases h : j = i
  · subst j
    simp only [Pi.mulSingle_eq_same]
    have hdet : GeneralLinear.determinant u.val = 1 := by
      apply Units.ext
      change Matrix.det u.val.val = 1
      rw [Matrix.det_of_isUpperTriangular u.property.1]
      simp only [GeneralLinear.UpperUnipotent.entry_diag, Finset.prod_const_one]
    change T.normalizedAbsUnits (GeneralLinear.determinant u.val) = 1
    rw [hdet, map_one]
  · simp [Pi.mulSingle_eq_of_ne h]

@[simp] theorem blockInverseHalfModulus_upperUnipotent (i : Fin B.length)
    (u : GeneralLinear.upperUnipotent (B.size i) F.Carrier) :
    T.blockInverseHalfModulus B i u.val = 1 := by
  rw [T.blockInverseHalfModulus_apply, T.blockHalfModulus_upperUnipotent, inv_one]

variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Positive half twists of the supplied block representations, on their original carriers. -/
def blockHalfTwist (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :=
  fun i => twist (T.blockHalfModulus B i) (σ i)

/-- Inverse half twists of the supplied block representations. -/
def blockInverseHalfTwist
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :=
  fun i => twist (T.blockInverseHalfModulus B i) (σ i)

theorem blockTensor_halfTwist
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    B.blockTensor (T.blockHalfTwist B σ) = twist (T.leviHalfModulus B) (B.blockTensor σ) := by
  let := T.topology
  exact (T.leviHalfCharacter B).external_coordinate_twist σ

theorem blockTensor_inverseHalfTwist
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    B.blockTensor (T.blockInverseHalfTwist B σ) =
      twist (T.leviHalfModulus B)⁻¹ (B.blockTensor σ) := by
  let := T.topology
  exact (T.leviHalfCharacter B).inverse.external_coordinate_twist σ

/-- The actual parabolic covariance actions coincide after positive absorption. -/
theorem halfAbsorptionInducing_eq
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier)) =
      (B.blockTensor (T.blockHalfTwist B σ)).comp (B.leviProjection F.Carrier) := by
  rw [T.blockTensor_halfTwist]
  rfl

/-- Inverse half twists cancel the normalization in the actual covariance action. -/
theorem inverseHalfAbsorptionInducing_eq
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    twist (T.parabolicHalfModulus B)
        ((B.blockTensor (T.blockInverseHalfTwist B σ)).comp (B.leviProjection F.Carrier)) =
      (B.blockTensor σ).comp (B.leviProjection F.Carrier) := by
  rw [T.blockTensor_inverseHalfTwist]
  change (twist (T.leviHalfModulus B) (twist (T.leviHalfModulus B)⁻¹
    (B.blockTensor σ))).comp (B.leviProjection F.Carrier) = _
  rw [twist_twist_inv]

/-- Identity on tensor values, regarded as an equivalence of the parabolic actions. -/
def halfAbsorptionInducingEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    (twist (T.parabolicHalfModulus B)
      ((B.blockTensor σ).comp (B.leviProjection F.Carrier))).Equiv
      ((B.blockTensor (T.blockHalfTwist B σ)).comp (B.leviProjection F.Carrier)) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    change (twist (T.parabolicHalfModulus B)
      ((B.blockTensor σ).comp (B.leviProjection F.Carrier))) g = _
    rw [T.halfAbsorptionInducing_eq]
    rfl

/-- Identity on tensor values after inverse normalization. -/
def inverseHalfAbsorptionInducingEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    (twist (T.parabolicHalfModulus B)
      ((B.blockTensor (T.blockInverseHalfTwist B σ)).comp (B.leviProjection F.Carrier))).Equiv
      ((B.blockTensor σ).comp (B.leviProjection F.Carrier)) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    change (twist (T.parabolicHalfModulus B)
      ((B.blockTensor (T.blockInverseHalfTwist B σ)).comp (B.leviProjection F.Carrier))) g = _
    rw [T.inverseHalfAbsorptionInducing_eq]
    rfl

/-- Absorb positive normalization into the actual block factors. -/
def normalizedProductHalfAbsorptionEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B σ).Equiv
      (Induction.smoothInduced (B.parabolic F.Carrier)
        ((B.blockTensor (T.blockHalfTwist B σ)).comp (B.leviProjection F.Carrier))) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.smoothInducedEquiv _ (T.halfAbsorptionInducingEquiv B σ)

/-- Normalize inverse-half-twisted factors to recover the original unnormalized induction. -/
def normalizedProductInverseHalfAbsorptionEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B (T.blockInverseHalfTwist B σ)).Equiv
      (Induction.smoothInduced (B.parabolic F.Carrier)
        ((B.blockTensor σ).comp (B.leviProjection F.Carrier))) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.smoothInducedEquiv _ (T.inverseHalfAbsorptionInducingEquiv B σ)

/-- Both directions of positive absorption preserve every value of the induced function. -/
@[simp] theorem normalizedProductHalfAbsorptionEquiv_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier))))
    (g : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ (T.normalizedProductHalfAbsorptionEquiv B σ f) g =
      Induction.eval _ _ f g := rfl

@[simp] theorem normalizedProductHalfAbsorptionEquiv_symm_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        ((B.blockTensor (T.blockHalfTwist B σ)).comp (B.leviProjection F.Carrier)))
    (g : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ ((T.normalizedProductHalfAbsorptionEquiv B σ).symm f) g =
      Induction.eval _ _ f g := rfl

/-- Both directions of inverse absorption also preserve every function value. -/
@[simp] theorem normalizedProductInverseHalfAbsorptionEquiv_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor (T.blockInverseHalfTwist B σ)).comp (B.leviProjection F.Carrier))))
    (g : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ (T.normalizedProductInverseHalfAbsorptionEquiv B σ f) g =
      Induction.eval _ _ f g := rfl

@[simp] theorem normalizedProductInverseHalfAbsorptionEquiv_symm_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))
    (g : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ ((T.normalizedProductInverseHalfAbsorptionEquiv B σ).symm f) g =
      Induction.eval _ _ f g := rfl

/-- Admissibility of each positive-half-twisted factor is unchanged. -/
theorem isAdmissible_blockHalfTwist_iff
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (i : Fin B.length) :
    letI := T.topology
    IsAdmissible (T.blockHalfTwist B σ i) ↔ IsAdmissible (σ i) := by
  let := T.topology
  exact isAdmissible_twist_iff _ _ (T.isOpen_ker_blockHalfModulus B i)

/-- Admissibility of each inverse-half-twisted factor is unchanged. -/
theorem isAdmissible_blockInverseHalfTwist_iff
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (i : Fin B.length) :
    letI := T.topology
    IsAdmissible (T.blockInverseHalfTwist B σ i) ↔ IsAdmissible (σ i) := by
  let := T.topology
  exact isAdmissible_twist_iff _ _ (T.isOpen_ker_blockInverseHalfModulus B i)

end Langlands.PadicField.TopologicalData
