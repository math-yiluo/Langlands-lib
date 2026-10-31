import Langlands.Representation.Derivative.MirabolicPlus
import Langlands.Representation.Derivative.MirabolicMinusNormalization

/-!
# Normalized mirabolic plus functors

The normalized Bernstein–Zelevinsky functors `Ψ⁺ : GL_n → P_(n+1)` and
`Φ⁺ : P_(n+1) → P_(n+2)`: twist the input by the canonical positive half of the
actual radical Haar character, here the determinant real power `+1/2`, and then
apply the published unnormalized plus functors.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uV uF uG uH

namespace Jacquet

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

/-- The canonical complex positive half commutes with restriction along a
homomorphism. -/
theorem complexPositiveHalfCharacter_comp (δ : G →* NNReal ˣ) (φ : H →* G) :
    (complexCharacter (positiveHalfCharacter δ)).comp φ =
      complexCharacter (positiveHalfCharacter (δ.comp φ)) := by
  rfl

end Jacquet

namespace Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## Positive-half characters -/

/-- The `Ψ⁺` normalization character `|det|^(1/2)` on `GL_n`. -/
abbrev psiPlusCharacter (T : F.TopologicalData) (n : ℕ) :
    GeneralLinear n F.Carrier →* ℂˣ :=
  realPowerCharacter (T.determinantNorm n) (1 / 2 : ℝ)

/-- The `Φ⁺` normalization character `|det|^(1/2)` on `P_(n+1)`. -/
abbrev phiPlusCharacter (T : F.TopologicalData) (n : ℕ) :
    mirabolic n F.Carrier →* ℂˣ :=
  realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype)
    (1 / 2 : ℝ)

theorem isOpen_ker_psiPlusCharacter (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen ((psiPlusCharacter T n).ker : Set (GeneralLinear n F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact isOpen_ker_realPowerCharacter _ (T.isOpen_ker_determinantNorm n) _

theorem isOpen_ker_phiPlusCharacter (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen ((phiPlusCharacter T n).ker : Set (mirabolic n F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1)
  apply isOpen_ker_realPowerCharacter
  exact (T.isOpen_ker_determinantNorm (n + 1)).preimage continuous_subtype_val

/-- `|det|^(1/2)` is the inverse of the published `Ψ⁻` character `|det|^(-1/2)`. -/
theorem psiPlusCharacter_eq_inv (T : F.TopologicalData) (n : ℕ) :
    psiPlusCharacter T n = (psiMinusCharacter T n)⁻¹ := by
  rw [psiMinusCharacter, realPowerCharacter_neg]
  exact (inv_inv (realPowerCharacter (T.determinantNorm n) (1 / 2 : ℝ))).symm

/-- `|det|^(1/2)` is the inverse of the published `Φ⁻` character `|det|^(-1/2)`. -/
theorem phiPlusCharacter_eq_inv (T : F.TopologicalData) (n : ℕ) :
    phiPlusCharacter T n = (phiMinusCharacter T n)⁻¹ := by
  rw [phiMinusCharacter, realPowerCharacter_neg]
  exact (inv_inv (realPowerCharacter
    ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype) (1 / 2 : ℝ))).symm

theorem psiPlusCharacter_mul_psiMinusCharacter (T : F.TopologicalData) (n : ℕ) :
    psiPlusCharacter T n * psiMinusCharacter T n = 1 := by
  rw [psiPlusCharacter_eq_inv]
  exact inv_mul_cancel (psiMinusCharacter T n)

theorem phiPlusCharacter_mul_phiMinusCharacter (T : F.TopologicalData) (n : ℕ) :
    phiPlusCharacter T n * phiMinusCharacter T n = 1 := by
  rw [phiPlusCharacter_eq_inv]
  exact inv_mul_cancel (phiMinusCharacter T n)

/-! ## The actual radical Haar positive halves -/

/-- The canonical positive complex half of actual radical Haar modulus, restricted
through the standard Levi equivalence to `GL_n`. -/
def psiPlusHaarHalf (T : F.TopologicalData) (n : ℕ) :
    GeneralLinear n F.Carrier →* ℂˣ := by
  letI := T.topology
  letI := T.fieldT2
  letI := T.generalLinearTopologicalGroup (n + 1)
  letI := T.generalLinearLocallyCompactSpace (n + 1)
  letI := locallyCompactSpace (n := n) (F := F.Carrier)
  exact (HaarModulus.closedHalfCharacter (radical n F.Carrier)
    radical_isClosed (leviSubgroup n F.Carrier) leviSubgroup_le_normalizer).comp
    (leviEquiv (n := n) (F := F.Carrier)).toMonoidHom

/-- The canonical positive complex half of actual radical Haar modulus, restricted
through the successor equivalence to `P_(n+1)`. -/
def phiPlusHaarHalf (T : F.TopologicalData) (n : ℕ) :
    mirabolic n F.Carrier →* ℂˣ := by
  letI := T.topology
  letI := T.fieldT2
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  letI := T.generalLinearLocallyCompactSpace (n + 1 + 1)
  letI := locallyCompactSpace (n := n + 1) (F := F.Carrier)
  exact (HaarModulus.closedHalfCharacter (radical (n + 1) F.Carrier)
    radical_isClosed (successorSubgroup n F.Carrier)
    successorSubgroup_le_normalizer).comp
    (successorEquiv (n := n) (F := F.Carrier)).toMonoidHom

/-- The actual Haar positive half agrees with the `Ψ⁺` character. -/
theorem psiPlusHaarHalf_eq (T : F.TopologicalData) (n : ℕ) :
    psiPlusHaarHalf T n = psiPlusCharacter T n := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := locallyCompactSpace (n := n) (F := F.Carrier)
  change (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter
    (HaarModulus.closedRestrictCharacter (radical n F.Carrier)
      radical_isClosed (leviSubgroup n F.Carrier) leviSubgroup_le_normalizer))).comp
      (leviEquiv (n := n) (F := F.Carrier)).toMonoidHom = _
  rw [Jacquet.complexPositiveHalfCharacter_comp, leviRadical_haarCharacter F T n,
    Jacquet.positiveHalfCharacter_eq_realPowerCharacter]

/-- The actual Haar positive half agrees with the `Φ⁺` character. -/
theorem phiPlusHaarHalf_eq (T : F.TopologicalData) (n : ℕ) :
    phiPlusHaarHalf T n = phiPlusCharacter T n := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1 + 1)
  let := locallyCompactSpace (n := n + 1) (F := F.Carrier)
  change (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter
    (HaarModulus.closedRestrictCharacter (radical (n + 1) F.Carrier)
      radical_isClosed (successorSubgroup n F.Carrier)
      successorSubgroup_le_normalizer))).comp
      (successorEquiv (n := n) (F := F.Carrier)).toMonoidHom = _
  rw [Jacquet.complexPositiveHalfCharacter_comp, successorRadical_haarCharacter F T n,
    Jacquet.positiveHalfCharacter_eq_realPowerCharacter]

/-- The Haar positive half is the inverse of the published Haar inverse half for `Ψ`. -/
theorem psiPlusHaarHalf_eq_inv (T : F.TopologicalData) (n : ℕ) :
    psiPlusHaarHalf T n = (psiMinusHaarInverseHalf T n)⁻¹ := by
  rw [psiPlusHaarHalf_eq, psiMinusHaarInverseHalf_eq, psiPlusCharacter_eq_inv]

/-- The Haar positive half is the inverse of the published Haar inverse half for `Φ`. -/
theorem phiPlusHaarHalf_eq_inv (T : F.TopologicalData) (n : ℕ) :
    phiPlusHaarHalf T n = (phiMinusHaarInverseHalf T n)⁻¹ := by
  rw [phiPlusHaarHalf_eq, phiMinusHaarInverseHalf_eq, phiPlusCharacter_eq_inv]

theorem isOpen_ker_psiPlusHaarHalf (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen ((psiPlusHaarHalf T n).ker : Set (GeneralLinear n F.Carrier)) := by
  rw [psiPlusHaarHalf_eq]
  exact isOpen_ker_psiPlusCharacter T n

theorem isOpen_ker_phiPlusHaarHalf (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen ((phiPlusHaarHalf T n).ker : Set (mirabolic n F.Carrier)) := by
  rw [phiPlusHaarHalf_eq]
  exact isOpen_ker_phiPlusCharacter T n

/-! ## Normalized Psi-plus -/

/-- Normalized `Ψ⁺`: twist by `|det|^(1/2)` on `GL_n`, then inflate along the actual
projection `P_(n+1) → GL_n`. -/
def psiPlus (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) := by
  letI := T.topology
  exact SmoothRep.twistFunctor (psiPlusCharacter T n) (isOpen_ker_psiPlusCharacter T n) ⋙
    psiPlusUnnormalized T n

theorem psiPlus_eq (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    psiPlus.{uV} T n =
      SmoothRep.twistFunctor (psiPlusCharacter T n) (isOpen_ker_psiPlusCharacter T n) ⋙
        psiPlusUnnormalized T n :=
  rfl

/-- Equality of normalized `Ψ⁺` with normalization by the actual radical Haar
positive half, including maps. -/
theorem psiPlus_haarNormalization (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    psiPlus.{uV} T n =
      SmoothRep.twistFunctor (psiPlusHaarHalf T n) (isOpen_ker_psiPlusHaarHalf T n) ⋙
        psiPlusUnnormalized T n := by
  simp only [psiPlusHaarHalf_eq]
  rfl

/-- Equivalently, inflate first and then twist by `|det(projection g)|^(1/2)`. -/
theorem psiPlus_eq_unnormalized_twist (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    psiPlus.{uV} T n = psiPlusUnnormalized T n ⋙
      SmoothRep.twistFunctor ((psiPlusCharacter T n).comp projection)
        ((isOpen_ker_psiPlusCharacter T n).preimage continuous_projection) :=
  rfl

/-- The object carrier is the input carrier. -/
theorem psiPlus_obj_carrier (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      ((psiPlus T n).obj A : Type uV) = A := by
  intros
  rfl

/-- The object action is the twisted input action composed with `projection`. -/
theorem psiPlus_obj_representation (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      ((psiPlus T n).obj A).representation =
        (Langlands.twist (psiPlusCharacter T n) A.representation).comp projection := by
  intros
  rfl

/-- `Ψ⁺(ρ)(g) v = |det(projection g)|^(1/2) ρ(projection g) v`. -/
theorem psiPlus_action (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (g : mirabolic n F.Carrier)
      (v : A), ((psiPlus T n).obj A).representation g v =
        (psiPlusCharacter T n (projection g) : ℂ) • A.representation (projection g) v := by
  intros
  rfl

/-- The radical `V_(n+1)` acts trivially. -/
theorem psiPlus_radical (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (u : radical n F.Carrier)
      (v : A), ((psiPlus T n).obj A).representation (u : mirabolic n F.Carrier) v = v := by
  let := T.topology
  intro A u v
  change (psiPlusCharacter T n (projection (u : mirabolic n F.Carrier)) : ℂ) •
    A.representation (projection (u : mirabolic n F.Carrier)) v = v
  rw [(projection_eq_one_iff _).mpr u.property, map_one, map_one, Units.val_one, one_smul,
    Module.End.one_apply]

/-- The Levi formula `Ψ⁺(ρ)(levi a) = |det a|^(1/2) ρ(a)`. -/
theorem psiPlus_levi (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (a : GeneralLinear n F.Carrier),
      ((psiPlus T n).obj A).representation (levi a) =
        (psiPlusCharacter T n a : ℂ) • A.representation a := by
  let := T.topology
  intro A a
  change (psiPlusCharacter T n (projection (levi a)) : ℂ) •
    A.representation (projection (levi a)) = _
  rw [projection_levi]

/-- In radical-first coordinates, `Ψ⁺(ρ)(u(v) levi a) = |det a|^(1/2) ρ(a)`. -/
theorem psiPlus_radicalElement_mul_levi (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (v : Fin n → F.Carrier)
      (a : GeneralLinear n F.Carrier),
      ((psiPlus T n).obj A).representation ((radicalElement v).val * levi a) =
        (psiPlusCharacter T n a : ℂ) • A.representation a := by
  let := T.topology
  intro A v a
  change (psiPlusCharacter T n (projection ((radicalElement v).val * levi a)) : ℂ) •
    A.representation (projection ((radicalElement v).val * levi a)) = _
  rw [projection_radicalElement_mul_levi]

theorem psiPlus_isSmooth (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      IsSmooth ((psiPlus T n).obj A).representation := by
  let := T.topology
  intro A
  exact ((psiPlus T n).obj A).isSmooth

/-- The induced map has the same underlying linear map. -/
theorem psiPlus_map_apply (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} (f : A ⟶ B) (v : A),
      SmoothRep.hom ((psiPlus T n).map f) v = SmoothRep.hom f v := by
  intros
  rfl

theorem psiPlus_map_equivariant (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} (f : A ⟶ B)
      (g : mirabolic n F.Carrier) (w : (psiPlus T n).obj A),
      SmoothRep.hom ((psiPlus T n).map f) (((psiPlus T n).obj A).representation g w) =
        ((psiPlus T n).obj B).representation g (SmoothRep.hom ((psiPlus T n).map f) w) := by
  let := T.topology
  intro A B f g w
  exact Representation.IntertwiningMap.isIntertwining _ _
    (SmoothRep.hom ((psiPlus T n).map f)) g w

theorem psiPlus_map_id (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      (psiPlus T n).map (𝟙 A) = 𝟙 ((psiPlus T n).obj A) := by
  let := T.topology
  intro A
  exact (psiPlus T n).map_id A

theorem psiPlus_map_comp (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} (f : A ⟶ B) (g : B ⟶ C),
      (psiPlus T n).map (f ≫ g) = (psiPlus T n).map f ≫ (psiPlus T n).map g := by
  let := T.topology
  intro A B C f g
  exact (psiPlus T n).map_comp f g

/-! ## Normalized Phi-plus -/

/-- Normalized `Φ⁺`: twist by `|det|^(1/2)` on `P_(n+1)`, then apply the actual
unnormalized compact induction from the plus subgroup `Q = P_(n+1) V_(n+2)`. -/
def phiPlus (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + 1) F.Carrier) := by
  letI := T.topology
  exact SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n) ⋙
    phiPlusUnnormalized T ψ n

theorem phiPlus_eq (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    phiPlus.{uV} T ψ n =
      SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n) ⋙
        phiPlusUnnormalized T ψ n :=
  rfl

/-- Equality of normalized `Φ⁺` with normalization by the actual radical Haar
positive half, including maps. -/
theorem phiPlus_haarNormalization (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    phiPlus.{uV} T ψ n =
      SmoothRep.twistFunctor (phiPlusHaarHalf T n) (isOpen_ker_phiPlusHaarHalf T n) ⋙
        phiPlusUnnormalized T ψ n := by
  simp only [phiPlusHaarHalf_eq]
  rfl

/-- The object carrier is the actual space of compactly supported covariant functions
for the positively normalized inducing representation. -/
theorem phiPlus_obj_carrier (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      ((phiPlus T ψ n).obj τ : Type (max uF uV)) =
        Induction.CompactFunctions (plusSubgroup n F.Carrier)
          (plusTwistRepresentation ψ n
            (Langlands.twist (phiPlusCharacter T n) τ.representation)) := by
  intros
  rfl

/-- The object is the bundled actual compact induction of the normalized `τ'`. -/
theorem phiPlus_obj (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      (phiPlus T ψ n).obj τ =
        SmoothRep.of
          (Induction.compactInduced (plusSubgroup n F.Carrier)
            (plusTwistRepresentation ψ n
              (Langlands.twist (phiPlusCharacter T n) τ.representation)))
          (Induction.compactInduced_smooth (plusSubgroup n F.Carrier)
            (plusTwistRepresentation ψ n
              (Langlands.twist (phiPlusCharacter T n) τ.representation))) := by
  intros
  rfl

/-- The object action is the actual compact induction of the normalized `τ'`. -/
theorem phiPlus_obj_representation (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : mirabolic (n + 1) F.Carrier)
      (φ : (phiPlus T ψ n).obj τ),
      @Eq (Induction.CompactFunctions (plusSubgroup n F.Carrier)
          (plusTwistRepresentation ψ n
            (Langlands.twist (phiPlusCharacter T n) τ.representation)))
        (((phiPlus T ψ n).obj τ).representation g φ)
        (Induction.compactInduced (plusSubgroup n F.Carrier)
          (plusTwistRepresentation ψ n
            (Langlands.twist (phiPlusCharacter T n) τ.representation)) g φ) := by
  intros
  rfl

/-- Evaluation of a vector of normalized `Φ⁺(τ)` at a point of `P_(n+2)`. -/
abbrev phiPlusNormalizedEval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      (phiPlus T ψ n).obj τ → mirabolic (n + 1) F.Carrier → τ := by
  letI := T.topology
  exact fun τ => phiPlusEval T ψ n
    ((SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n)).obj τ)

/-- Normalized evaluation is unnormalized evaluation for the twisted input. -/
theorem phiPlusNormalizedEval_eq (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (φ : (phiPlus T ψ n).obj τ)
      (x : mirabolic (n + 1) F.Carrier),
      phiPlusNormalizedEval T ψ n τ φ x =
        phiPlusEval T ψ n
          ((SmoothRep.twistFunctor (phiPlusCharacter T n)
            (isOpen_ker_phiPlusCharacter T n)).obj τ) φ x := by
  intros
  rfl

/-- Vectors of normalized `Φ⁺(τ)` are determined by their values. -/
theorem phiPlusNormalizedEval_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      Function.Injective (phiPlusNormalizedEval T ψ n τ) := by
  let := T.topology
  intro τ
  exact phiPlusEval_injective T ψ n _

/-- Covariance
`φ(q x) = thetaPlus(q) • |det(plusProjection q)|^(1/2) • τ(plusProjection q) φ(x)`
for `q ∈ Q`. -/
theorem phiPlusNormalizedEval_covariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiPlus T ψ n).obj τ) (q : plusSubgroup n F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiPlusNormalizedEval T ψ n τ φ ((q : mirabolic (n + 1) F.Carrier) * x) =
        (thetaPlus ψ n q : ℂ) • (phiPlusCharacter T n (plusProjection q) : ℂ) •
          τ.representation (plusProjection q) (phiPlusNormalizedEval T ψ n τ φ x) := by
  let := T.topology
  intro τ φ q x
  exact phiPlusEval_covariant T ψ n _ φ q x

/-- Levi-first coordinates: `φ(p m x) = Θ(m) |det p|^(1/2) τ(p) φ(x)`. -/
theorem phiPlusNormalizedEval_successor_mul_radical (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiPlus T ψ n).obj τ) (g : mirabolic n F.Carrier)
      (u : radical (n + 1) F.Carrier) (x : mirabolic (n + 1) F.Carrier),
      phiPlusNormalizedEval T ψ n τ φ (successor g * u.val * x) =
        (theta ψ n u : ℂ) • (phiPlusCharacter T n g : ℂ) •
          τ.representation g (phiPlusNormalizedEval T ψ n τ φ x) := by
  let := T.topology
  intro τ φ g u x
  exact phiPlusEval_successor_mul_radical T ψ n _ φ g u x

/-- Radical elements act on values through `Θ`. -/
theorem phiPlusNormalizedEval_radical_mul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiPlus T ψ n).obj τ) (u : radical (n + 1) F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiPlusNormalizedEval T ψ n τ φ (u.val * x) =
        (theta ψ n u : ℂ) • phiPlusNormalizedEval T ψ n τ φ x := by
  let := T.topology
  intro τ φ u x
  exact phiPlusEval_radical_mul T ψ n _ φ u x

/-- Successor elements act on values through `|det|^(1/2) τ`. -/
theorem phiPlusNormalizedEval_successor_mul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiPlus T ψ n).obj τ) (g : mirabolic n F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiPlusNormalizedEval T ψ n τ φ (successor g * x) =
        (phiPlusCharacter T n g : ℂ) • τ.representation g (phiPlusNormalizedEval T ψ n τ φ x) := by
  let := T.topology
  intro τ φ g x
  exact phiPlusEval_successor_mul T ψ n _ φ g x

/-- The projected nonzero support in `Q \ P_(n+2)` is compact. -/
theorem phiPlusNormalizedEval_isCompact_quotientSupport (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiPlus T ψ n).obj τ),
      IsCompact (Induction.quotientSupport (plusSubgroup n F.Carrier)
        (phiPlusNormalizedEval T ψ n τ φ)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  intro τ φ
  exact phiPlusEval_isCompact_quotientSupport T ψ n _ φ

/-- Each vector has one open subgroup of right stabilizers. -/
theorem phiPlusNormalizedEval_exists_openSubgroup (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiPlus T ψ n).obj τ),
      ∃ K : OpenSubgroup (mirabolic (n + 1) F.Carrier), ∀ (k : K) (x : mirabolic (n + 1) F.Carrier),
        phiPlusNormalizedEval T ψ n τ φ (x * (k : mirabolic (n + 1) F.Carrier)) =
          phiPlusNormalizedEval T ψ n τ φ x := by
  let := T.topology
  intro τ φ
  exact phiPlusEval_exists_openSubgroup T ψ n _ φ

/-- A vector of normalized `Φ⁺(τ)` from a normalized covariant function with one open
subgroup of right stabilizers and compact projected support. -/
def phiPlusNormalizedMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      (f : mirabolic (n + 1) F.Carrier → τ) →
      (∀ (q : plusSubgroup n F.Carrier) (x : mirabolic (n + 1) F.Carrier),
        f ((q : mirabolic (n + 1) F.Carrier) * x) =
          (thetaPlus ψ n q : ℂ) • (phiPlusCharacter T n (plusProjection q) : ℂ) •
            τ.representation (plusProjection q) (f x)) →
      (K : OpenSubgroup (mirabolic (n + 1) F.Carrier)) →
      (∀ (k : K) (x : mirabolic (n + 1) F.Carrier), f (x * (k : mirabolic (n + 1) F.Carrier)) =
        f x) →
      IsCompact (Induction.quotientSupport (plusSubgroup n F.Carrier) f) →
      (phiPlus T ψ n).obj τ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact fun τ f hcov K hK hc => phiPlusMk T ψ n
    ((SmoothRep.twistFunctor (phiPlusCharacter T n) (isOpen_ker_phiPlusCharacter T n)).obj τ)
    f hcov K hK hc

theorem phiPlusNormalizedEval_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (f : mirabolic (n + 1) F.Carrier → τ)
      (hcov : ∀ (q : plusSubgroup n F.Carrier) (x : mirabolic (n + 1) F.Carrier),
        f ((q : mirabolic (n + 1) F.Carrier) * x) =
          (thetaPlus ψ n q : ℂ) • (phiPlusCharacter T n (plusProjection q) : ℂ) •
            τ.representation (plusProjection q) (f x))
      (K : OpenSubgroup (mirabolic (n + 1) F.Carrier))
      (hK : ∀ (k : K) (x : mirabolic (n + 1) F.Carrier),
        f (x * (k : mirabolic (n + 1) F.Carrier)) = f x)
      (hc : IsCompact (Induction.quotientSupport (plusSubgroup n F.Carrier) f)),
      phiPlusNormalizedEval T ψ n τ (phiPlusNormalizedMk T ψ n τ f hcov K hK hc) = f := by
  intros
  rfl

/-- The action is right translation: `(g • φ)(x) = φ(x g)`. -/
theorem phiPlus_action (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : mirabolic (n + 1) F.Carrier)
      (φ : (phiPlus T ψ n).obj τ) (x : mirabolic (n + 1) F.Carrier),
      phiPlusNormalizedEval T ψ n τ (((phiPlus T ψ n).obj τ).representation g φ) x =
        phiPlusNormalizedEval T ψ n τ φ (x * g) := by
  intros
  rfl

theorem phiPlus_isSmooth (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      IsSmooth ((phiPlus T ψ n).obj τ).representation := by
  let := T.topology
  intro τ
  exact ((phiPlus T ψ n).obj τ).isSmooth

/-- The induced map is the actual compact-induction map of the same underlying
intertwiner, viewed between the normalized inducing representations. -/
theorem phiPlus_map_hom (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ {τ σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ),
      SmoothRep.hom ((phiPlus T ψ n).map f) =
        Induction.compactInducedMap (plusSubgroup n F.Carrier)
          (SmoothRep.hom ((plusTwistFunctor T ψ n).map
            ((SmoothRep.twistFunctor (phiPlusCharacter T n)
              (isOpen_ker_phiPlusCharacter T n)).map f))) := by
  intros
  rfl

/-- On values, the induced map is postcomposition: `(Φ⁺ f) φ (x) = f (φ x)`. -/
theorem phiPlus_map_eval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ)
      (φ : (phiPlus T ψ n).obj τ) (x : mirabolic (n + 1) F.Carrier),
      phiPlusNormalizedEval T ψ n σ (SmoothRep.hom ((phiPlus T ψ n).map f) φ) x =
        SmoothRep.hom f (phiPlusNormalizedEval T ψ n τ φ x) := by
  intros
  rfl

theorem phiPlus_map_equivariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ)
      (g : mirabolic (n + 1) F.Carrier) (w : (phiPlus T ψ n).obj τ),
      SmoothRep.hom ((phiPlus T ψ n).map f) (((phiPlus T ψ n).obj τ).representation g w) =
        ((phiPlus T ψ n).obj σ).representation g
          (SmoothRep.hom ((phiPlus T ψ n).map f) w) := by
  let := T.topology
  intro τ σ f g w
  exact Representation.IntertwiningMap.isIntertwining _ _
    (SmoothRep.hom ((phiPlus T ψ n).map f)) g w

theorem phiPlus_map_id (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      (phiPlus T ψ n).map (𝟙 τ) = 𝟙 ((phiPlus T ψ n).obj τ) := by
  let := T.topology
  intro τ
  exact (phiPlus T ψ n).map_id τ

theorem phiPlus_map_comp (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ σ ρ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ) (g : σ ⟶ ρ),
      (phiPlus T ψ n).map (f ≫ g) = (phiPlus T ψ n).map f ≫ (phiPlus T ψ n).map g := by
  let := T.topology
  intro τ σ ρ f g
  exact (phiPlus T ψ n).map_comp f g

end Derivative.Mirabolic

end Langlands
