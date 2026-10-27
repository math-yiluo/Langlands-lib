import Langlands.Representation.Exponents.RealTwistFamilies
import Langlands.Representation.Twist.LeviComplexPower
import Langlands.Representation.CuspidalSupport.LeviAssociation

/-!
# Actual complex-twist induced families and opposite Jacquet occurrence loci

Internal packaging of the existing induction, complex product-Levi determinant
twist, Weyl transport, and class-exponent predicate, with real-indexed complex
affine parameter maps. No continuation property is part of these data.
-/

noncomputable section

namespace Langlands.ComplexTwistFamilies

open GeneralLinear Geometric
open scoped NNReal

universe uF uV uW

section Parameters

variable {ι κ : Type*}

/-- Coordinatewise inclusion of real vectors as complex vectors with zero
imaginary part. -/
def realInclusion (ι : Type*) : (ι → ℝ) →ₗ[ℝ] (ι → ℂ) where
  toFun v j := (v j : ℂ)
  map_add' v w := by
    ext j
    simp
  map_smul' c v := by
    ext j
    simp [Complex.real_smul]

@[simp]
theorem realInclusion_apply (v : ι → ℝ) (j : ι) :
    realInclusion ι v j = (v j : ℂ) := rfl

/-- Coordinatewise multiplication of real vectors by `Complex.I`. -/
def imaginaryInclusion (ι : Type*) : (ι → ℝ) →ₗ[ℝ] (ι → ℂ) where
  toFun v j := Complex.I * (v j : ℂ)
  map_add' v w := by
    ext j
    simp [mul_add]
  map_smul' c v := by
    ext j
    simp [Complex.real_smul]
    ring

@[simp]
theorem imaginaryInclusion_apply (v : ι → ℝ) (j : ι) :
    imaginaryInclusion ι v j = Complex.I * (v j : ℂ) := rfl

/-- A real affine map into complex parameters is its offset plus its real
linear part. -/
theorem affine_apply (a : (ι → ℝ) →ᵃ[ℝ] (κ → ℂ)) (u : ι → ℝ) :
    a u = a 0 + a.linear u := by
  simpa only [vadd_eq_add, add_zero, add_comm] using a.map_vadd 0 u

/-- The mixed real-indexed complex affine map `u ↦ r + i L(u)`. -/
def mixedAffine (r : κ → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    (ι → ℝ) →ᵃ[ℝ] (κ → ℂ) :=
  AffineMap.const ℝ (ι → ℝ) (realInclusion κ r) +
    ((imaginaryInclusion κ).comp L).toAffineMap

@[simp]
theorem mixedAffine_apply (r : κ → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (u : ι → ℝ) (j : κ) :
    mixedAffine r L u j = (r j : ℂ) + Complex.I * (L u j : ℂ) := rfl

theorem mixedAffine_zero (r : κ → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    mixedAffine r L 0 = fun j => (r j : ℂ) := by
  ext j
  simp

@[simp]
theorem mixedAffine_linear (r : κ → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    (mixedAffine r L).linear = (imaginaryInclusion κ).comp L := by
  simp [mixedAffine]

@[simp]
theorem re_mixedAffine_apply (r : κ → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (u : ι → ℝ) (j : κ) :
    (mixedAffine r L u j).re = r j := by
  simp

@[simp]
theorem im_mixedAffine_apply (r : κ → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (u : ι → ℝ) (j : κ) :
    (mixedAffine r L u j).im = L u j := by
  simp

/-- The coordinatewise-`ofReal` inclusion of a real affine map. -/
def ofRealAffine (a : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ)) : (ι → ℝ) →ᵃ[ℝ] (κ → ℂ) :=
  (realInclusion κ).toAffineMap.comp a

@[simp]
theorem ofRealAffine_apply (a : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ)) (u : ι → ℝ) (j : κ) :
    ofRealAffine a u j = (a u j : ℂ) := rfl

end Parameters

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B D C : BlockShape n)

/-! ### Induced families -/

/-- The complex determinant-twist family of actual upper normalized inductions. -/
def induced (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) :
    (Fin B.length → ℂ) → Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  fun z => CuspidalJacquetMultiplicity.induced T B
    (Rep.of (T.leviComplexPowerTwist B z σ.ρ))

theorem induced_apply (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (z : Fin B.length → ℂ) :
    induced T B σ z = CuspidalJacquetMultiplicity.induced T B
      (Rep.of (T.leviComplexPowerTwist B z σ.ρ)) := rfl

/-- The bundled action is the existing normalized induction action. -/
theorem induced_representation (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (z : Fin B.length → ℂ) :
    letI := T.topology
    (induced T B σ z).ρ =
      T.normalizedParabolicInduced B (T.leviComplexPowerTwist B z σ.ρ) := rfl

theorem isSmooth_induced (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (z : Fin B.length → ℂ) :
    letI := T.topology
    IsSmooth (induced T B σ z).ρ :=
  T.isSmooth_normalizedParabolicInduced B (T.leviComplexPowerTwist B z σ.ρ)

@[simp]
theorem induced_zero (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) :
    induced T B σ 0 = CuspidalJacquetMultiplicity.induced T B σ := by
  simp [induced]

/-- Real complex exponents give exactly the published real-twist family. -/
@[simp]
theorem induced_ofReal (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (t : Fin B.length → ℝ) :
    induced T B σ (fun i => (t i : ℂ)) = RealTwistFamilies.induced T B σ t := by
  simp only [induced, RealTwistFamilies.induced,
    PadicField.TopologicalData.leviComplexPowerTwist_ofReal]

/-- Evaluate the existing smooth induced function; no new carrier is introduced. -/
def inducedEval (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (z : Fin B.length → ℂ) (f : induced T B σ z)
    (g : GeneralLinear n F.Carrier) : σ :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.eval (B.parabolic F.Carrier)
    (twist (T.parabolicHalfModulus B)
      ((T.leviComplexPowerTwist B z σ.ρ).comp (B.leviProjection F.Carrier))) f g

@[simp]
theorem inducedEval_add (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (z : Fin B.length → ℂ) (f f' : induced T B σ z)
    (g : GeneralLinear n F.Carrier) :
    inducedEval T B σ z (f + f') g = inducedEval T B σ z f g + inducedEval T B σ z f' g :=
  rfl

@[simp]
theorem inducedEval_smul (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (z : Fin B.length → ℂ) (c : ℂ) (f : induced T B σ z)
    (g : GeneralLinear n F.Carrier) :
    inducedEval T B σ z (c • f) g = c • inducedEval T B σ z f g :=
  rfl

/-- The induced family acts by the same right translations at every parameter. -/
@[simp]
theorem inducedEval_action (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (z : Fin B.length → ℂ) (f : induced T B σ z)
    (g x : GeneralLinear n F.Carrier) :
    inducedEval T B σ z ((induced T B σ z).ρ g f) x =
      inducedEval T B σ z f (x * g) := rfl

/-- Covariance retains the upper positive half modulus and the actual complex
determinant character. -/
theorem inducedEval_covariant (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (z : Fin B.length → ℂ) (f : induced T B σ z)
    (g : B.parabolic F.Carrier) (x : GeneralLinear n F.Carrier) :
    inducedEval T B σ z f ((g : GeneralLinear n F.Carrier) * x) =
      ((NNReal.sqrt (T.leviModulus B (B.leviProjection F.Carrier g) : ℝ≥0) : ℝ) : ℂ) •
        ((T.leviComplexPowerCharacter B z (B.leviProjection F.Carrier g) : ℂ) •
          σ.ρ (B.leviProjection F.Carrier g) (inducedEval T B σ z f x)) :=
  T.normalizedParabolicInduced_covariant B (T.leviComplexPowerTwist B z σ.ρ) f g x

/-! ### Unitary and mixed slices -/

/-- The unitary slice `z i = I * u i`, for arbitrary real `u`. -/
def unitaryInduced (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) (u : Fin B.length → ℝ) :
    Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  induced T B σ (fun i => Complex.I * (u i : ℂ))

/-- The mixed slice `z i = r i + I * u i`, for arbitrary real `r` and `u`. -/
def mixedInduced (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) (r u : Fin B.length → ℝ) :
    Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  induced T B σ (fun i => (r i : ℂ) + Complex.I * (u i : ℂ))

theorem unitaryInduced_apply (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (u : Fin B.length → ℝ) :
    unitaryInduced T B σ u = induced T B σ (fun i => Complex.I * (u i : ℂ)) := rfl

theorem mixedInduced_apply (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (r u : Fin B.length → ℝ) :
    mixedInduced T B σ r u =
      induced T B σ (fun i => (r i : ℂ) + Complex.I * (u i : ℂ)) := rfl

/-- The unitary-slice character has norm one at every actual Levi element. -/
theorem norm_unitaryCharacter (u : Fin B.length → ℝ) (m : B.Levi F.Carrier) :
    ‖(T.leviComplexPowerCharacter B (fun i => Complex.I * (u i : ℂ)) m : ℂ)‖ = 1 :=
  T.norm_leviComplexPowerCharacter_imaginary B u m

@[simp]
theorem unitaryInduced_zero (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) :
    unitaryInduced T B σ 0 = CuspidalJacquetMultiplicity.induced T B σ := by
  have h : (fun i : Fin B.length => Complex.I * (((0 : Fin B.length → ℝ) i : ℝ) : ℂ)) = 0 := by
    ext i
    simp
  rw [unitaryInduced_apply, h, induced_zero]

@[simp]
theorem mixedInduced_zero_left (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (u : Fin B.length → ℝ) :
    mixedInduced T B σ 0 u = unitaryInduced T B σ u := by
  simp [mixedInduced_apply, unitaryInduced_apply]

@[simp]
theorem mixedInduced_zero_right (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (r : Fin B.length → ℝ) :
    mixedInduced T B σ r 0 = RealTwistFamilies.induced T B σ r := by
  simp [mixedInduced_apply]

/-- The mixed twist is the published real twist of the unitary twist. -/
theorem leviComplexPowerTwist_mixed (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (r u : Fin B.length → ℝ) :
    T.leviComplexPowerTwist B (fun i => (r i : ℂ) + Complex.I * (u i : ℂ)) σ.ρ =
      T.leviRealPowerTwist B r
        (T.leviComplexPowerTwist B (fun i => Complex.I * (u i : ℂ)) σ.ρ) := by
  rw [← PadicField.TopologicalData.leviComplexPowerTwist_ofReal,
    ← PadicField.TopologicalData.leviComplexPowerTwist_add]
  rfl

/-- The mixed slice is the real-twist family of the unitary twist, on the same carrier. -/
theorem mixedInduced_eq_realInduced (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (r u : Fin B.length → ℝ) :
    mixedInduced T B σ r u = RealTwistFamilies.induced T B
      (Rep.of (T.leviComplexPowerTwist B (fun i => Complex.I * (u i : ℂ)) σ.ρ)) r := by
  rw [mixedInduced_apply, induced_apply, leviComplexPowerTwist_mixed]
  rfl

/-! ### Real-indexed complex affine parameter maps -/

/-- The canonical unitary ambient map `u ↦ I u`, the mixed map with zero offset
and identity linear part. -/
def unitaryAmbient : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin B.length → ℂ) :=
  mixedAffine (0 : Fin B.length → ℝ) LinearMap.id

theorem unitaryAmbient_eq :
    unitaryAmbient B = mixedAffine (0 : Fin B.length → ℝ) LinearMap.id := rfl

@[simp]
theorem unitaryAmbient_apply (u : Fin B.length → ℝ) :
    unitaryAmbient B u = fun i => Complex.I * (u i : ℂ) := by
  ext i
  simp [unitaryAmbient]

/-- Mixed candidate parameters along an actual refinement: the linear part is
the published coarse restriction. -/
def refinedMixedAffine (S : BlockRefinement B) (r : Fin (B.flatten S).length → ℝ) :
    (Fin B.length → ℝ) →ᵃ[ℝ] (Fin (B.flatten S).length → ℂ) :=
  mixedAffine r (RealTwistFamilies.restrictParameter B S)

@[simp]
theorem refinedMixedAffine_apply (S : BlockRefinement B)
    (r : Fin (B.flatten S).length → ℝ) (u : Fin B.length → ℝ)
    (k : Fin (B.flatten S).length) :
    refinedMixedAffine B S r u k =
      (r k : ℂ) + Complex.I * (u ((B.flattenBlockEquiv S).symm k).1 : ℂ) := rfl

/-! ### Transported candidates -/

/-- Complex-twist a fixed actual source-Levi representation at `a u`, then use
the existing inverse-conjugation transport along the supplied permutation. -/
def transported (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℂ)) :
    (Fin B.length → ℝ) → Rep.{uW} ℂ (C.Levi F.Carrier) :=
  fun u => Rep.of (CuspidalSupport.transport D C w hw
    (T.leviComplexPowerTwist D (a u) ω.ρ))

theorem transported_apply (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℂ))
    (u : Fin B.length → ℝ) :
    transported T B D C w hw ω a u =
      Rep.of (CuspidalSupport.transport D C w hw
        (T.leviComplexPowerTwist D (a u) ω.ρ)) := rfl

/-- Both the character and the representation are evaluated at the actual
inverse Levi conjugation. -/
@[simp]
theorem transported_action (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℂ))
    (u : Fin B.length → ℝ) (m : C.Levi F.Carrier) (v : ω) :
    (transported T B D C w hw ω a u).ρ m v =
      (T.leviComplexPowerCharacter D (a u)
        ((CuspidalSupport.leviConjugation D C w hw).symm m) : ℂ) •
      ω.ρ ((CuspidalSupport.leviConjugation D C w hw).symm m) v := rfl

@[simp]
theorem transported_zero (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier)) (u : Fin B.length → ℝ) :
    transported T B D C w hw ω 0 u =
      Rep.of (CuspidalSupport.transport D C w hw ω.ρ) := by
  simp [transported]

/-- For the identity permutation the candidate is the untransported twist. -/
theorem transported_one
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D D 1)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℂ))
    (u : Fin B.length → ℝ) :
    transported T B D D 1 hw ω a u =
      Rep.of (T.leviComplexPowerTwist D (a u) ω.ρ) :=
  congrArg Rep.of (CuspidalSupport.transport_one (F := F.Carrier) _)

/-- The coordinatewise-`ofReal` inclusion of a real affine map recovers the
published real transported family. -/
@[simp]
theorem transported_ofRealAffine (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℝ))
    (t : Fin B.length → ℝ) :
    transported T B D C w hw ω (ofRealAffine a) t =
      RealTwistFamilies.transported T B D C w hw ω a t := by
  rw [transported_apply, RealTwistFamilies.transported_apply]
  change Rep.of (CuspidalSupport.transport D C w hw
    (T.leviComplexPowerTwist D (fun j => (a t j : ℂ)) ω.ρ)) = _
  rw [PadicField.TopologicalData.leviComplexPowerTwist_ofReal]

/-! ### Occurrence -/

/-- Pointwise occurrence, at the same real argument, of the transported
candidate at `a u` in the actual opposite Jacquet module of the entire
induced representation at `b u`. -/
def Occurs (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (b : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin B.length → ℂ))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℂ))
    (u : Fin B.length → ℝ) : Prop :=
  T.IsOppositeJacquetClassExponent C (induced T B σ (b u))
    (transported T B D C w hw ω a u)

/-- Exactly the real parameters at which the specified actual candidate occurs. -/
def occurrenceLocus (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (b : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin B.length → ℂ))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℂ)) :
    Set (Fin B.length → ℝ) :=
  {u | Occurs T B D C σ w hw ω b a u}

@[simp]
theorem mem_occurrenceLocus (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (b : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin B.length → ℂ))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℂ))
    (u : Fin B.length → ℝ) :
    u ∈ occurrenceLocus T B D C σ w hw ω b a ↔
      Occurs T B D C σ w hw ω b a u := Iff.rfl

/-- Unfolding exposes only irreducibility, admissibility and an actual
subrepresentation followed by a surjective intertwiner. -/
theorem occurs_iff (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (b : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin B.length → ℂ))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℂ))
    (u : Fin B.length → ℝ) :
    letI := T.topology
    Occurs T B D C σ w hw ω b a u ↔
      Representation.IsIrreducible (transported T B D C w hw ω a u).ρ ∧
      IsAdmissible (transported T B D C w hw ω a u).ρ ∧
      ∃ U : Subrepresentation
          (CuspidalJacquetMultiplicity.oppositeJacquet T C (induced T B σ (b u))).ρ,
        ∃ q : U.toRepresentation.IntertwiningMap (transported T B D C w hw ω a u).ρ,
          Function.Surjective q := Iff.rfl

/-- Real parameters: the `ofReal` inclusions of the ambient identity and a real
candidate map give exactly the published real occurrence predicate. -/
theorem occurs_ofRealAffine_iff (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℝ))
    (t : Fin B.length → ℝ) :
    Occurs T B D C σ w hw ω (ofRealAffine (AffineMap.id ℝ (Fin B.length → ℝ)))
        (ofRealAffine a) t ↔
      RealTwistFamilies.Occurs T B D C σ w hw ω a t := by
  rw [Occurs, RealTwistFamilies.Occurs, transported_ofRealAffine]
  change T.IsOppositeJacquetClassExponent C (induced T B σ (fun i => (t i : ℂ))) _ ↔ _
  rw [induced_ofReal]

theorem occurrenceLocus_ofRealAffine (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℝ)) :
    occurrenceLocus T B D C σ w hw ω (ofRealAffine (AffineMap.id ℝ (Fin B.length → ℝ)))
        (ofRealAffine a) =
      RealTwistFamilies.occurrenceLocus T B D C σ w hw ω a := by
  ext t
  exact occurs_ofRealAffine_iff T B D C σ w hw ω a t

/-- The canonical unitary ambient map together with a mixed candidate map:
the ambient is the unitary slice and the candidate exponent is `r + i L(u)`. -/
theorem occurs_unitaryAmbient_mixedAffine_iff (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (r : Fin D.length → ℝ) (L : (Fin B.length → ℝ) →ₗ[ℝ] (Fin D.length → ℝ))
    (u : Fin B.length → ℝ) :
    Occurs T B D C σ w hw ω (unitaryAmbient B) (mixedAffine r L) u ↔
      T.IsOppositeJacquetClassExponent C (unitaryInduced T B σ u)
        (Rep.of (CuspidalSupport.transport D C w hw
          (T.leviComplexPowerTwist D
            (fun j => (r j : ℂ) + Complex.I * (L u j : ℂ)) ω.ρ))) := by
  rw [Occurs, unitaryAmbient_apply]
  rfl

/-- Along an actual refinement with identity transport, the unitary ambient
and refined mixed candidate unfold to the fine-Levi twist by
`r k + i u(parent k)`. -/
theorem occurs_unitaryAmbient_refinedMixedAffine_iff
    (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) (S : BlockRefinement B)
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) (B.flatten S) (B.flatten S) 1)
    (ω : Rep.{uW} ℂ ((B.flatten S).Levi F.Carrier))
    (r : Fin (B.flatten S).length → ℝ) (u : Fin B.length → ℝ) :
    Occurs T B (B.flatten S) (B.flatten S) σ 1 hw ω (unitaryAmbient B)
        (refinedMixedAffine B S r) u ↔
      T.IsOppositeJacquetClassExponent (B.flatten S) (unitaryInduced T B σ u)
        (Rep.of (T.leviComplexPowerTwist (B.flatten S)
          (fun k => (r k : ℂ) +
            Complex.I * (u ((B.flattenBlockEquiv S).symm k).1 : ℂ)) ω.ρ)) := by
  rw [Occurs, unitaryAmbient_apply, transported_one]
  rfl

end Langlands.ComplexTwistFamilies
