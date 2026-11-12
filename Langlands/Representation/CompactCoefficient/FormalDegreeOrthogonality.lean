import Langlands.Representation.CompactCoefficient.CompactFormalDegreeStatements
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Langlands.Representation.Hecke.CommonInvarianceProof

noncomputable section

universe u v w

open MeasureTheory

namespace Langlands.Renard.CompactRepresentation

open CompactSplitting HarmonicAnalysis

section Coefficients

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
  (hc : HasCompactSmoothDualCoefficients ρ)

/-- Inverse coefficients, linear in both the smooth functional and the vector. -/
def formalDegreeCoefficient : SmoothDual ρ →ₗ[ℂ] V →ₗ[ℂ] SchwartzBruhat G where
  toFun ℓ := testMap ρ hρ hc ℓ.val ℓ.property
  map_add' ℓ η := by
    ext x g
    rfl
  map_smul' c ℓ := by
    ext x g
    rfl

@[simp] theorem formalDegreeCoefficient_apply (ℓ : SmoothDual ρ) (x : V) (g : G) :
    formalDegreeCoefficient ρ hρ hc ℓ x g = ℓ.val (ρ g⁻¹ x) := rfl

variable [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]

/-- Evaluate the coefficient operator at one fixed vector and functional. -/
def coefficientDualOperator (a : V) (m : Module.Dual ℂ V) :
    SmoothDual ρ →ₗ[ℂ] Module.Dual ℂ V where
  toFun ℓ := m.comp (Hecke.integratedAction μ ρ hρ
    (formalDegreeCoefficient ρ hρ hc ℓ a))
  map_add' ℓ η := by
    ext x
    simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply]
  map_smul' c ℓ := by
    ext x
    simp only [map_smul, LinearMap.smul_apply, LinearMap.comp_apply, RingHom.id_apply]

@[simp] theorem coefficientDualOperator_apply (a : V) (m : Module.Dual ℂ V)
    (ℓ : SmoothDual ρ) (x : V) :
    coefficientDualOperator ρ hρ hc μ a m ℓ x =
      m (Hecke.integratedAction μ ρ hρ (formalDegreeCoefficient ρ hρ hc ℓ a) x) := rfl

/-- Right invariance of Haar measure makes the coefficient operator commute
with the contragredient action. -/
theorem coefficientDualOperator_intertwines [μ.IsMulRightInvariant]
    (a : V) (m : Module.Dual ℂ V) (g : G) (ℓ : SmoothDual ρ) :
    coefficientDualOperator ρ hρ hc μ a m (smoothContragredient ρ g ℓ) =
      ρ.dual g (coefficientDualOperator ρ hρ hc μ a m ℓ) := by
  ext x
  change coefficientDualOperator ρ hρ hc μ a m (smoothContragredient ρ g ℓ) x =
    coefficientDualOperator ρ hρ hc μ a m ℓ (ρ g⁻¹ x)
  simp only [coefficientDualOperator_apply, Hecke.integratedAction_dual,
    formalDegreeCoefficient_apply]
  change (∫ y, ℓ.val (ρ g⁻¹ (ρ y⁻¹ a)) * m (ρ y x) ∂μ) =
    ∫ y, ℓ.val (ρ y⁻¹ a) * m (ρ y (ρ g⁻¹ x)) ∂μ
  rw [← integral_mul_right_eq_self
    (fun y => ℓ.val (ρ g⁻¹ (ρ y⁻¹ a)) * m (ρ y x)) g⁻¹]
  congr 1
  funext y
  simp only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply,
    Representation.inv_self_apply]

/-- The evaluated coefficient operator as a smooth-dual endomorphism. -/
def coefficientDualIntertwiner [μ.IsMulRightInvariant]
    (a : V) (m : Module.Dual ℂ V) :
    (smoothContragredient ρ).IntertwiningMap (smoothContragredient ρ) :=
  smoothLift (isSmooth_smoothContragredient ρ)
    (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (coefficientDualOperator ρ hρ hc μ a m)
      (coefficientDualOperator_intertwines ρ hρ hc μ a m))

/-- Two applications of admissible Schur give the coefficient orthogonality
formula, initially without the nonvanishing assertion. -/
theorem exists_formalDegreeScalar [μ.IsMulRightInvariant]
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (ha : IsAdmissible ρ) (hi : ρ.IsIrreducible) :
    ∃ κ : ℂ, ∀ (ℓ : SmoothDual ρ) (x a : V),
      Hecke.integratedAction μ ρ hρ (formalDegreeCoefficient ρ hρ hc ℓ a) x =
        (κ * ℓ.val x) • a := by
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : V)
  obtain ⟨m₀, hm₀, hm₀a⟩ := exists_smooth_functional_ne_zero hcof ρ hρ ha₀
  let m : Module.Dual ℂ V := (m₀ a₀)⁻¹ • m₀
  have hma : m a₀ = 1 := by simp [m, hm₀a]
  have hda := isAdmissible_smoothContragredient_of_compact_cofinal hcof ρ ha
  have hdi := isIrreducible_smoothContragredient hcof ρ ha hi
  obtain ⟨κ, hκ, -⟩ := admissibleSchur_scalarEndomorphism
    (smoothContragredient ρ) hda hdi (coefficientDualIntertwiner ρ hρ hc μ a₀ m)
  have hD (ℓ : SmoothDual ρ) (x : V) :
      coefficientDualOperator ρ hρ hc μ a₀ m ℓ x = κ * ℓ.val x := by
    have h := congrArg (fun T : (smoothContragredient ρ).IntertwiningMap
      (smoothContragredient ρ) => (T ℓ).val x) hκ
    exact h
  refine ⟨κ, ?_⟩
  intro ℓ x a
  let T := liftMap μ ρ hρ hc ℓ.val ℓ.property ρ hρ x
  obtain ⟨c, hcT, -⟩ := admissibleSchur_scalarEndomorphism ρ ha hi T
  have hT (b : V) : T b = c • b := congrArg (fun S : ρ.IntertwiningMap ρ => S b) hcT
  have hDc : coefficientDualOperator ρ hρ hc μ a₀ m ℓ x = c := by
    change m (T a₀) = c
    rw [hT, map_smul, hma, smul_eq_mul, mul_one]
  change T a = (κ * ℓ.val x) • a
  rw [hT, ← hDc, hD]

/-- The scalar in the coefficient formula is nonzero, by a positive square
integral of a nonzero compact coefficient. -/
theorem formalDegreeScalar_ne_zero
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hi : ρ.IsIrreducible) {κ : ℂ}
    (hκ : ∀ (ℓ : SmoothDual ρ) (x a : V),
      Hecke.integratedAction μ ρ hρ (formalDegreeCoefficient ρ hρ hc ℓ a) x =
        (κ * ℓ.val x) • a) : κ ≠ 0 := by
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : V)
  obtain ⟨ℓ₀, hℓ₀, hℓ₀a⟩ := exists_smooth_functional_ne_zero hcof ρ hρ ha₀
  let m := formLeft μ ρ hρ hc hℓ₀ a₀
  have hm : IsSmoothVector ρ.dual m := formLeft_isSmoothVector μ ρ hρ hc hℓ₀ a₀
  intro hzero
  have hact := hκ ⟨m, hm⟩ a₀ a₀
  rw [hzero, zero_mul, zero_smul] at hact
  have hz := congrArg m hact
  rw [Hecke.integratedAction_dual, map_zero] at hz
  let F : G → ℂ := fun y => m (ρ y a₀)
  have hF : Continuous F :=
    ((Hecke.orbitMap_locallyConstant ρ (hρ a₀)).comp m).continuous
  have hFc : HasCompactSupport F := hc a₀ m hm
  have hF1 : F 1 ≠ 0 := by
    change form μ ρ ℓ₀ (ρ 1 a₀) a₀ ≠ 0
    rw [map_one, Module.End.one_apply]
    exact form_self_ne_zero μ ρ hρ hc hℓ₀ hℓ₀a
  apply integral_mul_conj_ne_zero μ hF hFc hF1
  rw [← hz]
  congr 1
  funext y
  rw [formalDegreeCoefficient_apply, mul_comm]
  congr 1
  change starRingEnd ℂ (form μ ρ ℓ₀ (ρ y a₀) a₀) =
    form μ ρ ℓ₀ (ρ y⁻¹ a₀) a₀
  rw [form_conj, ← form_invariant μ ρ ℓ₀ y⁻¹ a₀ (ρ y a₀),
    Representation.inv_self_apply]

end Coefficients

/-- Renard IV.1.4, Proposition and the nonzero inverse formal degree. -/
theorem compactCoefficientFormalDegree : CompactCoefficientFormalDegreeStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ _ μ _ _ _ τ hi hc
  have hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hL, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
    exact ⟨L, hL, hLK⟩
  let C := formalDegreeCoefficient τ.representation τ.isSmooth hc
  have htest (a : τ) (ℓ : SmoothDual τ.representation) (f : Hecke.HeckeAlgebra μ)
      (hf : ∀ g, f g = ℓ.val (τ.representation g⁻¹ a)) :
      Hecke.HeckeAlgebra.toTestFunction μ f = C ℓ a := by
    ext g
    exact hf g
  refine ⟨?_, ?_, ?_⟩
  · intro a ℓ
    exact ⟨(Hecke.HeckeAlgebra.toTestFunction μ).symm (C ℓ a), fun _ => rfl⟩
  · intro σ hσ hne a ℓ f hf
    apply LinearMap.ext
    intro x
    let T := liftMap μ τ.representation τ.isSmooth hc ℓ.val ℓ.property
      σ.representation σ.isSmooth x
    let := hi
    let := hσ
    have hT : T = 0 :=
      (Representation.IsIrreducible.bijective_or_eq_zero T).resolve_left (by
        intro hb
        exact hne.false (SmoothRep.mkIso (T.ofBijective hb).symm))
    change Hecke.integratedAction μ σ.representation σ.isSmooth
      (Hecke.HeckeAlgebra.toTestFunction μ f) x = 0
    rw [htest a ℓ f hf]
    exact congrArg (fun S : τ.representation.IntertwiningMap σ.representation => S a) hT
  · have ha := isAdmissible_of_compactCoefficients μ hcof τ.representation τ.isSmooth hi hc
    obtain ⟨κ, hκ⟩ := exists_formalDegreeScalar τ.representation τ.isSmooth hc μ hcof ha hi
    refine ⟨κ, formalDegreeScalar_ne_zero τ.representation τ.isSmooth hc μ hcof hi hκ, ?_⟩
    intro a ℓ f hf x
    change Hecke.integratedAction μ τ.representation τ.isSmooth
      (Hecke.HeckeAlgebra.toTestFunction μ f) x = _
    rw [htest a ℓ f hf]
    exact hκ ℓ x a

end Langlands.Renard.CompactRepresentation
