import Langlands.VirtualRepresentation.Weil.Generic
import Langlands.Weil.Representation.TwistClasses

/-!
# Actual character twists and twist orbits of the irreducible lattice

The maps extend the genuine class equivalences, with no chosen representative.
The unramified action uses every complex unit through an actual degree map.
-/

noncomputable section

universe uG uV

namespace Langlands.VirtualRepresentation.Weil

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Twist each genuine irreducible class, retaining its positive rank. -/
def twistBasisEquiv (χ : G →ₜ* ℂˣ) :
    IrreducibleBasis.{uG, uV} G ≃ IrreducibleBasis.{uG, uV} G :=
  Equiv.sigmaCongrRight (fun n =>
    FiniteRepresentation.continuousIrreducibleTwistEquiv χ (n : ℕ))

@[simp]
theorem twistBasisEquiv_rank (χ : G →ₜ* ℂˣ) (b : IrreducibleBasis.{uG, uV} G) :
    (twistBasisEquiv χ b).1 = b.1 := rfl

@[simp]
theorem underlyingClass_twistBasisEquiv (χ : G →ₜ* ℂˣ)
    (b : IrreducibleBasis.{uG, uV} G) :
    underlyingClass G (twistBasisEquiv χ b) =
      FiniteRepresentation.twistClass χ.toMonoidHom (underlyingClass G b) :=
  FiniteRepresentation.forget_continuousIrreducibleTwistEquiv χ _ b.2

@[simp]
theorem twistBasisEquiv_one :
    twistBasisEquiv (1 : G →ₜ* ℂˣ) =
      Equiv.refl (IrreducibleBasis.{uG, uV} G) := by
  apply Equiv.ext
  rintro ⟨n, b⟩
  simp [twistBasisEquiv]

theorem twistBasisEquiv_mul (χ η : G →ₜ* ℂˣ) :
    (twistBasisEquiv.{uG, uV} η).trans (twistBasisEquiv χ) =
      twistBasisEquiv (χ * η) := by
  apply Equiv.ext
  rintro ⟨n, b⟩
  exact congrArg (Sigma.mk n)
    (Equiv.congr_fun (FiniteRepresentation.continuousIrreducibleTwistEquiv_mul χ η n) b)

@[simp]
theorem twistBasisEquiv_symm (χ : G →ₜ* ℂˣ) :
    (twistBasisEquiv.{uG, uV} χ).symm = twistBasisEquiv χ⁻¹ := by
  apply Equiv.ext
  rintro ⟨n, b⟩
  rfl

/-- Extend the actual character twist by integral linearity. -/
def twistLatticeEquiv (χ : G →ₜ* ℂˣ) :
    IrreducibleLattice.{uG, uV} G ≃ₗ[ℤ] IrreducibleLattice.{uG, uV} G :=
  reindex (twistBasisEquiv χ)

@[simp]
theorem twistLatticeEquiv_single (χ : G →ₜ* ℂˣ)
    (b : IrreducibleBasis.{uG, uV} G) (m : ℤ) :
    twistLatticeEquiv χ (Finsupp.single b m) =
      Finsupp.single (twistBasisEquiv χ b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem twistLatticeEquiv_generator (χ : G →ₜ* ℂˣ)
    (b : IrreducibleBasis.{uG, uV} G) :
    twistLatticeEquiv χ (generator b) = generator (twistBasisEquiv χ b) :=
  twistLatticeEquiv_single χ b 1

/-- Multiplicities are transported along the actual basis equivalence. -/
@[simp]
theorem twistLatticeEquiv_coefficient (χ : G →ₜ* ℂˣ)
    (x : IrreducibleLattice.{uG, uV} G) (b : IrreducibleBasis.{uG, uV} G) :
    twistLatticeEquiv χ x (twistBasisEquiv χ b) = x b := by
  change x ((twistBasisEquiv χ).symm (twistBasisEquiv χ b)) = x b
  exact congrArg x ((twistBasisEquiv χ).symm_apply_apply b)

@[simp]
theorem twistLatticeEquiv_one :
    twistLatticeEquiv (1 : G →ₜ* ℂˣ) =
      LinearEquiv.refl ℤ (IrreducibleLattice.{uG, uV} G) := by
  simp [twistLatticeEquiv, reindex]

theorem twistLatticeEquiv_mul (χ η : G →ₜ* ℂˣ) :
    (twistLatticeEquiv.{uG, uV} η).trans (twistLatticeEquiv χ) =
      twistLatticeEquiv (χ * η) := by
  simp only [twistLatticeEquiv, reindex, Finsupp.domLCongr_trans, twistBasisEquiv_mul]

@[simp]
theorem twistLatticeEquiv_symm (χ : G →ₜ* ℂˣ) :
    (twistLatticeEquiv.{uG, uV} χ).symm = twistLatticeEquiv χ⁻¹ := by
  simp [twistLatticeEquiv, reindex]

/-- Scalar twisting preserves the rank-weighted integer degree. -/
@[simp]
theorem degree_twistLatticeEquiv (χ : G →ₜ* ℂˣ)
    (x : IrreducibleLattice.{uG, uV} G) :
    degree G (twistLatticeEquiv χ x) = degree G x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m =>
    simp [degree, rankedDegree, VirtualRepresentation.degree, extend]

/-- Scalar twisting preserves the coefficient pairing on the irreducible basis. -/
theorem multiplicityPairing_twistLatticeEquiv (χ : G →ₜ* ℂˣ)
    (x y : IrreducibleLattice.{uG, uV} G) :
    multiplicityPairing G (twistLatticeEquiv χ x) (twistLatticeEquiv χ y) =
      multiplicityPairing G x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | single b m =>
    simp [multiplicityPairing, pairing, extend, coefficient]

/-- The effective cone is preserved and reflected by actual character twisting. -/
theorem effective_twistLatticeEquiv_iff (χ : G →ₜ* ℂˣ)
    (x : IrreducibleLattice.{uG, uV} G) :
    twistLatticeEquiv χ x ∈ VirtualRepresentation.effective ↔
      x ∈ VirtualRepresentation.effective := by
  change (∀ b, 0 ≤ twistLatticeEquiv χ x b) ↔ ∀ b, 0 ≤ x b
  constructor
  · intro h b
    simpa using h (twistBasisEquiv χ b)
  · intro h b
    obtain ⟨a, rfl⟩ := (twistBasisEquiv χ).surjective b
    simpa using h a

/-- The actual continuous-character action on genuine positive-rank classes. -/
@[instance_reducible]
def twistAction : MulAction (G →ₜ* ℂˣ) (IrreducibleBasis.{uG, uV} G) where
  smul χ b := twistBasisEquiv χ b
  one_smul b := by
    change twistBasisEquiv (1 : G →ₜ* ℂˣ) b = b
    rw [twistBasisEquiv_one]
    rfl
  mul_smul χ η b := (Equiv.congr_fun (twistBasisEquiv_mul χ η) b).symm

/-- Classes up to twisting by an actual continuous complex character. -/
abbrev TwistOrbitClasses (G : Type uG) [Group G] [TopologicalSpace G] :=
  letI := twistAction.{uG, uV} (G := G)
  OrbitClasses (ι := IrreducibleBasis.{uG, uV} G) (G →ₜ* ℂˣ)

/-- Send an actual irreducible class to its character-twist orbit. -/
def twistOrbitClass (b : IrreducibleBasis.{uG, uV} G) : TwistOrbitClasses.{uG, uV} G :=
  letI := twistAction (G := G)
  orbitClass (G →ₜ* ℂˣ) b

/-- Orbit equality means that an actual continuous character carries one class to the other. -/
theorem twistOrbitClass_eq_iff (a b : IrreducibleBasis.{uG, uV} G) :
    twistOrbitClass a = twistOrbitClass b ↔
      ∃ χ : G →ₜ* ℂˣ, twistBasisEquiv χ b = a := by
  let := twistAction.{uG, uV} (G := G)
  change Quotient.mk _ a = Quotient.mk _ b ↔ _
  rw [Quotient.eq]
  exact MulAction.mem_orbit_iff

/-- Add coefficients within each actual character-twist orbit. -/
def twistOrbitMap :
    IrreducibleLattice.{uG, uV} G →ₗ[ℤ] IntegralLattice (TwistOrbitClasses.{uG, uV} G) :=
  map twistOrbitClass

/-- The action of all complex unramified twists for a supplied continuous degree map. -/
@[instance_reducible]
def unramifiedTwistAction (d : G →ₜ* Langlands.Weil.Degree) :
    MulAction ℂˣ (IrreducibleBasis.{uG, uV} G) where
  smul z b := twistBasisEquiv (Langlands.Weil.Local.unramifiedCharacter d z) b
  one_smul b := by
    change twistBasisEquiv (Langlands.Weil.Local.unramifiedCharacterHom d 1) b = b
    rw [map_one, twistBasisEquiv_one]
    rfl
  mul_smul z w b := by
    change twistBasisEquiv (Langlands.Weil.Local.unramifiedCharacterHom d (z * w)) b = _
    rw [map_mul]
    exact (Equiv.congr_fun (twistBasisEquiv_mul _ _) b).symm

/-- The integer-linear action of an actual unramified character. -/
def unramifiedTwistLatticeEquiv (d : G →ₜ* Langlands.Weil.Degree) (z : ℂˣ) :
    IrreducibleLattice.{uG, uV} G ≃ₗ[ℤ] IrreducibleLattice.{uG, uV} G :=
  twistLatticeEquiv (Langlands.Weil.Local.unramifiedCharacter d z)

/-- Genuine unramified-twist orbits, including phase and magnitude of every complex unit. -/
abbrev UnramifiedOrbitClasses (d : G →ₜ* Langlands.Weil.Degree) :=
  letI := unramifiedTwistAction.{uG, uV} d
  OrbitClasses (ι := IrreducibleBasis.{uG, uV} G) ℂˣ

def unramifiedOrbitClass (d : G →ₜ* Langlands.Weil.Degree)
    (b : IrreducibleBasis.{uG, uV} G) : UnramifiedOrbitClasses.{uG, uV} d :=
  letI := unramifiedTwistAction d
  orbitClass ℂˣ b

/-- The orbit quotient identifies exactly the actual unramified twists. -/
theorem unramifiedOrbitClass_eq_iff (d : G →ₜ* Langlands.Weil.Degree)
    (a b : IrreducibleBasis.{uG, uV} G) :
    unramifiedOrbitClass d a = unramifiedOrbitClass d b ↔
      ∃ z : ℂˣ, twistBasisEquiv (Langlands.Weil.Local.unramifiedCharacter d z) b = a := by
  let := unramifiedTwistAction.{uG, uV} d
  change Quotient.mk _ a = Quotient.mk _ b ↔ _
  rw [Quotient.eq]
  exact MulAction.mem_orbit_iff

/-- Integral collection of coefficients on genuine unramified-twist orbits. -/
def unramifiedOrbitMap (d : G →ₜ* Langlands.Weil.Degree) :
    IrreducibleLattice.{uG, uV} G →ₗ[ℤ] IntegralLattice (UnramifiedOrbitClasses.{uG, uV} d) :=
  map (unramifiedOrbitClass d)

/-- Positive rank descends to the actual unramified-twist orbit quotient. -/
def unramifiedOrbitRank (d : G →ₜ* Langlands.Weil.Degree) :
    UnramifiedOrbitClasses.{uG, uV} d → ℕ+ := by
  letI := unramifiedTwistAction.{uG, uV} d
  exact Quotient.lift (fun b : IrreducibleBasis G => b.1) (by
    intro a b hab
    obtain ⟨z, hz⟩ := MulAction.mem_orbit_iff.mp hab
    exact (congrArg Sigma.fst hz).symm)

@[simp]
theorem unramifiedOrbitRank_class (d : G →ₜ* Langlands.Weil.Degree)
    (b : IrreducibleBasis.{uG, uV} G) :
    unramifiedOrbitRank d (unramifiedOrbitClass d b) = b.1 := rfl

/-- The genuine orbit classes of a fixed positive rank; no finiteness is imposed. -/
def unramifiedOrbitRankStratum (d : G →ₜ* Langlands.Weil.Degree) (n : ℕ+) :
    Set (UnramifiedOrbitClasses.{uG, uV} d) :=
  {c | unramifiedOrbitRank d c = n}

end Langlands.VirtualRepresentation.Weil
