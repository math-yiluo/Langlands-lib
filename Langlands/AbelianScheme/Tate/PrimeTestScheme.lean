import Langlands.AbelianScheme.Tate.TestScheme
import Langlands.AbelianScheme.Tate.PrimeComparison

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Tate.PrimeAdic
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]
variable {T T' T'' : Over S} (p : ℕ) [Fact p.Prime]

/-- Restriction on actual prime-power torsion preserves p-adic residue scalars. -/
def levelTestRestrict (a : T' ⟶ T) (n : ℕ) :
    Level G T (p ^ n) →ₗ[ℤ_[p]] Level G T' (p ^ n) where
  toAddHom := levelRestrict G a (p ^ n)
  map_smul' r x := ZMod.map_smul (levelRestrict G a (p ^ n)) (PadicInt.toZModPow n r) x

/-- Actual test-scheme restriction on the prime-adic inverse limit. -/
def testRestrict (a : T' ⟶ T) : Integral G T p →ₗ[ℤ_[p]] Integral G T' p :=
  lift G T' p (fun n => (levelTestRestrict G p a n).comp (evaluation G T p n)) (by
    intro n x
    change transition G T' _ (levelRestrict G a (p ^ (n + 1)) (x.val (n + 1))) =
      levelRestrict G a (p ^ n) (x.val n)
    rw [← levelRestrict_transition, x.property n])

@[simp] theorem evaluation_testRestrict (a : T' ⟶ T) (n : ℕ) (x : Integral G T p) :
    evaluation G T' p n (testRestrict G p a x) =
      levelRestrict G a (p ^ n) (evaluation G T p n x) := rfl

@[simp] theorem testRestrict_id : testRestrict G p (𝟙 T) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  apply toSection_injective G T (p ^ n)
  exact Category.id_comp (Additive.toMul (x.val n)).val

/-- Restriction composes contravariantly on the existing prime-adic carrier. -/
theorem testRestrict_comp (a : T' ⟶ T) (b : T'' ⟶ T') :
    testRestrict G p (b ≫ a) = (testRestrict G p b).comp (testRestrict G p a) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  apply toSection_injective G T'' (p ^ n)
  exact Category.assoc b a (Additive.toMul (x.val n)).val

theorem continuous_testRestrict (a : T' ⟶ T) : Continuous (testRestrict G p a) :=
  continuous_lift G T' p _ _ (fun n =>
    (continuous_of_discreteTopology (f := levelTestRestrict G p a n)).comp
      (continuous_evaluation G T p n))

/-- The same restriction, with its integral continuity bundled. -/
def continuousTestRestrict (a : T' ⟶ T) : Integral G T p →L[ℤ_[p]] Integral G T' p :=
  { testRestrict G p a with cont := continuous_testRestrict G p a }

@[simp] theorem continuousTestRestrict_apply (a : T' ⟶ T) (x : Integral G T p) :
    continuousTestRestrict G p a x = testRestrict G p a x := rfl

/-- Extend actual integral restriction to the existing p-adic rational Tate module. -/
def rationalTestRestrict (a : T' ⟶ T) : Rational G T p →ₗ[ℚ_[p]] Rational G T' p :=
  (testRestrict G p a).baseChange ℚ_[p]

@[simp] theorem rationalTestRestrict_tmul (a : T' ⟶ T) (q : ℚ_[p]) (x : Integral G T p) :
    rationalTestRestrict G p a (q ⊗ₜ[ℤ_[p]] x) = q ⊗ₜ[ℤ_[p]] testRestrict G p a x := rfl

@[simp] theorem rationalTestRestrict_id : rationalTestRestrict G p (𝟙 T) = LinearMap.id := by
  simp [rationalTestRestrict]
  rfl

theorem rationalTestRestrict_comp (a : T' ⟶ T) (b : T'' ⟶ T') :
    rationalTestRestrict G p (b ≫ a) =
      (rationalTestRestrict G p b).comp (rationalTestRestrict G p a) := by
  simp only [rationalTestRestrict, testRestrict_comp, LinearMap.baseChange_comp]
  rfl

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]

/-- Restriction commutes with the actual induced prime-adic homomorphism. -/
theorem testRestrict_map (a : T' ⟶ T) (f : G ⟶ H) (x : Integral G T p) :
    testRestrict H p a (map T p f x) = map T' p f (testRestrict G p a x) := by
  apply Subtype.ext
  funext n
  apply toSection_injective H T' (p ^ n)
  exact (Category.assoc a (Additive.toMul (x.val n)).val f.hom.hom).symm

/-- This compatibility survives scalar extension to the p-adic field. -/
theorem rationalTestRestrict_map (a : T' ⟶ T) (f : G ⟶ H) (x : Rational G T p) :
    rationalTestRestrict H p a (rationalMap T p f x) =
      rationalMap T' p f (rationalTestRestrict G p a x) := by
  have h : (testRestrict H p a).comp (map T p f) =
      (map T' p f).comp (testRestrict G p a) :=
    LinearMap.ext (testRestrict_map p a f)
  have hq := congrArg (fun k => k.baseChange ℚ_[p]) h
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hq
  exact LinearMap.congr_fun hq x

end Langlands.GroupScheme.Tate.PrimeAdic

namespace Langlands.GroupScheme.Tate.PrimeComparison
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]
variable {T T' : Over S} (p : ℕ) [Fact p.Prime]

/-- Extracting prime-power coordinates commutes with test-scheme restriction. -/
theorem toPrime_testRestrict (P : ℕ → Prop) (hP : ∀ n : ℕ, P (p ^ n))
    (a : T' ⟶ T) (x : Integral G T P) :
    toPrime G T' P p hP (testRestrict G P a x) =
      PrimeAdic.testRestrict G p a (toPrime G T P p hP x) := rfl

/-- The full prime-coordinate square. -/
theorem fullToPrime_testRestrict (a : T' ⟶ T) (x : Full G T) :
    fullToPrime G T' p (testRestrict G (fun _ => True) a x) =
      PrimeAdic.testRestrict G p a (fullToPrime G T p x) := rfl

/-- The away square keeps the explicit coprimality hypothesis. -/
theorem awayToPrime_testRestrict (m : ℕ) (h : Nat.Coprime p m)
    (a : T' ⟶ T) (x : Away G T m) :
    awayToPrime G T' p m h (testRestrict G (fun n => Nat.Coprime n m) a x) =
      PrimeAdic.testRestrict G p a (awayToPrime G T p m h x) := rfl

end Langlands.GroupScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate.PrimeAdic
universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) {T T' : Over S} (p : ℕ) [Fact p.Prime]

/-- Integral restriction for the actual abelian scheme. -/
abbrev testRestrict (a : T' ⟶ T) :
    GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p →L[ℤ_[p]]
      GroupScheme.Tate.PrimeAdic.Integral A.toGrp T' p :=
  GroupScheme.Tate.PrimeAdic.continuousTestRestrict A.toGrp p a

/-- Rational restriction for the actual abelian scheme. -/
abbrev rationalTestRestrict (a : T' ⟶ T) :
    GroupScheme.Tate.PrimeAdic.Rational A.toGrp T p →ₗ[ℚ_[p]]
      GroupScheme.Tate.PrimeAdic.Rational A.toGrp T' p :=
  GroupScheme.Tate.PrimeAdic.rationalTestRestrict A.toGrp p a

end Langlands.AbelianScheme.Tate.PrimeAdic
