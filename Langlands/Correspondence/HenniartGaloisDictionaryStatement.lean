import Langlands.Correspondence.HenniartLocalNumerical
import Langlands.Weil.Representation.Restriction

/-! # The finite-image Weil–Galois orbit dictionary -/

noncomputable section

universe uK uΩ uW

namespace Langlands.Henniart.LocalNumerical

open Langlands.VirtualRepresentation

/-- Rank-`n` isomorphism classes of continuous irreducible complex Galois representations. -/
abbrev IrreducibleGaloisClass
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ+) :=
  FiniteRepresentation.ContinuousIrreducibleClasses.{uΩ, uW} (Ω ≃ₐ[K] Ω) (n : ℕ)

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local notation "GalK" => Ω ≃ₐ[K] Ω

/-- Continuous complex Galois characters trivial on absolute inertia. -/
def galoisUnramifiedCharacters : Subgroup (GalK →ₜ* ℂˣ) where
  carrier := {χ | ∀ i : LocalGalois.SepClosed.absoluteInertia K Ω, χ i = 1}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro χ η hχ hη i
    change χ i * η i = 1
    rw [hχ i, hη i, mul_one]
  inv_mem' := by
    intro χ hχ i
    change (χ i)⁻¹ = 1
    rw [hχ i, inv_one]

/-- Twist a rank-`k + 1` Galois class by an unramified character. -/
def galoisUnramifiedTwist (k : ℕ) (χ : galoisUnramifiedCharacters K Ω) :
    IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat ≃
      IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat :=
  FiniteRepresentation.continuousIrreducibleTwistEquiv χ.val (k + 1)

/-- The natural cardinality of the unramified-twist stabilizer of a Galois class. -/
def galoisTorsionNumber {k : ℕ} (ρ : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat) :
    ℕ :=
  Nat.card {χ : galoisUnramifiedCharacters K Ω // galoisUnramifiedTwist K Ω k χ ρ = ρ}

@[instance_reducible]
private def galoisUnramifiedTwistAction :
    MulAction (galoisUnramifiedCharacters K Ω) (Weil.IrreducibleBasis.{uΩ, uW} GalK) :=
  letI := Weil.twistAction.{uΩ, uW} (G := GalK)
  MulAction.compHom (Weil.IrreducibleBasis.{uΩ, uW} GalK)
    (galoisUnramifiedCharacters K Ω).subtype

/-- Irreducible Galois classes of all positive ranks up to unramified twists. -/
abbrev GaloisUnramifiedOrbitClasses :=
  letI := galoisUnramifiedTwistAction.{uK, uΩ, uW} K Ω
  OrbitClasses (ι := Weil.IrreducibleBasis.{uΩ, uW} GalK) (galoisUnramifiedCharacters K Ω)

/-- Send a rank-tagged Galois class to its unramified-twist orbit. -/
def galoisUnramifiedOrbitClass (b : Weil.IrreducibleBasis.{uΩ, uW} GalK) :
    GaloisUnramifiedOrbitClasses.{uK, uΩ, uW} K Ω :=
  letI := galoisUnramifiedTwistAction.{uK, uΩ, uW} K Ω
  orbitClass (galoisUnramifiedCharacters K Ω) b

/-- The Weil class is the pullback of the Galois class along the canonical projection. -/
def IsGaloisPullback {k : ℕ} (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat)
    (ρ : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat) : Prop :=
  weilClassForget K Ω σ =
    FiniteRepresentation.restrictClass
      (@Weil.Local.SepClosed.localProjection K _ _ _ _ Ω _ _ _
        (IsSepClosure.sep_closed K)).toMonoidHom
      (Weil.underlyingClass GalK ⟨k.succPNat, ρ⟩)

/-- The Swan exponent of a Galois class is that of its Weil pullback. -/
def HasGaloisSwan {k : ℕ} (ρ : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat)
    (s : ℕ) : Prop :=
  ∃ σ, IsGaloisPullback K Ω σ ρ ∧ HasWeilSwan K Ω σ s

/-- Galois orbits containing a class of the specified rank, Swan exponent and torsion number. -/
def galoisRefinedStratum (k s f : ℕ) :
    Set (GaloisUnramifiedOrbitClasses.{uK, uΩ, uW} K Ω) :=
  {c | ∃ ρ : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat,
    galoisUnramifiedOrbitClass K Ω ⟨k.succPNat, ρ⟩ = c ∧
      HasGaloisSwan K Ω ρ s ∧ galoisTorsionNumber K Ω ρ = f}

end Langlands.Henniart.LocalNumerical

namespace Langlands.Henniart

open Langlands.VirtualRepresentation LocalNumerical

/-- Each irreducible Weil class has an unramified twist of Galois type. -/
def WeilGaloisTypeTwistStatement : Prop :=
  ∀ (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (k : ℕ) (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat),
    ∃ (z : ℂˣ) (ρ : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat),
      IsGaloisPullback K Ω (weilUnramifiedTwist K Ω k z σ) ρ

/-- Each Galois class has a unique Weil pullback, which in turn determines the Galois class. -/
def GaloisPullbackBijectionStatement : Prop :=
  ∀ (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ),
    (∀ ρ : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat,
      ∃! σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat, IsGaloisPullback K Ω σ ρ) ∧
    (∀ (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat)
      (ρ ρ' : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat),
      IsGaloisPullback K Ω σ ρ → IsGaloisPullback K Ω σ ρ' → ρ = ρ')

/-- Pullback preserves and reflects unramified-twist equivalence and preserves torsion numbers. -/
def GaloisPullbackTwistStatement : Prop :=
  ∀ (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ),
    (∀ (σ σ' : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat)
      (ρ ρ' : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat),
      IsGaloisPullback K Ω σ ρ → IsGaloisPullback K Ω σ' ρ' →
      ((∃ z : ℂˣ, σ' = weilUnramifiedTwist K Ω k z σ) ↔
        (∃ χ : galoisUnramifiedCharacters K Ω, ρ' = galoisUnramifiedTwist K Ω k χ ρ))) ∧
    (∀ (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat)
      (ρ : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat),
      IsGaloisPullback K Ω σ ρ → weilTorsionNumber K Ω σ = galoisTorsionNumber K Ω ρ)

/-- The orbit equivalence induced by pullback preserves the refined strata. -/
def WeilGaloisOrbitDictionaryStatement : Prop :=
  ∀ (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω],
    let d := @Weil.Local.SepClosed.localDegree K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K)
    ∃ e : Weil.UnramifiedOrbitClasses.{uΩ, uW} d ≃
        GaloisUnramifiedOrbitClasses.{uK, uΩ, uW} K Ω,
      (∀ (k : ℕ) (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat)
        (ρ : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat),
        IsGaloisPullback K Ω σ ρ →
        e (Weil.unramifiedOrbitClass d ⟨k.succPNat, σ⟩) =
          galoisUnramifiedOrbitClass K Ω ⟨k.succPNat, ρ⟩) ∧
      (∀ k s f : ℕ, e '' weilRefinedStratum K Ω k s f = galoisRefinedStratum K Ω k s f)

/-- The class-level and orbit-level Weil–Galois dictionary. -/
def WeilGaloisDictionaryStatement : Prop :=
  WeilGaloisTypeTwistStatement.{uK, uΩ, uW} ∧
    GaloisPullbackBijectionStatement.{uK, uΩ, uW} ∧
    GaloisPullbackTwistStatement.{uK, uΩ, uW} ∧
    WeilGaloisOrbitDictionaryStatement.{uK, uΩ, uW}

end Langlands.Henniart
