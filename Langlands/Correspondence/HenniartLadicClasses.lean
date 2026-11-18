import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.Weil.Local.Assembly
import Langlands.Weil.Representation.Restriction
import Langlands.Weil.Representation.TwistClasses
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Irreducible ℓ-adic local Galois classes and their unramified twists -/

noncomputable section

universe uK uΩ uG uW

namespace Langlands.Henniart.LocalNumerical

open FiniteRepresentation

section Coefficients

variable {G : Type uG} [Group G] (ℓ : ℕ) [Fact ℓ.Prime]

local notation "E" => PadicAlgCl ℓ

/-- Continuity for the module topology on the endomorphisms of the actual carrier. -/
def IsLadicContinuous [TopologicalSpace G] (A : FiniteRepresentation.{0, uG, uW} E G) : Prop :=
  letI : TopologicalSpace (Module.End E A) := moduleTopology E (Module.End E A)
  Continuous A.representation

/-- In one basis, every matrix entry of every action lies in a common finite extension. -/
def IsLadicDefinedOverFiniteExtension (A : FiniteRepresentation.{0, uG, uW} E G) : Prop :=
  ∃ L : IntermediateField ℚ_[ℓ] E, FiniteDimensional ℚ_[ℓ] L ∧
    ∃ b : Module.Basis (Fin (Module.finrank E A)) E A,
      ∀ (g : G) i j, b.repr (A.representation g (b j)) i ∈ L

/-- Extend scalars through the chosen embedding into `ℂ` on the tensor-product carrier. -/
def ladicScalarExtension (ι : E →+* ℂ) (A : FiniteRepresentation.{0, uG, uW} E G) :
    FiniteRepresentation.{0, uG, uW} ℂ G :=
  letI : Algebra E ℂ := ι.toAlgebra
  of ((Module.End.baseChangeHom E ℂ A).toMonoidHom.comp A.representation)

/-- Tensoring an invertible intertwiner gives an invertible intertwiner after extending scalars. -/
theorem ladicScalarExtension_isIsomorphic (ι : E →+* ℂ)
    {A B : FiniteRepresentation.{0, uG, uW} E G} (h : IsIsomorphic A B) :
    IsIsomorphic (ladicScalarExtension ℓ ι A) (ladicScalarExtension ℓ ι B) := by
  obtain ⟨e⟩ := h
  let : Algebra E ℂ := ι.toAlgebra
  refine ⟨Representation.Equiv.mk (e.toLinearEquiv.baseChange E ℂ) ?_⟩
  intro g
  change e.toLinearEquiv.toLinearMap.baseChange ℂ ∘ₗ (A.representation g).baseChange ℂ =
    (B.representation g).baseChange ℂ ∘ₗ e.toLinearEquiv.toLinearMap.baseChange ℂ
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
  exact congrArg (LinearMap.baseChange ℂ) (e.toIntertwiningMap.isIntertwining' g)

/-- Extend scalars on genuine isomorphism classes. -/
def ladicScalarExtensionClass (ι : E →+* ℂ) :
    IsomorphismClasses.{0, uG, uW} E G → IsomorphismClasses.{0, uG, uW} ℂ G :=
  Quotient.map (ladicScalarExtension ℓ ι) (fun _ _ h => ladicScalarExtension_isIsomorphic ℓ ι h)

private abbrev HasFiniteLadicValues (χ : G → Eˣ) : Prop :=
  ∃ L : IntermediateField ℚ_[ℓ] E, FiniteDimensional ℚ_[ℓ] L ∧ ∀ g, (χ g : E) ∈ L

private theorem isLadicContinuous_twist [TopologicalSpace G] (χ : G →ₜ* Eˣ)
    {A : FiniteRepresentation.{0, uG, uW} E G} (hA : IsLadicContinuous ℓ A) :
    IsLadicContinuous ℓ (FiniteRepresentation.twist χ.toMonoidHom A) := by
  let : TopologicalSpace (Module.End E A) := moduleTopology E (Module.End E A)
  let : IsModuleTopology E (Module.End E A) := ⟨rfl⟩
  change Continuous (fun g : G => (χ g : E) • A.representation g)
  exact (Units.continuous_val.comp χ.continuous).smul hA

private theorem isLadicDefinedOverFiniteExtension_twist (χ : G →* Eˣ)
    (hχ : HasFiniteLadicValues ℓ χ) {A : FiniteRepresentation.{0, uG, uW} E G}
    (hA : IsLadicDefinedOverFiniteExtension ℓ A) :
    IsLadicDefinedOverFiniteExtension ℓ (FiniteRepresentation.twist χ A) := by
  obtain ⟨L, hL, b, hb⟩ := hA
  obtain ⟨M, hM, hχ⟩ := hχ
  let := hL
  let := hM
  refine ⟨L ⊔ M, inferInstance, b, ?_⟩
  intro g i j
  change b.repr ((χ g : E) • A.representation g (b j)) i ∈ L ⊔ M
  rw [map_smul]
  exact mul_mem (SetLike.le_def.mp le_sup_right (hχ g))
    (SetLike.le_def.mp le_sup_left (hb g i j))

private abbrev IsIrreducibleLadic [TopologicalSpace G]
    (A : FiniteRepresentation.{0, uG, uW} E G) : Prop :=
  IsLadicContinuous ℓ A ∧ IsLadicDefinedOverFiniteExtension ℓ A ∧
    Representation.IsIrreducible A.representation

end Coefficients

section LocalField

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
variable (ℓ : ℕ) [Fact ℓ.Prime]

local notation "E" => PadicAlgCl ℓ
local notation "GalK" => Ω ≃ₐ[K] Ω

/-- Continuous ℓ-adic Galois characters trivial on inertia and with values in a finite extension. -/
def ladicUnramifiedCharacters : Subgroup (GalK →ₜ* Eˣ) where
  carrier := {χ | (∀ i : LocalGalois.SepClosed.absoluteInertia K Ω, χ i = 1) ∧
    HasFiniteLadicValues ℓ χ}
  one_mem' := ⟨fun _ => rfl, ⊥, inferInstance, fun _ => one_mem _⟩
  mul_mem' := by
    rintro χ η ⟨hχ, L, hL, hχL⟩ ⟨hη, M, hM, hηM⟩
    let := hL
    let := hM
    refine ⟨fun i => ?_, L ⊔ M, inferInstance, fun g => ?_⟩
    · change χ i * η i = 1
      rw [hχ i, hη i, mul_one]
    · change (χ g : E) * (η g : E) ∈ L ⊔ M
      exact mul_mem (SetLike.le_def.mp le_sup_left (hχL g))
        (SetLike.le_def.mp le_sup_right (hηM g))
  inv_mem' := by
    rintro χ ⟨hχ, L, hL, hχL⟩
    refine ⟨fun i => ?_, L, hL, fun g => ?_⟩
    · change (χ i)⁻¹ = 1
      rw [hχ i, inv_one]
    · change (↑((χ g)⁻¹) : E) ∈ L
      rw [Units.val_inv_eq_inv_val]
      exact inv_mem (hχL g)

/-- Positive-rank irreducible ℓ-adic Galois classes with continuity and a finite model. -/
def IrreducibleLadicClass
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ+) :=
  IsomorphismClassesOfRankWith (G := Ω ≃ₐ[K] Ω) (IsIrreducibleLadic.{uΩ, uW} ℓ) (n : ℕ)

/-- The underlying genuine Galois representation class. -/
def ladicClassForget {n : ℕ+} (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ n) :
    IsomorphismClasses.{0, _, uW} E GalK :=
  forgetPropertyClass _ ρ.val

private theorem ladicClassForget_injective {n : ℕ+} :
    Function.Injective (ladicClassForget.{uK, uΩ, uW} K Ω ℓ (n := n)) :=
  fun _ _ h => Subtype.ext (forgetPropertyClass_injective _ h)

private def ladicTwistPropertyClass (χ : ladicUnramifiedCharacters K Ω ℓ) :
    IsomorphismClassesWith (G := GalK) (IsIrreducibleLadic.{_, uW} ℓ) →
      IsomorphismClassesWith (G := GalK) (IsIrreducibleLadic.{_, uW} ℓ) :=
  Quotient.map
    (fun A => ⟨FiniteRepresentation.twist χ.val.toMonoidHom A.val,
      isLadicContinuous_twist ℓ χ.val A.property.1,
      isLadicDefinedOverFiniteExtension_twist ℓ χ.val.toMonoidHom χ.property.2 A.property.2.1,
      (Langlands.twistSubrepresentationOrderIso χ.val.toMonoidHom
        A.val.representation).isSimpleOrder_iff.mp A.property.2.2⟩)
    (fun _ _ ⟨e⟩ => ⟨FiniteRepresentation.twistEquiv χ.val.toMonoidHom e⟩)

private theorem forget_ladicTwistPropertyClass (χ : ladicUnramifiedCharacters K Ω ℓ)
    (c : IsomorphismClassesWith (G := GalK) (IsIrreducibleLadic.{_, uW} ℓ)) :
    forgetPropertyClass _ (ladicTwistPropertyClass K Ω ℓ χ c) =
      twistClassEquiv χ.val.toMonoidHom (forgetPropertyClass _ c) := by
  refine Quotient.inductionOn c ?_
  intro A
  rfl

private def ladicTwistAtRank (k : ℕ) (χ : ladicUnramifiedCharacters K Ω ℓ)
    (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) :
    IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat :=
  ⟨ladicTwistPropertyClass K Ω ℓ χ ρ.val, by
    rw [forget_ladicTwistPropertyClass, classRank_twistClassEquiv]
    exact ρ.property⟩

private theorem forget_ladicTwistAtRank (k : ℕ) (χ : ladicUnramifiedCharacters K Ω ℓ)
    (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) :
    ladicClassForget K Ω ℓ (ladicTwistAtRank K Ω ℓ k χ ρ) =
      twistClassEquiv χ.val.toMonoidHom (ladicClassForget K Ω ℓ ρ) :=
  forget_ladicTwistPropertyClass K Ω ℓ χ ρ.val

/-- Twisting in rank `k + 1`, with the inverse character giving the inverse equivalence. -/
def ladicUnramifiedTwist (k : ℕ) (χ : ladicUnramifiedCharacters K Ω ℓ) :
    IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat ≃
      IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat where
  toFun := ladicTwistAtRank K Ω ℓ k χ
  invFun := ladicTwistAtRank K Ω ℓ k χ⁻¹
  left_inv ρ := by
    apply ladicClassForget_injective K Ω ℓ
    rw [forget_ladicTwistAtRank, forget_ladicTwistAtRank]
    exact twistClass_inv_twistClass _ _
  right_inv ρ := by
    apply ladicClassForget_injective K Ω ℓ
    rw [forget_ladicTwistAtRank, forget_ladicTwistAtRank]
    exact twistClass_twistClass_inv _ _

/-- Forgetting the certificates commutes with the Library's class-twist equivalence. -/
@[simp]
theorem ladicClassForget_unramifiedTwist (k : ℕ) (χ : ladicUnramifiedCharacters K Ω ℓ)
    (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) :
    ladicClassForget K Ω ℓ (ladicUnramifiedTwist K Ω ℓ k χ ρ) =
      twistClassEquiv χ.val.toMonoidHom (ladicClassForget K Ω ℓ ρ) :=
  forget_ladicTwistAtRank K Ω ℓ k χ ρ

/-- The cardinality of the subtype of unramified self-twisting characters. -/
def ladicTorsionNumber {k : ℕ} (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) : ℕ :=
  Nat.card {χ : ladicUnramifiedCharacters K Ω ℓ // ladicUnramifiedTwist K Ω ℓ k χ ρ = ρ}

/-- The group of unramified characters acts by twisting within each positive rank. -/
@[instance_reducible]
def ladicUnramifiedTwistAction : MulAction (ladicUnramifiedCharacters K Ω ℓ)
    (Σ k : ℕ, IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) where
  smul χ ρ := ⟨ρ.1, ladicUnramifiedTwist K Ω ℓ ρ.1 χ ρ.2⟩
  one_smul := by
    rintro ⟨k, ρ⟩
    apply congrArg (Sigma.mk k)
    apply ladicClassForget_injective K Ω ℓ
    rw [ladicClassForget_unramifiedTwist]
    exact twistClass_one _
  mul_smul χ η := by
    rintro ⟨k, ρ⟩
    apply congrArg (Sigma.mk k)
    change ladicUnramifiedTwist K Ω ℓ k (χ * η) ρ =
      ladicUnramifiedTwist K Ω ℓ k χ (ladicUnramifiedTwist K Ω ℓ k η ρ)
    apply ladicClassForget_injective K Ω ℓ
    simp only [ladicClassForget_unramifiedTwist, twistClassEquiv_apply, twistClass_twistClass]
    rfl

/-- The orbit quotient of all positive-rank irreducible ℓ-adic classes. -/
abbrev LadicUnramifiedOrbitClasses :=
  letI := ladicUnramifiedTwistAction.{uK, uΩ, uW} K Ω ℓ
  MulAction.orbitRel.Quotient (ladicUnramifiedCharacters K Ω ℓ)
    (Σ k : ℕ, IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat)

/-- The unramified-twist orbit of a rank-`k + 1` class. -/
def ladicUnramifiedOrbitClass (k : ℕ) (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) :
    LadicUnramifiedOrbitClasses.{uK, uΩ, uW} K Ω ℓ :=
  letI := ladicUnramifiedTwistAction.{uK, uΩ, uW} K Ω ℓ
  Quotient.mk _ ⟨k, ρ⟩

open Weil.Local.SepClosed (localProjection localWeilGroup) in
/-- Restrict to the actual local Weil group and extend scalars to `ℂ` on isomorphism classes. -/
def ladicWeilTransport (ι : E →+* ℂ) :
    IsomorphismClasses.{0, _, uW} E GalK →
      (letI := IsSepClosure.sep_closed K (K := Ω)
       IsomorphismClasses.{0, _, uW} ℂ (localWeilGroup K Ω)) := by
  letI := IsSepClosure.sep_closed K (K := Ω)
  exact ladicScalarExtensionClass ℓ ι ∘ restrictClass (localProjection K Ω).toMonoidHom

end LocalField

end Langlands.Henniart.LocalNumerical
