import Langlands.Correspondence.HenniartGaloisDictionaryProof
import Langlands.Correspondence.HenniartLadicClasses
import Langlands.Weil.Representation.FiniteImageCoefficientDescent

/-! # ℓ-adic models of continuous complex Galois representations -/

noncomputable section

set_option autoImplicit false

universe uK uΩ uG uW

namespace Langlands.Henniart.LocalNumerical

open FiniteRepresentation VirtualRepresentation
open Langlands.Weil.Local.SepClosed

section Model

variable {G : Type uG} [Group G] (ℓ : ℕ) [Fact ℓ.Prime]

local notation "E" => PadicAlgCl ℓ

/-- A finite-image ℓ-adic action is defined over a finite coefficient extension. -/
theorem isLadicDefinedOverFiniteExtension_of_finite_range
    (A : FiniteRepresentation.{0, uG, uW} E G) (hA : (Set.range A.representation).Finite) :
    IsLadicDefinedOverFiniteExtension ℓ A := by
  let b := Module.finBasis E A
  let : Finite (Set.range A.representation) := hA.to_subtype
  let n := Module.finrank E A
  let entries : Set E := Set.range
    (fun x : (Set.range A.representation) × Fin n × Fin n => b.repr (x.1.val (b x.2.2)) x.2.1)
  let : Finite entries := (Set.finite_range _).to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[ℓ] entries, IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x), b, ?_⟩
  intro g i j
  apply IntermediateField.subset_adjoin
  exact ⟨(⟨A.representation g, g, rfl⟩, i, j), rfl⟩

variable [TopologicalSpace G] [NonarchimedeanGroup G] [CompactSpace G]

/-- Every continuous irreducible complex action of a compact nonarchimedean
group has a continuous irreducible ℓ-adic model with a finite coefficient field. -/
def ladicModelOfContinuousComplex (ι : E →+* ℂ)
    (A : FiniteRepresentation.{0, uG, uW} ℂ G) (hA : A.IsContinuous) (hi : A.IsIrreducible) :
    letI := ι.toAlgebra
    {B : FiniteImageCoefficientModel (k := E) ℂ A //
      IsLadicContinuous ℓ B.model ∧ IsLadicDefinedOverFiniteExtension ℓ B.model} := by
  letI := ι.toAlgebra
  let B := finiteImageCoefficientModel (k := E) ℂ A hi (finite_range_of_isContinuous A hA)
  refine ⟨B, ?_, isLadicDefinedOverFiniteExtension_of_finite_range ℓ B.model B.finite_range⟩
  let : TopologicalSpace (Module.End E B.model) := moduleTopology E (Module.End E B.model)
  exact Weil.continuous_of_open_kernel B.model.representation
    (B.ker_eq.symm ▸ isOpen_ker_of_isContinuous A hA)

end Model

section Local

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ →+* ℂ)

/-- A Weil class that is pulled back from a complex Galois class is the
transport of an irreducible ℓ-adic Galois class. -/
theorem exists_ladicWeilTransport_of_galoisPullback {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat}
    {ρ : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat}
    (h : IsGaloisPullback K Ω σ ρ) :
    ∃ τ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat,
      weilClassForget K Ω σ = ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ τ) := by
  let := IsSepClosure.sep_closed K (K := Ω)
  let := absoluteGalois_nonarchimedean K Ω
  let := absoluteGalois_compactSpace K Ω
  let := ι.toAlgebra
  obtain ⟨A, hAc, hAi, hclass⟩ := exists_classOf_eq_underlyingClass
    (G := Ω ≃ₐ[K] Ω) ⟨k.succPNat, ρ⟩
  let B := ladicModelOfContinuousComplex ℓ ι A hAc hAi
  let e : FiniteRepresentation.Equiv (ladicScalarExtension ℓ ι B.val.model) A := B.val.scalarEquiv
  have hrankA : A.rank = k + 1 := (congrArg classRank hclass).trans ρ.property
  have hrankB : B.val.model.rank = k + 1 :=
    ((rank_extendCoefficients ℂ B.val.model).symm.trans (rank_eq_of_equiv e)).trans hrankA
  let τ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat :=
    ⟨Quotient.mk _ ⟨B.val.model, B.property.1, B.property.2, B.val.irreducible⟩, hrankB⟩
  refine ⟨τ, ?_⟩
  rw [IsGaloisPullback] at h
  rw [h, ← hclass]
  exact (classOf_eq_iff _ _).mpr ⟨(restrictEquiv (localProjection K Ω).toMonoidHom e).symm⟩

/-- Every irreducible complex Weil class has an unramified twist in the
image of ℓ-adic transport, for each chosen coefficient embedding. -/
theorem exists_unramifiedTwist_ladicWeilTransport (k : ℕ)
    (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat) :
    ∃ (z : ℂˣ) (τ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat),
      weilClassForget K Ω (weilUnramifiedTwist K Ω k z σ) =
        ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ τ) := by
  obtain ⟨z, ρ, hρ⟩ := weilGaloisTypeTwist K Ω k σ
  obtain ⟨τ, hτ⟩ := exists_ladicWeilTransport_of_galoisPullback K Ω ℓ ι hρ
  exact ⟨z, τ, hτ⟩

end Local

end Langlands.Henniart.LocalNumerical
