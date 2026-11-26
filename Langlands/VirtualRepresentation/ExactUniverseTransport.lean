import Langlands.VirtualRepresentation.ExactTensor
import Langlands.Weil.Representation.SubquotientContinuity
import Langlands.Correspondence.TriangularArithmeticGamma

/-!
# Changing the carrier universe of finite representations

A finite-dimensional representation is equivalent to a copy on the standard carrier
`ULift (Fin n → ℂ)` in any carrier universe. The copy is functorial on intertwiners
and preserves short exact sequences, so it induces an integer-linear map between the
exact Grothendieck groups of continuous representations in two carrier universes.
-/

noncomputable section

set_option autoImplicit false

universe uG uV uW uA uB uC

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- The standard carrier `ULift (Fin n → ℂ)`, in an arbitrary universe, of a finite
representation of dimension `n`. -/
def transportLinearEquiv (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    ULift.{uW} (Fin (Module.finrank ℂ A) → ℂ) ≃ₗ[ℂ] A :=
  ULift.moduleEquiv.trans (Module.finBasis ℂ A).equivFun.symm

/-- A copy of a finite representation with carrier in the universe `uW`. -/
def transport (A : FiniteRepresentation.{0, uG, uV} ℂ G) : FiniteRepresentation.{0, uG, uW} ℂ G :=
  of (transportRepresentation A.representation (transportLinearEquiv.{uG, uV, uW} A).symm)

/-- The copy on coordinates is equivalent to the original representation. -/
def coordinatesEquiv (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    FiniteRepresentation.Equiv (transport A : FiniteRepresentation.{0, uG, uW} ℂ G) A :=
  (transportEquiv A.representation (transportLinearEquiv.{uG, uV, uW} A).symm).symm

end Langlands.FiniteRepresentation

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- An intertwiner transported to the standard copies. -/
def transportHom {A : FiniteRepresentation.{0, uG, uA} ℂ G}
    {B : FiniteRepresentation.{0, uG, uB} ℂ G}
    (f : A.representation.IntertwiningMap B.representation) :
    (transport A : FiniteRepresentation.{0, uG, uW} ℂ G).representation.IntertwiningMap
      (transport B : FiniteRepresentation.{0, uG, uW} ℂ G).representation :=
  ((coordinatesEquiv B).symm.toIntertwiningMap.comp f).comp (coordinatesEquiv A).toIntertwiningMap

theorem transportHom_apply {A : FiniteRepresentation.{0, uG, uA} ℂ G}
    {B : FiniteRepresentation.{0, uG, uB} ℂ G}
    (f : A.representation.IntertwiningMap B.representation)
    (x : (transport A : FiniteRepresentation.{0, uG, uW} ℂ G)) :
    transportHom f x = (coordinatesEquiv B).symm (f (coordinatesEquiv A x)) := rfl

/-- Transport preserves short exact sequences. -/
theorem isShortExact_transportHom {A : FiniteRepresentation.{0, uG, uA} ℂ G}
    {B : FiniteRepresentation.{0, uG, uB} ℂ G} {C : FiniteRepresentation.{0, uG, uC} ℂ G}
    {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation}
    (h : IsShortExact f g) :
    IsShortExact
      (transportHom f : (transport A : FiniteRepresentation.{0, uG, uW} ℂ G).representation.IntertwiningMap
        (transport B : FiniteRepresentation.{0, uG, uW} ℂ G).representation)
      (transportHom g : (transport B : FiniteRepresentation.{0, uG, uW} ℂ G).representation.IntertwiningMap
        (transport C : FiniteRepresentation.{0, uG, uW} ℂ G).representation) := by
  obtain ⟨hf, hg, hfg⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    rw [transportHom_apply, transportHom_apply] at hxy
    exact (coordinatesEquiv.{uG, uA, uW} A).toLinearEquiv.injective
      (hf ((coordinatesEquiv.{uG, uB, uW} B).symm.toLinearEquiv.injective hxy))
  · intro z
    obtain ⟨y, hy⟩ := hg (coordinatesEquiv.{uG, uC, uW} C z)
    refine ⟨(coordinatesEquiv.{uG, uB, uW} B).symm y, ?_⟩
    rw [transportHom_apply]
    rw [Representation.Equiv.apply_symm_apply, hy, Representation.Equiv.symm_apply_apply]
  · ext y
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, rfl⟩
      change (coordinatesEquiv.{uG, uC, uW} C).symm (g ((coordinatesEquiv.{uG, uB, uW} B)
        ((coordinatesEquiv.{uG, uB, uW} B).symm (f (coordinatesEquiv.{uG, uA, uW} A x))))) = 0
      rw [Representation.Equiv.apply_symm_apply]
      have : f (coordinatesEquiv.{uG, uA, uW} A x) ∈ LinearMap.ker g.toLinearMap :=
        hfg ▸ ⟨_, rfl⟩
      rw [LinearMap.mem_ker] at this
      change (coordinatesEquiv.{uG, uC, uW} C).symm (g.toLinearMap _) = 0
      rw [this, map_zero]
    · intro hy
      have hy' : coordinatesEquiv.{uG, uB, uW} B y ∈ LinearMap.ker g.toLinearMap := by
        rw [LinearMap.mem_ker]
        have := congrArg (coordinatesEquiv.{uG, uC, uW} C) hy
        rw [map_zero] at this
        change coordinatesEquiv C ((coordinatesEquiv.{uG, uC, uW} C).symm (g (coordinatesEquiv.{uG, uB, uW} B y))) = 0 at this
        rwa [Representation.Equiv.apply_symm_apply] at this
      rw [← hfg] at hy'
      obtain ⟨x, hx⟩ := hy'
      refine ⟨(coordinatesEquiv.{uG, uA, uW} A).symm x, ?_⟩
      change (coordinatesEquiv.{uG, uB, uW} B).symm (f ((coordinatesEquiv.{uG, uA, uW} A) ((coordinatesEquiv.{uG, uA, uW} A).symm x))) = y
      rw [Representation.Equiv.apply_symm_apply]
      change (coordinatesEquiv.{uG, uB, uW} B).symm (f.toLinearMap x) = y
      rw [hx, Representation.Equiv.symm_apply_apply]

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The class of the transported copy of a continuous representation. -/
def continuousTransportClass :
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) →
      Continuous.{uG, uW} G :=
  Quotient.lift
    (fun A => ofRepresentation _ ⟨(transport A.val : FiniteRepresentation.{0, uG, uW} ℂ G),
      (isContinuous_iff_of_equiv (coordinatesEquiv A.val)).mpr A.property⟩)
    (fun A B hAB => by
      obtain ⟨e⟩ := hAB
      exact ofRepresentation_eq_of_equiv _
        (((coordinatesEquiv A.val).trans e).trans (coordinatesEquiv B.val).symm))

theorem continuousTransportClass_isExactAdditive :
    IsExactAdditive (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
      (continuousTransportClass.{uG, uV, uW} (G := G)) := by
  intro A B C f g h
  exact ofRepresentation_shortExact _ (isShortExact_transportHom h)

/-- Change of carrier universe on the exact Grothendieck group of continuous
representations. -/
def continuousTransport : Continuous.{uG, uV} G →ₗ[ℤ] Continuous.{uG, uW} G :=
  lift _ continuousTransportClass continuousTransportClass_isExactAdditive

@[simp]
theorem continuousTransport_ofRepresentation
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // A.IsContinuous}) :
    continuousTransport.{uG, uV, uW} (ofRepresentation _ A) =
      ofRepresentation _ ⟨(transport A.val : FiniteRepresentation.{0, uG, uW} ℂ G),
        (isContinuous_iff_of_equiv (coordinatesEquiv A.val)).mpr A.property⟩ :=
  lift_ofRepresentation _ _ _ _

/-- On an actual representation, transport is the class of any equivalent
representation in the target universe. -/
theorem continuousTransport_ofRepresentation_of_equiv
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // A.IsContinuous})
    (B : {B : FiniteRepresentation.{0, uG, uW} ℂ G // B.IsContinuous})
    (e : FiniteRepresentation.Equiv A.val B.val) :
    continuousTransport.{uG, uV, uW} (ofRepresentation _ A) = ofRepresentation _ B := by
  rw [continuousTransport_ofRepresentation]
  exact ofRepresentation_eq_of_equiv _ ((coordinatesEquiv A.val).trans e)

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
