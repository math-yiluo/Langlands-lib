import Langlands.Automorphic.DeterminantMultiplier
import Langlands.Global.AdelicGLTopology
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Langlands.Representation.Twist.ContinuousCharacterProof

/-! # Local constancy of the finite determinant factor of every Hecke character

The finite adelic matrix group is locally compact and totally disconnected, so by
van Dantzig's theorem its open subgroups form a neighbourhood basis of the identity.
A continuous homomorphism from such a group to `ℂˣ` has open kernel, because `ℂˣ` has
a neighbourhood of `1` containing no nontrivial subgroup. No finite-order hypothesis
on the Hecke character is needed.
-/

noncomputable section

universe u

open NumberField IsDedekindDomain
open scoped RestrictedProduct

set_option autoImplicit false

namespace Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The finite adelic matrix group is totally disconnected: its matrix entries embed it
continuously and injectively in a product of totally disconnected spaces. -/
theorem finiteAdelicGL_totallyDisconnectedSpace :
    TotallyDisconnectedSpace (FiniteAdelicGL F n) := by
  let : TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) :=
    finiteAdeles_totallyDisconnectedSpace F
  let : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → FiniteAdeleRing (𝓞 F) F))
  constructor
  exact isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- Van Dantzig: the finite adelic matrix group has a basis of open subgroups at `1`. -/
theorem finiteAdelicGL_nonarchimedeanGroup : NonarchimedeanGroup (FiniteAdelicGL F n) := by
  let := finiteAdelicGL_totallyDisconnectedSpace F n
  let : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let : T2Space (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :=
    inferInstanceAs (T2Space (Fin n → Fin n → FiniteAdeleRing (𝓞 F) F))
  refine { is_nonarchimedean := ?_ }
  intro U hU
  obtain ⟨H, _, hH⟩ :=
    ((Langlands.Topology.LocallyProfiniteProof.vanDantzig _).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib).2 U hU
  exact ⟨H, hH⟩

/-- A homomorphism to `ℂˣ` with open kernel is locally constant as a `ℂˣ`-valued map. -/
theorem isLocallyConstant_of_isOpen_ker {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (θ : H →* ℂˣ) (hθ : IsOpen (θ.ker : Set H)) :
    IsLocallyConstant θ := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro u
  refine ⟨(fun v : H => u⁻¹ * v) ⁻¹' (θ.ker : Set H),
    hθ.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro v hv
    have hv' : θ (u⁻¹ * v) = 1 := hv
    rw [map_mul, map_inv, inv_mul_eq_one] at hv'
    exact hv'.symm

namespace HeckeCharacter

variable {F}

/-- The determinant factor of any Hecke character on the finite adelic matrix group has
open kernel. -/
theorem isOpen_ker_finiteDeterminant (χ : HeckeCharacter F) :
    IsOpen (((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).toMonoidHom.ker :
      Set (FiniteAdelicGL F n)) := by
  let := finiteAdelicGL_nonarchimedeanGroup F n
  exact Langlands.isOpen_ker_of_continuous_complex_character _
    ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).continuous

/-- The determinant factor of any Hecke character on the finite adelic matrix group is
locally constant. -/
theorem isLocallyConstant_finiteDeterminant (χ : HeckeCharacter F) :
    IsLocallyConstant ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)) :=
  isLocallyConstant_of_isOpen_ker _ (χ.isOpen_ker_finiteDeterminant n)

/-- The complex values of the finite determinant factor are locally constant. -/
theorem isLocallyConstant_finiteDeterminant_val (χ : HeckeCharacter F) :
    IsLocallyConstant (fun d : FiniteAdelicGL F n =>
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ)) :=
  (χ.isLocallyConstant_finiteDeterminant n).comp (fun z : ℂˣ => (z : ℂ))

end HeckeCharacter

end Langlands.Global
