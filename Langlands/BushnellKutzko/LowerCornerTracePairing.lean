import Langlands.BushnellKutzko.LowerCornerQuotient
import Langlands.BushnellKutzko.SimpleCharacterTraceDual

/-! # Trace characters separating the shifted lower-corner quotient -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V

variable (ψF : AddChar F ℂ) (β e₁ e₂ ζ' : Module.End F V)
  (I T X : Submodule 𝒪[F] (Module.End F V))
  (hI : I.map (adjointMap 𝒪[F] β) ≤ traceDualLattice ψF X)

local notation "Y" => lowerCornerQuotient T X e₁ e₂ ζ'

/-- The adjoint of `I` pairs with the shifted lower corner. Its containment in
`D(X)` makes the trace character descend to the quotient. -/
def lowerCornerTracePairing : I →+ AddChar Y ℂ where
  toFun y :=
    let f := ((AddMonoidHom.mulLeft (adjointMap O β (y : A))).comp
      (lowerCornerShift e₁ e₂ ζ').toAddMonoidHom).comp T.subtype.toAddMonoidHom
    AddChar.toAddMonoidHomEquiv.symm <|
      QuotientAddGroup.lift (X.comap ((lowerCornerShift e₁ e₂ ζ').comp T.subtype)).toAddSubgroup
        ((traceCharacter ψF).compAddMonoidHom f).toAddMonoidHom (fun x hx => by
          change traceCharacter ψF (adjointMap O β (y : A) * lowerCornerShift e₁ e₂ ζ' (x : A)) = 1
          exact hI (Submodule.mem_map_of_mem y.property) _ hx)
  map_zero' := by
    ext z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change traceCharacter ψF (adjointMap O β 0 * lowerCornerShift e₁ e₂ ζ' (x : A)) = 1
    rw [map_zero, zero_mul, AddChar.map_zero_eq_one]
  map_add' y y' := by
    ext z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change traceCharacter ψF (adjointMap O β ((y : A) + (y' : A)) * lowerCornerShift e₁ e₂ ζ' (x : A)) =
      traceCharacter ψF (adjointMap O β (y : A) * lowerCornerShift e₁ e₂ ζ' (x : A)) *
        traceCharacter ψF (adjointMap O β (y' : A) * lowerCornerShift e₁ e₂ ζ' (x : A))
    rw [map_add, add_mul, AddChar.map_add_eq_mul]

theorem lowerCornerTracePairing_mk (y : I) (x : T) :
    lowerCornerTracePairing ψF β e₁ e₂ ζ' I T X hI y (Submodule.Quotient.mk x) =
      traceCharacter ψF (adjointMap O β (y : A) * lowerCornerShift e₁ e₂ ζ' (x : A)) :=
  rfl

/-- Cyclicity of trace also expresses the pairing using the shifted upper
corner in the adjoint and the original representative in the second factor. -/
theorem lowerCornerTracePairing_upper_mk (he₁ : Commute β e₁) (he₂ : Commute β e₂)
    (hζ' : Commute β ζ') (y : I) (x : T) :
    lowerCornerTracePairing ψF β e₁ e₂ ζ' I T X hI y (Submodule.Quotient.mk x) =
      traceCharacter ψF (adjointMap O β (e₁ * (ζ' * (y : A)) * e₂) * (x : A)) := by
  rw [lowerCornerTracePairing_mk, lowerCornerShift_apply]
  have hAdj : adjointMap O β (e₁ * (ζ' * (y : A)) * e₂) =
      (e₁ * ζ') * adjointMap O β (y : A) * e₂ := by
    change β * (e₁ * (ζ' * (y : A)) * e₂) - (e₁ * (ζ' * (y : A)) * e₂) * β =
      (e₁ * ζ') * (β * (y : A) - (y : A) * β) * e₂
    calc
      _ = (β * (e₁ * ζ')) * (y : A) * e₂ - (e₁ * ζ') * (y : A) * (e₂ * β) := by noncomm_ring
      _ = _ := by
        rw [(he₁.mul_right hζ').eq, ← he₂.eq]
        noncomm_ring
  rw [hAdj, traceCharacter_apply, traceCharacter_apply]
  congr 1
  rw [show ((e₁ * ζ') * adjointMap O β (y : A) * e₂) * (x : A) =
    (e₁ * ζ') * (adjointMap O β (y : A) * e₂ * (x : A)) by noncomm_ring,
    LinearMap.trace_mul_comm F (e₁ * ζ')]
  simp only [mul_assoc]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- If the entire trace dual of `X` is obtained by adding the complementary
filtration step, the reference trace characters separate the quotient. -/
theorem lowerCornerTracePairing_separates (L : LatticeChain O F V) (hψ : IsBKAdditiveCharacter ψF)
    (m : ℤ) (hX : X ≤ L.endFiltration m) (hT : T ≤ L.endFiltration (m + 1))
    (he₁ : e₁ ∈ L.endFiltration 0) (he₂ : e₂ ∈ L.endFiltration 0)
    (hζ' : ζ' ∈ L.endFiltration (-1))
    (hdual : traceDualLattice ψF X = I.map (adjointMap O β) ⊔ L.endFiltration (1 - m)) :
    ∀ z : Y, (∀ y : I, lowerCornerTracePairing ψF β e₁ e₂ ζ' I T X hI y z = 1) → z = 0 := by
  let := L.finiteDimensional
  intro z hz
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Submodule.Quotient.mk_eq_zero]
  let v := lowerCornerShift e₁ e₂ ζ' (x : A)
  change v ∈ X
  have hv : v ∈ L.endFiltration m :=
    mul_mul_mem_endFiltration L (L.mul_mem_endFiltration he₂ (hT x.property)) he₁ hζ' (by ring)
  have hP : v ∈ traceDualLattice ψF (L.endFiltration (1 - m)) := by
    rwa [traceDualLattice_endFiltration L ψF hψ, show 1 - (1 - m) = m by ring]
  have hvdual : v ∈ traceDualLattice ψF (traceDualLattice ψF X) := by
    intro b hb
    rw [hdual] at hb
    obtain ⟨a, ⟨y, hy, rfl⟩, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
    rw [mul_add, AddChar.map_add_eq_mul]
    have hb := hz ⟨y, hy⟩
    rw [lowerCornerTracePairing_mk] at hb
    change traceCharacter ψF (adjointMap O β y * v) = 1 at hb
    have hleft : traceCharacter ψF (v * adjointMap O β y) = 1 := by
      rw [traceCharacter_apply, LinearMap.trace_mul_comm F]
      exact hb
    rw [hleft, hP c hc, mul_one]
  rwa [traceDualLattice_traceDualLattice_aux (traceDualLattice ψF)
    (mem_additiveDual_iff_trace ψF hψ) ((L.fg_endFiltration m).of_le hX)] at hvdual

/-- The reference family separates the shifted lower-corner quotient when the
trace dual is the sum of the adjoint image and the complementary ambient step. -/
def LowerCornerTracePairingStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V]
    (L : LatticeChain 𝒪[F] F V) (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (β e₁ e₂ ζ' : Module.End F V) (I T X : Submodule 𝒪[F] (Module.End F V))
      (hI : I.map (adjointMap 𝒪[F] β) ≤ traceDualLattice ψF X)
      (m : ℤ), X ≤ L.endFiltration m → T ≤ L.endFiltration (m + 1) →
      e₁ ∈ L.endFiltration 0 → e₂ ∈ L.endFiltration 0 → ζ' ∈ L.endFiltration (-1) →
      traceDualLattice ψF X = I.map (adjointMap 𝒪[F] β) ⊔ L.endFiltration (1 - m) →
      ∀ z : lowerCornerQuotient T X e₁ e₂ ζ',
        (∀ y : I, lowerCornerTracePairing ψF β e₁ e₂ ζ' I T X hI y z = 1) → z = 0

theorem lowerCornerTracePairingSeparation : LowerCornerTracePairingStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ L ψF hψ β e₁ e₂ ζ' I T X hI m hX hT he₁ he₂ hζ' hdual
  exact lowerCornerTracePairing_separates ψF β e₁ e₂ ζ' I T X hI L hψ m hX hT he₁ he₂ hζ' hdual

end Langlands.BushnellKutzko.SplitBlocks
