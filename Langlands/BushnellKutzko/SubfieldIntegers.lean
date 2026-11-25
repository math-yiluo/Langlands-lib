import Langlands.MathlibBase

/-! # A subfield `E` of `A = End_F(V)`: `𝔬_E`, `𝔭_E`, `e(E|F)` (Bushnell–Kutzko 1993, §1.2)

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), §1.2, printed
pp. 24–25, considers a subfield `E ⊇ F` of `A = End_F(V)` and views `V` as an `E`-vector space.
Here `E` is any field with an `F`-algebra structure acting on `V` compatibly with `F`
(`[Module E V] [IsScalarTower F E V]`); a subfield of `A` containing `F`, such as `F[β]` when
it is a field, is the case `E ⊆ A` acting by evaluation. This file constructs from `E` the ring of
integers `𝔬_E`, its maximal ideal `𝔭_E`, the ramification index `e(E|F)`, and the embeddings
`E → A`, `E^× → G = Aut_F(V)`.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uE uV

variable (F : Type uF) [Field F] (E : Type uE) [Field E] [Algebra F E]

section Integers

variable [ValuativeRel F]

/-- The ring of integers `𝔬_E` of `E`, constructed as the integral closure of `𝔬_F = 𝒪[F]`
in `E`. For a finite extension `E` of a nonarchimedean local field `F` this is the valuation
ring of `E`. -/
def subfieldIntegers : Subalgebra 𝒪[F] E :=
  integralClosure 𝒪[F] E

/-- The maximal ideal `𝔭_E` of `𝔬_E`, constructed as the Jacobson radical of
`subfieldIntegers F E`. For a finite extension `E` of a nonarchimedean local field `F` the ring
`𝔬_E` is a discrete valuation ring, so this is its unique maximal ideal. -/
def subfieldMaximalIdeal : Ideal (subfieldIntegers F E) :=
  Ring.jacobson (subfieldIntegers F E)

/-- The ramification index `e(E|F)`, constructed as Mathlib's `Ideal.ramificationIdx` of
`𝔭_E = subfieldMaximalIdeal F E` over `𝔬_F`: the length of `(𝔬_E)_{𝔭_E} / 𝔭_F (𝔬_E)_{𝔭_E}`,
that is, the integer `e` with `𝔭_F 𝔬_E = 𝔭_E^e`. -/
def subfieldRamificationIndex : ℕ :=
  (subfieldMaximalIdeal F E).ramificationIdx 𝒪[F]

end Integers

variable (V : Type uV) [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

/-- The embedding `E → A = End_F(V)` through which `E` acts on `V` (BK93 p. 24, "the given
inclusion `E → A`"): `a ↦ (v ↦ a • v)`. -/
def subfieldEmbedding : E →ₐ[F] Module.End F V :=
  Algebra.lsmul F F V

theorem subfieldEmbedding_apply (a : E) (v : V) : subfieldEmbedding F E V a v = a • v :=
  rfl

/-- The induced embedding `E^× → G = Aut_F(V)`. -/
def subfieldUnits : Eˣ →* (Module.End F V)ˣ :=
  Units.map (subfieldEmbedding F E V).toMonoidHom

theorem coe_subfieldUnits (a : Eˣ) :
    ((subfieldUnits F E V a : (Module.End F V)ˣ) : Module.End F V) =
      subfieldEmbedding F E V (a : E) :=
  rfl

end Langlands.BushnellKutzko
