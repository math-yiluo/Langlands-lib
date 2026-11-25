import Langlands.MathlibBase

/-! # The additive character `ψ_A` and the duality `S ↦ S^*` (Bushnell–Kutzko 1993, §1.1)

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993): the additive
character `ψ_A = ψ_F ∘ tr_A` of `A = End_F(V)` (notation, printed pp. 19–20), the dual
`S^* = {x ∈ A : ψ_A(xs) = 1 for all s ∈ S}` of a subset `S ⊆ A` ((1.1.4), printed p. 22), and the
function `ψ_b(g) = ψ_A(b(g - 1))` of (1.1.6), printed p. 22.
-/

noncomputable section

namespace Langlands.BushnellKutzko

universe uK uV

variable {K : Type uK} {V : Type uV} [Field K] [AddCommGroup V] [Module K V]

/-- The additive character `ψ_A = ψ_F ∘ tr_A` of `A = End_K(V)` attached to an additive character
`ψ_F` of `K` (BK93, printed pp. 19–20), where `tr_A` is the trace `LinearMap.trace K V`. -/
def traceCharacter (ψF : AddChar K ℂ) : AddChar (Module.End K V) ℂ :=
  ψF.compAddMonoidHom (LinearMap.trace K V).toAddMonoidHom

theorem traceCharacter_apply (ψF : AddChar K ℂ) (x : Module.End K V) :
    traceCharacter ψF x = ψF (LinearMap.trace K V x) :=
  rfl

/-- The dual `S^* = {x ∈ A : ψ(xs) = 1 for all s ∈ S}` of a subset `S` of `A = End_K(V)` with
respect to an additive character `ψ` of `A` (BK93 (1.1.4), printed p. 22). -/
def additiveDual (ψ : AddChar (Module.End K V) ℂ) (S : Set (Module.End K V)) :
    Set (Module.End K V) :=
  {x | ∀ s ∈ S, ψ (x * s) = 1}

theorem mem_additiveDual {ψ : AddChar (Module.End K V) ℂ} {S : Set (Module.End K V)}
    {x : Module.End K V} : x ∈ additiveDual ψ S ↔ ∀ s ∈ S, ψ (x * s) = 1 :=
  Iff.rfl

/-- The function `ψ_b : G → ℂ`, `ψ_b(g) = ψ(b(g - 1))`, attached to an additive character `ψ`
of `A = End_K(V)` and an element `b ∈ A` (BK93 (1.1.6), printed p. 22, where `ψ = ψ_A` and
`ψ_b(1 + x) = ψ_A(bx)`). It is defined on all of `G = Aut_K(V)`; BK93 restricts it to
`U^{r+1}(𝔄)`, where it is a character for suitable `b` (`AdditiveDualityStatement`). -/
def elementCharacter (ψ : AddChar (Module.End K V) ℂ) (b : Module.End K V) :
    (Module.End K V)ˣ → ℂ :=
  fun g => ψ (b * ((g : Module.End K V) - 1))

theorem elementCharacter_apply (ψ : AddChar (Module.End K V) ℂ) (b : Module.End K V)
    (g : (Module.End K V)ˣ) : elementCharacter ψ b g = ψ (b * ((g : Module.End K V) - 1)) :=
  rfl

end Langlands.BushnellKutzko
