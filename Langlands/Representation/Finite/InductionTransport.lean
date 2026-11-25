import Langlands.Representation.Finite.Virtual
import Langlands.Representation.Twist.Definitions
import Mathlib.RepresentationTheory.Induced

/-!
# Induction along an isomorphism of the inducing group, and the two rank-one representations

`indCongrEquiv`: replacing the inducing group of `Representation.ind` along a group
isomorphism `e : H' ≃* H`, compatibly with the maps to `G` and with the representations,
does not change the induced representation. Both sides are coinvariants of the same space
`k[G] ⊗ V` for the same relations.

`oneDimensionalEquiv`: the `FDRep` `oneDimensional χ` of the Library's Brauer theory and the
scalar representation `Langlands.characterRepresentation χ` of the twist interface are the
same action of `H` on `k` by `χ`.
-/

noncomputable section

namespace Langlands.FiniteRep

universe uk uG uH uH' uV

section Transport

variable {k : Type uk} [CommRing k] {G : Type uG} {H : Type uH} {H' : Type uH'}
  [Group G] [Group H] [Group H'] {V : Type uV} [AddCommGroup V] [Module k V]

/-- **Induction does not change when the inducing group is replaced along an isomorphism.**
For `e : H' ≃* H`, homomorphisms `φ : H →* G`, `φ' : H' →* G` with `φ' = φ ∘ e` and
representations `ρ` of `H`, `ρ'` of `H'` on `V` with `ρ' = ρ ∘ e`, the induced representations
`Ind_{φ'} ρ'` and `Ind_φ ρ` of `G` are equivalent. The compatibilities are hypotheses on
elements because the carrier `Representation.IndV φ ρ` depends on `φ` and `ρ`. -/
def indCongrEquiv (e : H' ≃* H) {φ : H →* G} {φ' : H' →* G} (hφ : ∀ h, φ' h = φ (e h))
    {ρ : Representation k H V} {ρ' : Representation k H' V} (hρ : ∀ h, ρ' h = ρ (e h)) :
    (Representation.ind φ' ρ').Equiv (Representation.ind φ ρ) := by
  have htprod (h : H') :
      Representation.tprod ((Representation.leftRegular k G).comp φ') ρ' h =
        Representation.tprod ((Representation.leftRegular k G).comp φ) ρ (e h) := by
    simp only [Representation.tprod_apply, MonoidHom.coe_comp, Function.comp_apply, hφ, hρ]
  refine Representation.Equiv.mk
    { toLinearMap := Representation.Coinvariants.lift _
        (Representation.Coinvariants.mk _) (fun h => by
          rw [htprod h]
          exact LinearMap.ext fun x => Representation.Coinvariants.mk_self_apply _ _ x)
      invFun := Representation.Coinvariants.lift _
        (Representation.Coinvariants.mk _) (fun s => by
          obtain ⟨h, rfl⟩ := e.surjective s
          rw [← htprod h]
          exact LinearMap.ext fun x => Representation.Coinvariants.mk_self_apply _ _ x)
      left_inv := fun x => by
        induction x using Representation.Coinvariants.induction_on with
        | h v => rfl
      right_inv := fun x => by
        induction x using Representation.Coinvariants.induction_on with
        | h v => rfl } ?_
  intro g
  ext h v
  simp

end Transport

section RankOne

variable {k : Type uk} [Field k] {H : Type uH} [Group H]

/-- **The two rank-one representations attached to a character agree.** The action of
`oneDimensional χ` (an `FDRep` on `k`) and the scalar representation
`Langlands.characterRepresentation χ` both multiply by `χ h`; the identity of `k` intertwines
them. -/
def oneDimensionalEquiv (χ : H →* kˣ) :
    Representation.Equiv (oneDimensional χ).ρ (Langlands.characterRepresentation χ) :=
  Representation.Equiv.mk (LinearEquiv.refl k k) (by
    intro h
    apply LinearMap.ext_ring
    change (χ h : k) • (1 : k) = (χ h : k) • (1 : k)
    rfl)

end RankOne

end Langlands.FiniteRep
