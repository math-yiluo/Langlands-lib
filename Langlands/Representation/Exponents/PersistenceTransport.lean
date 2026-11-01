import Langlands.Representation.CuspidalSupport.WholeLeviTransport
import Langlands.Representation.Classification.MaximalConeLifting
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
import Langlands.Representation.Exponents.RealTwistFamilies

/-! Transport of cuspidality and of restricted coarse real twists. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV

namespace PadicField.TopologicalData

open CuspidalSupport RealTwistFamilies

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S R : BlockRefinement B)
  (h : Equiv.Perm (Fin n)) (hh : h ∈ blockWeyl B)
  (hc : ConjugatesLevi (F := F.Carrier) (B.flatten S) (B.flatten R) h)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

include hh

/-- Conjugation inside the coarse Levi leaves its restricted real character
unchanged, even between different fine refinements. -/
theorem leviRealPowerCharacter_restrictParameter_conjugation
    (t : Fin B.length → ℝ) (m : (B.flatten R).Levi F.Carrier) :
    T.leviRealPowerCharacter (B.flatten S) (restrictParameter B S t)
        ((leviConjugation (B.flatten S) (B.flatten R) h hc).symm m) =
      T.leviRealPowerCharacter (B.flatten R) (restrictParameter B R t) m := by
  have hemb :
      (flattenedLeviEquiv F.Carrier B S
        ((leviConjugation (B.flatten S) (B.flatten R) h hc).symm m)).val =
      (weylLeviElement (F := F.Carrier) h hh)⁻¹ *
        (flattenedLeviEquiv F.Carrier B R m).val *
          weylLeviElement (F := F.Carrier) h hh := by
    apply B.leviEmbedding_injective F.Carrier
    rw [flattenedLeviEquiv_embedding, leviConjugation_symm_embedding,
      map_mul, map_mul, map_inv, leviEmbedding_weylLeviElement,
      flattenedLeviEquiv_embedding]
  change T.leviRealPowerCharacter (B.flatten S)
      (fun k => t ((B.flattenBlockEquiv S).symm k).1) _ =
    T.leviRealPowerCharacter (B.flatten R)
      (fun k => t ((B.flattenBlockEquiv R).symm k).1) _
  rw [← T.leviRealPowerCharacter_flatten B S t, hemb,
    map_mul, map_mul, map_inv]
  rw [inv_mul_cancel_comm]
  exact T.leviRealPowerCharacter_flatten B R t m

/-- The repeated coarse twist commutes with transport by a permutation inside
the coarse block Weyl group. -/
theorem transport_restrictedLeviRealPowerTwist
    (t : Fin B.length → ℝ) (ρ : Representation ℂ ((B.flatten S).Levi F.Carrier) V) :
    transport (B.flatten S) (B.flatten R) h hc
        (T.leviRealPowerTwist (B.flatten S) (restrictParameter B S t) ρ) =
      T.leviRealPowerTwist (B.flatten R) (restrictParameter B R t)
        (transport (B.flatten S) (B.flatten R) h hc ρ) := by
  ext m x
  change (T.leviRealPowerCharacter (B.flatten S) (restrictParameter B S t)
      ((leviConjugation (B.flatten S) (B.flatten R) h hc).symm m) : ℂ) •
      ρ ((leviConjugation (B.flatten S) (B.flatten R) h hc).symm m) x =
    (T.leviRealPowerCharacter (B.flatten R) (restrictParameter B R t) m : ℂ) •
      ρ ((leviConjugation (B.flatten S) (B.flatten R) h hc).symm m) x
  rw [T.leviRealPowerCharacter_restrictParameter_conjugation B S R h hh hc t m]

/-- The actual intertwining equivalence retains the original vectors. -/
def restrictedRealTwistTransportEquiv
    (t : Fin B.length → ℝ) (ρ : Representation ℂ ((B.flatten S).Levi F.Carrier) V) :
    (transport (B.flatten S) (B.flatten R) h hc
      (T.leviRealPowerTwist (B.flatten S) (restrictParameter B S t) ρ)).Equiv
      (T.leviRealPowerTwist (B.flatten R) (restrictParameter B R t)
        (transport (B.flatten S) (B.flatten R) h hc ρ)) := by
  rw [T.transport_restrictedLeviRealPowerTwist B S R h hh hc]
  exact Representation.Equiv.refl _

/-- Split the nested parameter into its fixed fine twist and its restricted
coarse twist, preserving the actual conjugating permutation. -/
theorem transport_nestedLeviRealPowerTwist
    (v : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ)
    (ρ : Representation ℂ ((B.flatten S).Levi F.Carrier) V) :
    transport (B.flatten S) (B.flatten R) h hc
        (T.leviRealPowerTwist (B.flatten S) (nestedParameter B S v t) ρ) =
      T.leviRealPowerTwist (B.flatten R) (restrictParameter B R t)
        (transport (B.flatten S) (B.flatten R) h hc
          (T.leviRealPowerTwist (B.flatten S) (-v) ρ)) := by
  have hp : nestedParameter B S v t = restrictParameter B S t + (-v) := by
    ext k
    exact add_comm _ _
  rw [hp, T.leviRealPowerTwist_add,
    T.transport_restrictedLeviRealPowerTwist B S R h hh hc]

end PadicField.TopologicalData

end Langlands
