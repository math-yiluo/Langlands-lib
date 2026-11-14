import Langlands.Representation.Filtration.QuasicuspidalVanishingProof
import Langlands.AllField.Representation.Filtration.VanishingStatement
import Langlands.AllField.Representation.Induction.BlockFactors
/-! Absence of quasicuspidal subquotients propagates through finite filtrations. -/

open CategoryTheory

namespace Langlands.AllField

universe uR uG uV uF uW

namespace SmoothRep
open Langlands.SmoothRep
open Langlands.AllField.SmoothRep


end SmoothRep

namespace CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement padicLeviFiltrationNoQuasicuspidalSubquotients
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.Geometric

end CuspidalSupport

namespace ObjectRepFiltration
open Langlands.ObjectRepFiltration
open Langlands.AllField.ObjectRepFiltration


end ObjectRepFiltration

namespace CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement padicLeviFiltrationNoQuasicuspidalSubquotients
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

/-- Proof of `PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement`. -/
theorem padicLeviFiltrationNoQuasicuspidalSubquotients :
    PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement.{uV, uF} := by
  intro F _ T
  let _ := T.topology
  intro n B A r s hs D hD hDq
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hD
  have key : ∀ k : Fin (r + 1), ∀ x : D, x ∈ ObjectRepFiltration.imageStep s i q k := by
    intro k
    induction k using Fin.reverseInduction with
    | last =>
      intro x
      obtain ⟨v, rfl⟩ := hq x
      refine ⟨v, ?_, rfl⟩
      change SmoothRep.hom i v ∈ s.subrepresentation (Fin.last r)
      rw [s.subrepresentation_last]
      trivial
    | cast j ih =>
      obtain ⟨Q, ⟨e⟩, hQ⟩ := hs j
      have hY := hQ _ (ObjectRepFiltration.isSubquotient_quotient_imageStep s i q j ih Q e)
        (isLeviQuasicuspidal_of_surjective B _ (SmoothRep.mkQ_surjective D _) hDq)
      intro x
      have hx : SmoothRep.hom (SmoothRep.mkQ D (ObjectRepFiltration.imageStep s i q j.castSucc))
          x = 0 := Subsingleton.elim _ _
      exact (Submodule.Quotient.mk_eq_zero _).mp hx
  refine ⟨fun x y => ?_⟩
  have hzero : ∀ x : D, x = 0 := fun x => by
    obtain ⟨v, hv, rfl⟩ := key 0 x
    have hv' : SmoothRep.hom i v ∈ s.subrepresentation 0 := hv
    rw [s.subrepresentation_zero] at hv'
    have hv0 : SmoothRep.hom i v = 0 := (Submodule.mem_bot ℂ).mp hv'
    rw [hi (hv0.trans (map_zero _).symm), map_zero]
  rw [hzero x, hzero y]

end CuspidalSupport

end Langlands.AllField
