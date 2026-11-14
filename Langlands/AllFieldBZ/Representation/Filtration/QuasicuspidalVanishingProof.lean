import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupport
import Langlands.AllFieldBZ.Representation.Filtration.VanishingStatement
import Langlands.Representation.Filtration.QuasicuspidalVanishingProof

/-!
# All-field port of `Langlands.Representation.Filtration.QuasicuspidalVanishingProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Filtration.QuasicuspidalVanishingProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open CategoryTheory
namespace Langlands.AllFieldBZ
universe uR uG uV uF uW

namespace SmoothRep
open Langlands.SmoothRep
variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]

end SmoothRep
namespace CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement padicLeviFiltrationNoQuasicuspidalSubquotients
open Langlands.GeneralLinear
open Langlands.Geometric
end CuspidalSupport
namespace ObjectRepFiltration
open Langlands.ObjectRepFiltration
variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]
  {M C X : SmoothRep.{uR, uG, uV} R G} {r : ℕ}

end ObjectRepFiltration
namespace CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement padicLeviFiltrationNoQuasicuspidalSubquotients
open Langlands.GeneralLinear
/-- Proof of `PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement`. -/
theorem padicLeviFiltrationNoQuasicuspidalSubquotients :
    PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement.{uV, uF} := by
  intro F T
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
end Langlands.AllFieldBZ
