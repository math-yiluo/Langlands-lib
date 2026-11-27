import Langlands.BushnellKutzko.TypeContainment
import Langlands.Correspondence.SupercuspidalRelations

/-! # Containment of a pair `(J, λ)` in a supercuspidal class of `GL_{k+1}` over a p-adic field

BK93, §6.2, printed p. 202: an irreducible representation `π` contains `(J, λ)` when `π | J`
contains `λ`. For a class of the Library's supercuspidal class space this is asked of a
representative.
-/

noncomputable section

namespace Langlands.BushnellKutzko

universe uK uV uρ

section Instances

/-! The canonical topology of the p-adic field, under a name specific to this module. The
topology of `GL_{k+1}(K)` is then the one inferred from it, as in the class space
`Correspondence.SupercuspidalAutomorphicClass`. -/

local instance supercuspidalClassContainmentTopology {p : ℕ} [Fact p.Prime]
    (K : PadicField p) : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- **Containment for classes.** The class `π` of irreducible supercuspidal representations of
`GL_{k+1}(K)` contains the pair `(J, λ)`, `J` a subgroup of `GL_{k+1}(K)` and `λ` a smooth
complex representation of `J`, when some representative `A` of `π` contains `(J, λ)`: there is
a nonzero `J`-homomorphism from `λ` to the restriction of `A` to `J` (`ContainsType`). -/
def SupercuspidalClassContainsType {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {k : ℕ}
    (π : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat)
    {J : Subgroup (GeneralLinear (k + 1) K.Carrier)} (ρ : SmoothRep.{0, uK, uρ} ℂ J) : Prop :=
  ∃ A : GeneralLinear.SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := k + 1),
    A.isoClass = π ∧ ContainsType A.obj ρ

end Instances

end Langlands.BushnellKutzko
