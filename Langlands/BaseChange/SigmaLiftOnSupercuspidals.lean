import Langlands.BaseChange.TwistedCharacter
import Langlands.Automorphic.IsobaricLocalSupport

/-!
# σ-lift certification of a local base-change map on supercuspidal classes

For p-adic fields `L` and `M`, an embedding `ι : L → M` over `ℚ_p`, a map `Ch` sending each
supercuspidal class of `GL_{k+1}(L)` to a multiset of supercuspidal classes over `M`, and an
automorphism `σ` of `M` over `L`, the proposition `IsSigmaLiftOnSupercuspidals ι Ch σ` says:
for every supercuspidal representation `A` of `GL_{k+1}(L)` there are an irreducible
admissible representation `τ` of `GL_{k+1}(M)`, a σ-intertwiner `I` of `τ` and a constant
`c ≠ 0` such that `τ` is a σ-lift of `A` with constant `c` (Henniart–Lemaire II.2.7, through
`IsSigmaLift` with `l = orderOf σ`) and `Ch k [A]`, read as cuspidal data over `M`, is a
supercuspidal support of `τ` (Zelevinsky 1.10, through `IsSupercuspidalSupport`).

No existence of such a map and no uniqueness is asserted here.
-/

noncomputable section

namespace Langlands.BaseChange

open Langlands.Correspondence

universe uK uV

variable {p : ℕ} [Fact p.Prime]

/-- The canonical topology on the carrier of a p-adic field. -/
local instance sigmaLiftSupercuspidalTopology (F : PadicField.{uK} p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance sigmaLiftSupercuspidalValuativeRel (F : PadicField.{uK} p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance sigmaLiftSupercuspidalLocalField (F : PadicField.{uK} p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance sigmaLiftSupercuspidalFieldT2 (F : PadicField.{uK} p) : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2

local instance sigmaLiftSupercuspidalGLT2 (F : PadicField.{uK} p) (n : ℕ) :
    T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearT2Space n

local instance sigmaLiftSupercuspidalGLLocallyCompact (F : PadicField.{uK} p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n

local instance sigmaLiftSupercuspidalGLTotallyDisconnected (F : PadicField.{uK} p) (n : ℕ) :
    TotallyDisconnectedSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n

/-- `Ch` is certified by σ-lifts on supercuspidal classes: for every `k`, every supercuspidal
class `π` of `GL_{k+1}(L)` and every actual supercuspidal representative `A` of `π`, some
irreducible admissible representation `τ` of `GL_{k+1}(M)` with a σ-intertwiner `I` is a
σ-lift of `A` with a constant `c` (`IsSigmaLift σ (orderOf σ)`, Henniart–Lemaire II.2.7), and
`Ch k π`, read as cuspidal data over `M` by `supercuspidalSupportDatum`, is a supercuspidal
support of `τ`. Here `M` is an `L`-algebra through `ι`, and both fields carry their canonical
topologies. -/
def IsSigmaLiftOnSupercuspidals {L M : PadicField.{uK} p}
    (ι : L.Carrier →ₐ[Padic p] M.Carrier)
    (Ch : ∀ k : ℕ, SupercuspidalAutomorphicClass.{uK, uV} L k.succPNat →
      Multiset (Σ k' : ℕ, SupercuspidalAutomorphicClass.{uK, uV} M k'.succPNat))
    (σ : letI : Algebra L.Carrier M.Carrier := ι.toRingHom.toAlgebra
      M.Carrier ≃ₐ[L.Carrier] M.Carrier) : Prop :=
  letI : Algebra L.Carrier M.Carrier := ι.toRingHom.toAlgebra
  ∀ (k : ℕ) (π : SupercuspidalAutomorphicClass.{uK, uV} L k.succPNat)
    (A : GeneralLinear.SupercuspidalRep.{uK, uV} (F := L.Carrier) (n := k + 1)),
    A.isoClass = π →
      ∃ (τ : SmoothRep.{0, uK, max uK uV} ℂ (GeneralLinear (k + 1) M.Carrier))
        (hτ : IsAdmissible τ.representation)
        (I : SigmaIntertwiner σ (k + 1) τ.representation) (c : ℂ),
        IsSigmaLift σ (orderOf σ) A.obj.representation A.property.2.1
            τ.representation hτ I c ∧
          M.canonicalTopologicalData.IsSupercuspidalSupport τ
            ((Ch k π).map (supercuspidalSupportDatum M))

end Langlands.BaseChange
