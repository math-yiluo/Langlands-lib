import Langlands.BaseChange.CuspidalSigmaLiftConductorRankOneOverPadicBase
import Langlands.LocalField.CharZeroPadicRealization

/-! # Rank-one sigma-lifts over characteristic-zero local fields -/

noncomputable section

namespace Langlands.BaseChange

open CharZeroLocalField LocalField
open HarmonicAnalysis (Quasicharacter)
open RankinSelberg (rankOneCharacter)

universe u v uV uW

/-- Rank-one sigma-lifts of continuous characters are norm pullbacks on the
original field and representation carriers. -/
def CharZeroRankOneSigmaLiftNormPullbackStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear 1 F) V) (hπ : IsAdmissible π)
      (P : Representation ℂ (GeneralLinear 1 E) W) (hP : IsAdmissible P)
      (A : SigmaIntertwiner σ 1 P) (c : ℂ),
      (haveI := LocalFieldTopology.generalLinear_t2Space F 1
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F 1
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F 1
       haveI := LocalFieldTopology.generalLinear_t2Space E 1
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E 1
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E 1
       IsSigmaLift σ l π hπ P hP A c) →
    ∀ (χ : Quasicharacter F) (η : Quasicharacter E),
      π.Equiv (rankOneCharacter χ.toMonoidHom) → P.Equiv (rankOneCharacter η.toMonoidHom) →
        η.toMonoidHom = χ.toMonoidHom.comp (Units.map (Algebra.norm F : E →* F))

theorem charZeroRankOneSigmaLiftNormPullback :
    CharZeroRankOneSigmaLiftNormPullbackStatement.{u, v, uV, uW} := by
  intro F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc V _ _ W _ _ π hπ P hP A c hlift χ η eπ eP
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : Algebra (Padic p) F := padicAlgebra F
  let : FiniteDimensional (Padic p) F := finiteDimensional F
  let K := padicField F
  let T := topologicalData F
  let : FiniteDimensional F E := hcyc.1
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F)
  let : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let L := PadicField.ofField (p := p) E
  let : TopologicalSpace K.Carrier := T.topology
  let : Algebra K.Carrier E := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier E := (inferInstance : IsScalarTower (Padic p) F E)
  let : FiniteDimensional K.Carrier E := hcyc.1
  let S : L.TopologicalData := suppliedPadicExtension T E
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E))
  let : Algebra K.Carrier L.Carrier := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier L.Carrier := (inferInstance : IsScalarTower (Padic p) F E)
  let : TopologicalSpace L.Carrier := S.topology
  let : IsModuleTopology K.Carrier L.Carrier := (inferInstance : IsModuleTopology F E)
  exact rankOneSigmaLiftNormPullback p K L T S σ l hcyc V W π hπ P hP A c hlift χ η eπ eP

/-- The conductor identity in rank one on the original local fields, with no
p-adic structure required as input. -/
theorem cuspidalSigmaLiftConductorRankOne :
    CuspidalSigmaLiftConductorRankOneStatement.{u, v, uV, uW} := by
  intro F _ _ _ _ _ E _ _ _ _ _ _
  let : Fact (residueChar F).Prime := ⟨residueChar_prime F⟩
  let K := padicField F
  let T := topologicalData F
  let : Algebra K.Carrier E := (inferInstance : Algebra F E)
  let : TopologicalSpace K.Carrier := T.topology
  let : IsModuleTopology K.Carrier E := (inferInstance : IsModuleTopology F E)
  exact cuspidalSigmaLiftConductorRankOneOverPadicBase (residueChar F) K T E

end Langlands.BaseChange
