import Langlands.ClassField.Global.LocalRelativeWeilMapStatement
import Langlands.ClassField.Global.LocalRelativeWeilTransferStatement

/-! # Local relative Weil maps on a prime-transported completion package -/

noncomputable section

set_option autoImplicit false

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField ClassField.Global ClassField.Global.RelativeWeilGroup
open Langlands.Global.CompletionPadic
open scoped NumberField

/-- Assuming the existence of local relative Weil maps and the local transfer reciprocity
statement, a finite place `u` of `𝕃` with a place `w` of the Galois extension `K'` above it and
a geometric candidate of `K'_w` give a map `W_{𝕃_u} → W_{K'/𝕃}` on the canonical package of `𝕃_u`
over any prime equal to its residue prime. It satisfies the projection clause of a local
relative Weil map, and its transfer is the inverse of every geometric reciprocity of `𝕃_u`. -/
theorem exists_localMap_padicFieldAt
    (hM : LocalRelativeWeilMapExistenceStatement.{0})
    (hN3 : LocalTransferReciprocityStatement.{0})
    (I : ∀ (p : ℕ) [Fact p.Prime], ClassFieldTheory.Local.InvariantFamily.{0, 0} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    (c : FundamentalClass.ClassFamily.{0})
    (hc : FundamentalClass.Generates c ∧ FundamentalClass.Restriction c ∧
      FundamentalClass.Inflation c ∧ FundamentalClass.LocalCompatibility I c)
    {𝕃 K' : Type} [Field 𝕃] [NumberField 𝕃] [Field K'] [NumberField K'] [Algebra 𝕃 K']
    [IsGalois 𝕃 K'] (u : Langlands.Global.FinitePlace 𝕃) (w : Langlands.Global.FinitePlace K')
    [w.asIdeal.LiesOver u.asIdeal]
    (ew : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField u w))
    (hew : LocalClassField.GeometricWeilReciprocityRelation (towerPadicField u w)
      (towerPadicField u w).canonicalTopologicalData ew)
    {p : ℕ} [Fact p.Prime] (h : residuePrime u = p) :
    ∃ ι : Weil.Local.localWeilGroup (padicFieldAt u h) → RelativeWeilGroup c 𝕃 K',
      (∀ (g : Weil.Local.localWeilGroup (padicFieldAt u h)) (x : K'),
        completionClosureEmbedding u w
            (algebraMap K' (w.adicCompletion K') (projection c 𝕃 K' (ι g) x)) =
          AlgEquiv.toAlgHom (Weil.Local.localProjection (padicFieldAt u h) g)
            (completionClosureEmbedding u w (algebraMap K' (w.adicCompletion K') x))) ∧
      ∀ ez : LocalFactor.RankOne.ReciprocityCandidate (padicFieldAt u h),
        LocalClassField.GeometricWeilReciprocityRelation (padicFieldAt u h)
            (padicFieldAt u h).canonicalTopologicalData ez →
          ∀ y, transfer c 𝕃 K' (ι y) =
            (IdeleClassGroup.ofAdicCompletion (𝓞 𝕃) 𝕃 u
              (LocalFactor.RankOne.reciprocityUnits (padicFieldAt u h) ez y))⁻¹ := by
  subst h
  obtain ⟨ι, hι⟩ := hM I hI c hc 𝕃 K' u w ew hew
  exact ⟨ι, hι.2.1, hN3 c 𝕃 K' u w ew ι hι⟩

end Langlands.LocalFactor.NonabelianBrauer
