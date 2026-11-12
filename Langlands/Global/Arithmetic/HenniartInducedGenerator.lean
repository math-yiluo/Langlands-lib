import Langlands.Global.Arithmetic.HenniartWitnessedGenerator
import Langlands.Automorphic.InducedReciprocityLocalClass
import Langlands.Automorphic.InducedReciprocityIrreducible
import Langlands.Automorphic.InducedReciprocityUnitary
import Langlands.VirtualRepresentation.ExactInductionTwist

/-!
# Witnessed generators from Harris's automorphic induction

For a tower `F ⊆ E' ⊆ L` of number fields with `L / F` Galois, `F` totally complex and
`E'` a CM field, an `E'/F`-regular Hecke character `ξ = ξ⁻¹ ∘ c` of `E'` that has a weak
automorphic induction gives, at a finite place `v` of `F` with one place `u` of `E'` above
it, witnessed generators whose Weil element is the induction of the Weil character of
`ξ_u`, twisted by any unramified modulus-one character of `W_{F_v}`.
-/

noncomputable section

set_option autoImplicit false

universe uG uH uV uW uP

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} {H : Type uH} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H]

/-- The projection formula for induction along an open embedding. -/
theorem continuousTwist_continuousInduceAlong (φ : H →ₜ* G)
    (hφ : Topology.IsOpenEmbedding φ) [φ.toMonoidHom.range.FiniteIndex] (η : G →ₜ* ℂˣ)
    (x : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uH, uV} ℂ H => A.IsContinuous)) :
    continuousTwist η (continuousInduceAlong φ hφ x) =
      continuousInduceAlong φ hφ (continuousTwist (η.comp φ) x) := by
  simp only [continuousInduceAlong, LinearMap.comp_apply]
  rw [continuousRestrict_continuousTwist, ← continuousInduce_continuousTwist]
  have hη : (η.comp φ).comp ⟨InductionAlong.rangeInverse φ.toMonoidHom hφ.injective,
      InductionAlong.continuous_rangeInverse φ.toMonoidHom hφ.isEmbedding⟩ =
      η.comp ⟨φ.toMonoidHom.range.subtype, continuous_subtype_val⟩ := by
    ext s
    change (η (φ (InductionAlong.rangeInverse φ.toMonoidHom hφ.injective s)) : ℂ) = η s.1
    rw [show φ (InductionAlong.rangeInverse φ.toMonoidHom hφ.injective s) = s.1 from
      InductionAlong.apply_rangeInverse φ.toMonoidHom hφ.injective s]
  rw [hη]

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.VirtualRepresentation.RelativeGlobal

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality Langlands.Automorphic

/-- Harris's weak automorphic induction of an `E'/F`-regular conjugate-inverse Hecke
character `ξ` gives, at a place `v` with a single place `u` of `E'` above it, witnessed
generators whose Weil element realizes `z ⊗ Ind_{W_{E'_u}}^{W_{F_v}} (ξ_u ∘ rec_u)` for every
unramified modulus-one character `z` of `W_{F_v}`. -/
theorem exists_witnessedGenerator_inducedReciprocity
    (hlrm : LocalRelativeWeilMapExistenceStatement.{0})
    (hlir : RelativeWeilGroup.LocalInducedRestrictionStatement.{uW, 0})
    (hcalip : CuspidalAllLocalIrreduciblePresentationExistenceStatement.{0, uP})
    (hacc : RelativeWeilGroup.AssociatedCentralCharacterStatement.{0, uW, uP})
    (hasi : RelativeWeilGroup.AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP})
    (htransfer : RelativeWeilGroup.LocalTransferReciprocityStatement.{0})
    {c : FundamentalClass.ClassFamily.{0}} (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    {F E' L : Type} [Field F] [NumberField F] [Field E'] [NumberField E'] [Field L]
    [NumberField L] [Algebra F E'] [Algebra F L] [Algebra E' L] [IsScalarTower F E' L]
    [IsGalois F L] [NumberField.IsTotallyComplex F] [NumberField.IsCMField E']
    [CompactSpace (AdeleQuotient F)]
    (ξ : HeckeCharacter E') (hreg : Harris.IsRelativelyRegular F ξ)
    (hconj : Harris.IsConjugateInverse ξ) {r : ℕ}
    (π : CuspidalOperatorRealization.IsoClass F r)
    (hπ : π.IsWeakAutomorphicInductionOf.{0, 0, uP} ξ)
    (v : FinitePlace F) (u : FinitePlace E') [u.asIdeal.LiesOver v.asIdeal]
    [Subsingleton (FinitePlacesAbove E' v)]
    (eu : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v u))
    (heu : LocalClassField.GeometricWeilReciprocityRelation (towerPadicField v u)
      (towerPadicField v u).canonicalTopologicalData eu)
    (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) :
    ∃ d : WitnessedGenerator.{0, uW, uP} F L c v,
      LocalWeil.realizeExact (padicField v)
          (LocalWeil.includeUnitary (padicField v) d.weilElement) =
        ExactGrothendieckGroup.continuousTwist
          (Weil.Local.localUnramifiedCharacter (padicField v) z)
          (ExactGrothendieckGroup.continuousInduceAlong (RelativeWeilGroup.completionWeilMap v u)
            (Weil.Local.extensionWeilMap_isOpenEmbedding _ _ _)
            (ExactGrothendieckGroup.characterClass.{0, uW}
              (LocalFactor.RankOne.weilCharacter (towerPadicField v u) eu
                (quasicharacterAt u (residuePrime_eq v u) (ξ.finiteComponent u))))) := by
  obtain ⟨I, hI, hrest⟩ := hc
  have h : FundamentalClass.Restriction c := hrest.2.1
  have hwia := RelativeWeilGroup.weakInductionAssociation_of_local.{0, uW, uP}
    LocalClassField.geometricWeilReciprocityExistenceUniqueness hlrm hlir
  have hassoc := hwia c ⟨I, hI, hrest⟩ h F E' L π ξ hπ
  have hirr := RelativeWeilGroup.inducedReciprocityRepresentation_isIrreducible.{0, uW}
    c F E' L h ξ hreg
  have hu := RelativeWeilGroup.inducedReciprocityRepresentation_isUnitary_of_isConjugateInverse.{0, uW}
    c F E' L h hconj
  let w := AdelicFunctoriality.placeAbove L v
  have : w.1.asIdeal.LiesOver v.asIdeal := w.2
  obtain ⟨rec, hrec, -⟩ := LocalClassField.geometricWeilReciprocityExistenceUniqueness _
    (towerPadicField v w.1) (towerPadicField v w.1).canonicalTopologicalData
  obtain ⟨ι, hι⟩ := hlrm I hI c hrest F L v w.1 rec hrec
  obtain ⟨hS, d, hd⟩ := exists_witnessedGenerator_realizeExact hcalip hacc hasi
    ⟨I, hI, hrest⟩ v _ hirr hu π hassoc w rec ι hι
  have h7 := RelativeWeilGroup.continuousRestrict_inducedReciprocityRepresentation_class hlir h ξ
    w.1 rec ι hι u eu heu
  have hloc := hd.trans ((ExactGrothendieckGroup.restrict_ofRepresentation _ _ _ _ _).symm.trans h7)
  obtain ⟨d', hd'⟩ := exists_witnessedGenerator_unramifiedTwist htransfer ⟨I, hI, hrest⟩ d z hz
  exact ⟨d', hd'.trans (congrArg _ hloc)⟩

end Langlands.VirtualRepresentation.RelativeGlobal
