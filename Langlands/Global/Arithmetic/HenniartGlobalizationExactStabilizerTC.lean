import Langlands.Global.Arithmetic.HenniartGlobalizationReduction
import Langlands.Global.Arithmetic.HenniartHarrisDatumExactStabilizerStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerStatement
import Langlands.Automorphic.AssociatedFactorTCStatement

/-!
# Henniart's relative globalization over a totally complex base

Retain the totally complex property of the common CM base field in the relative globalization.
The induction steps use Harris's exact-stabilizer proposition and Henniart's Théorème 2.4
for totally complex base fields.
-/

noncomputable section

set_option autoImplicit false

universe uK uQ uW uP

namespace Langlands.VirtualRepresentation.RelativeGlobal

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global
open Langlands.Global.AdelicFunctoriality Langlands.Automorphic

section WitnessedGenerator

variable {F E : Type} [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  {c : FundamentalClass.ClassFamily.{0}}

/-- An irreducible unitary representation `S` of `W_{E/F}`, weakly associated with a
cuspidal class, gives a witnessed generator at `v` whose Weil element expands the
restriction of `S` along the local map `ι`. The inputs are the existence of presentations
irreducible at every finite place, the central-character comparison and Henniart's
Théorème 2.4. -/
private theorem exists_witnessedGenerator_realizeExactTC
    (hcalip : CuspidalAllLocalIrreduciblePresentationExistenceStatement.{0, uP})
    (hacc : RelativeWeilGroup.AssociatedCentralCharacterStatement.{0, uW, uP})
    (hasi : RelativeWeilGroup.AssociatedSupercuspidalInductionTCStatement.{0, uW, uP, uP})
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c) (v : FinitePlace F)
    (S : FiniteRepresentation.{0, 0, uW} ℂ (RelativeWeilGroup c F E))
    (hirr : S.IsIrreducible) (hu : S.IsUnitary) {r : ℕ}
    (π : CuspidalOperatorRealization.IsoClass F r)
    (hπ : RelativeWeilGroup.IsWeaklyAssociatedClass.{0, uW, uP} S π)
    (w : FinitePlacesAbove E v)
    (rec : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hι : RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 rec ι) :
    ∃ (hS : S.IsContinuous) (d : WitnessedGenerator.{0, uW, uP} F E c v),
      LocalWeil.realizeExact (padicField v)
          (LocalWeil.includeUnitary (padicField v) d.weilElement) =
        localExactClass F E c v S hS ι := by
  obtain ⟨T, rfl⟩ := π.exists_representative
  obtain ⟨P₀, -⟩ := (RelativeWeilGroup.isWeaklyAssociatedClass_isoClass_iff S T).mp hπ
  obtain ⟨Q, hQ⟩ := hcalip F r T P₀
  have hassoc := isWeaklyAssociated_of_isWeaklyAssociatedClass S T hπ Q.universeLift.{uP}
  have hlirr :=
    (CuspidalSpectralPresentation.universeLift_localComponent_isIrreducible_iff.{uP} Q v).mpr
      (hQ v).1
  have hladm :=
    (CuspidalSpectralPresentation.universeLift_localComponent_isAdmissible_iff.{uP} Q v).mpr
      (hQ v).2
  have hcent := RelativeWeilGroup.hasUnitaryCentralCharacter_of_associatedCentralCharacter
    F E c hacc hc S T hπ hu
  obtain ⟨B, σ, hσ, ⟨e⟩⟩ := hasi c hc F E S T hirr hu hcent hπ _ v hlirr hladm
  exact ⟨hassoc.1, WitnessedGenerator.ofUnitaryInduction F E c v S hirr hu T _ hassoc w rec ι
    hι hlirr hladm B σ hσ e, localUnitaryExpansion_spec F E c v S hassoc.1 hu ι⟩

end WitnessedGenerator

/-- Harris's weak automorphic induction of an `E'/F`-regular conjugate-inverse Hecke
character `ξ` gives, at a place `v` with a single place `u` of `E'` above it, witnessed
generators whose Weil element realizes `z ⊗ Ind_{W_{E'_u}}^{W_{F_v}} (ξ_u ∘ rec_u)` for every
unramified modulus-one character `z` of `W_{F_v}`. -/
private theorem exists_witnessedGenerator_inducedReciprocityTC
    (hlrm : LocalRelativeWeilMapExistenceStatement.{0})
    (hlir : RelativeWeilGroup.LocalInducedRestrictionStatement.{uW, 0})
    (hcalip : CuspidalAllLocalIrreduciblePresentationExistenceStatement.{0, uP})
    (hacc : RelativeWeilGroup.AssociatedCentralCharacterStatement.{0, uW, uP})
    (hasi : RelativeWeilGroup.AssociatedSupercuspidalInductionTCStatement.{0, uW, uP, uP})
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
  have hu :=
    RelativeWeilGroup.inducedReciprocityRepresentation_isUnitary_of_isConjugateInverse.{0, uW}
      c F E' L h hconj
  let w := AdelicFunctoriality.placeAbove L v
  have : w.1.asIdeal.LiesOver v.asIdeal := w.2
  obtain ⟨rec, hrec, -⟩ := LocalClassField.geometricWeilReciprocityExistenceUniqueness _
    (towerPadicField v w.1) (towerPadicField v w.1).canonicalTopologicalData
  obtain ⟨ι, hι⟩ := hlrm I hI c hrest F L v w.1 rec hrec
  obtain ⟨hS, d, hd⟩ := exists_witnessedGenerator_realizeExactTC hcalip hacc hasi
    ⟨I, hI, hrest⟩ v _ hirr hu π hassoc w rec ι hι
  have h7 := RelativeWeilGroup.continuousRestrict_inducedReciprocityRepresentation_class hlir h ξ
    w.1 rec ι hι u eu heu
  have hloc := hd.trans ((ExactGrothendieckGroup.restrict_ofRepresentation _ _ _ _ _).symm.trans h7)
  obtain ⟨d', hd'⟩ := exists_witnessedGenerator_unramifiedTwist htransfer ⟨I, hI, hrest⟩ d z hz
  exact ⟨d', hd'.trans (congrArg _ hloc)⟩

end Langlands.VirtualRepresentation.RelativeGlobal

namespace Langlands.Global

open NumberField Langlands.Weil.Local Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open Langlands.LocalFactor.CommonClosure Langlands.VirtualRepresentation
open Langlands.VirtualRepresentation.RelativeGlobal Langlands.Automorphic
open GeneralPosition
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

/-- The relative globalization with a totally complex witness for its base field `F`. -/
def RelativeGaloisGlobalizationTC : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{0}, RelativeWeilGroup.IsArithmeticClassFamily c →
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) {Q : Type uQ} [Group Q] [Finite Q]
    (q : Field.absoluteGaloisGroup K.Carrier →* Q),
    ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : IsTotallyComplex F)
      (_ : Field E) (_ : NumberField E)
      (_ : Algebra F E) (_ : IsGalois F E)
      (v : FinitePlace F) (h : residuePrime v = p)
      (f : letI := (padicFieldAt v h).algebra
        K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier),
      ∀ [CompactSpace (AdeleQuotient F)],
      ∀ x ∈ LocalWeil.unitaryFiniteFactoringSupported.{uK, uW} K q,
        ∃ y ∈ weilImage.{0, uW, uP} F E c v,
          ExactGrothendieckGroup.continuousRestrict (completionWeilTransport v h K f)
              (LocalWeil.realizeExact (padicField v)
                (LocalWeil.includeUnitary (padicField v) y)) =
            LocalWeil.realizeExact K (LocalWeil.includeUnitary K x)

/-- Henniart (2000), §3.4, for one generator: on a paired-place configuration for `F'`
whose place `P.v` carries `f : K ≅ F₀_{P.v}`, the induction to `W_{F₀_{P.v}}` of a modulus-one
character of `W_L`, with `W_L` the transport of `W_{F'}`, is the realization of an element
of the Weil image of witnessed pairs at `P.v`. -/
private theorem exists_weilImage_realizeExact_continuousInduceTC
    (hRealize : HarrisDatumCharacterRealizationExactStabilizerStatement.{uK, 0, 0, 0})
    (hHarris : Harris.Proposition48ExactStabilizerStatement.{uK, 0, 0, 0, uP})
    (hccre : LocalClassField.CommonClosureReciprocityExistence.{uK})
    (hlrm : LocalRelativeWeilMapExistenceStatement.{0})
    (hlir : LocalInducedRestrictionStatement.{uW, 0})
    (hcalip : CuspidalAllLocalIrreduciblePresentationExistenceStatement.{0, uP})
    (hacc : AssociatedCentralCharacterStatement.{0, uW, uP})
    (hasi : AssociatedSupercuspidalInductionTCStatement.{0, uW, uP, uP})
    (htransfer : LocalTransferReciprocityStatement.{0})
    {c : FundamentalClass.ClassFamily.{0}} (hc : IsArithmeticClassFamily c)
    {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    {F₀ : Type} [Field F₀] [NumberField F₀] [IsCMField F₀] [CompactSpace (AdeleQuotient F₀)]
    (F' : Extension K) {E' Lg : Type} [Field E'] [Field Lg] [NumberField E'] [NumberField Lg]
    [IsCMField E'] [IsCMField Lg] [Algebra F₀ E'] [Algebra F₀ Lg] [Algebra E' Lg]
    (K₀ : IntermediateField ℚ F₀) (P Ps : Harris.PlaceDatum K F' F₀ E' Lg)
    (φ : FiniteCompletion E' P.v' ≃+* F'.field) (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
    (θ : (Lg ≃ₐ[F₀] Lg) ≃*
      ((galoisClosure K F').field ≃ₐ[K.Carrier] (galoisClosure K F').field))
    (hconf : Harris.IsPairedPlaceConfiguration K₀ P Ps φ φs θ)
    (h : residuePrime P.v = p)
    (f : letI := (padicFieldAt P.v h).algebra
      K.Carrier ≃ₐ[Padic p] (padicFieldAt P.v h).Carrier)
    (hf : letI := (padicFieldAt P.v h).algebra
      ∀ x : FiniteCompletion F₀ P.v, f.symm x = P.iso x)
    {𝔼 : Type} [Field 𝔼] [NumberField 𝔼] [Algebra F₀ 𝔼] [Algebra E' 𝔼]
    [IsScalarTower F₀ E' 𝔼] [IsGalois F₀ 𝔼]
    (L : Extension (padicField P.v))
    (hL : ∀ y : localWeilGroup K,
      completionWeilTransport P.v h K f y ∈ weilSubgroup (padicField P.v) L ↔
        y ∈ weilSubgroup K F')
    (η : weilSubgroup (padicField P.v) L →ₜ* ℂˣ) (hη : ∀ a, ‖(η a : ℂ)‖ = 1) :
    ∃ y ∈ weilImage.{0, uW, uP} F₀ 𝔼 c P.v,
      haveI := weilSubgroup_finiteIndex (padicField P.v) L
      LocalWeil.realizeExact (padicField P.v) (LocalWeil.includeUnitary (padicField P.v) y) =
        ExactGrothendieckGroup.continuousInduce (weilSubgroup (padicField P.v) L)
          (weilSubgroup_open _ L) (ExactGrothendieckGroup.characterClass.{0, uW} η) := by
  have hconf' := hconf
  obtain ⟨hST, -, -, -, -, -, -, -, -, hplaces, -, -, hφsc, -, -, hφP, hφT, -, -⟩ := hconf'
  have : IsScalarTower F₀ E' Lg := hST
  have : Subsingleton (AdelicFunctoriality.FinitePlacesAbove E' P.v) :=
    Harris.finitePlacesAbove_subsingleton (L := Lg) P.v
      (hplaces P.v (List.mem_cons_self ..)).2
  -- The image of `W_{E'_{P.v'}}` is conjugate to `W_L`.
  have hφ' : letI := (padicFieldAt P.v h).algebra
      ∀ x : P.v.adicCompletion F₀,
        φ (algebraMap (P.v.adicCompletion F₀) (P.v'.adicCompletion E') x) =
          algebraMap K.Carrier F'.field (f.symm x) := by
    intro x
    rw [hf x]
    exact hφP x
  obtain ⟨g, hg⟩ := exists_conj_completionWeilMap_range P.v P.v' h K f F' φ hφ' L hL
  have := weilSubgroup_finiteIndex (padicField P.v) L
  have hY := ExactGrothendieckGroup.continuousInduce_characterClass_eq_along_conj.{0, 0, uW}
    (completionWeilMap P.v P.v') (extensionWeilMap_isOpenEmbedding _ _ _)
    (weilSubgroup (padicField P.v) L) (weilSubgroup_open _ L) g hg η
  set η' := η.comp (ExactGrothendieckGroup.conjCodRestrict (completionWeilMap P.v P.v')
    (weilSubgroup (padicField P.v) L) g hg) with hη'def
  have hη' : ∀ w, ‖(η' w : ℂ)‖ = 1 := fun w => hη _
  -- The character `χ₀` of `F'ˣ` transported from the field character of `η'`.
  obtain ⟨eu, heu, -⟩ := LocalClassField.geometricWeilReciprocityExistenceUniqueness _
    (towerPadicField P.v P.v') (towerPadicField P.v P.v').canonicalTopologicalData
  let θu := LocalFactor.RankOne.fieldCharacter (towerPadicField P.v P.v') eu η'
  let θc : (P.v'.adicCompletion E')ˣ →ₜ* ℂˣ :=
    LocalFactor.PadicAbelian.quasicharacterCongr
      (padicFieldAt_topology_eq P.v' (residuePrime_eq P.v P.v')).symm θu
  let χ₀ : FieldCharacter K F' :=
    letI := (fieldData K F').topology
    θc.comp ⟨Units.map φ.symm.toRingHom.toMonoidHom,
      Units.continuous_iff.mpr ⟨hφsc.comp Units.continuous_val,
        hφsc.comp Units.continuous_coe_inv⟩⟩
  obtain ⟨e, he⟩ := hccre p K K.canonicalTopologicalData
  obtain ⟨χ, χs, ξ, hdatum, hunits⟩ :=
    hRealize K F' F₀ E' Lg K₀ P Ps φ φs θ hconf e he χ₀
  obtain ⟨r, π, hπ, -, -, -⟩ := hHarris K F' F₀ E' Lg e χ χs K₀ P Ps ξ he hdatum
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hreg, hconj, hcomp, -⟩ := hdatum
  -- The component of `ξ` at `P.v'` agrees with the field character of `η'` on units.
  have hξu : ξ.IsUnitary := HeckeConjugateInverse.isUnitary_of_isConjugateInverse ξ hconj
  have hψ : ∀ a, ‖(ξ.finiteComponent P.v' a : ℂ)‖ = 1 := fun a => hξu _
  have hunr : ∀ a : (P.v'.adicCompletion E')ˣ, Valued.v (a : P.v'.adicCompletion E') = 1 →
      ξ.finiteComponent P.v' a =
        LocalFactor.RankOne.fieldCharacter (towerPadicField P.v P.v') eu η' a := by
    intro a ha
    rw [hcomp a (Units.map φ.toRingHom.toMonoidHom a) (hφT a),
      hunits (Units.map φ.toRingHom.toMonoidHom a)
        (discreteValuation_eq_one_of_valued_eq_one F' P.v' φ hφsc ha)]
    change θu (Units.map φ.symm.toRingHom.toMonoidHom
      (Units.map φ.toRingHom.toMonoidHom a)) = θu a
    congr 1
    ext
    simp
  obtain ⟨z, hz, hwc⟩ := exists_weilCharacter_eq_mul_unramified P.v P.v' eu heu η' hη'
    (ξ.finiteComponent P.v') hψ hunr
  -- The witnessed generator, twisted by the inverse unramified character.
  obtain ⟨d, hd⟩ := exists_witnessedGenerator_inducedReciprocityTC (L := 𝔼) hlrm hlir
    hcalip hacc hasi htransfer hc ξ hreg hconj π hπ P.v P.v' eu heu z⁻¹ (by simpa using hz)
  refine ⟨d.weilElement, witnessed_weil_mem d, ?_⟩
  have hlu : (localUnramifiedCharacter (padicField P.v) z⁻¹).comp
      (completionWeilMap P.v P.v') *
        (η' * (localUnramifiedCharacter (padicField P.v) z).comp (completionWeilMap P.v P.v')) =
      η' := by
    ext w
    change ((z⁻¹ ^ (localDegree (padicField P.v) (completionWeilMap P.v P.v' w)).toAdd *
      (η' w * z ^ (localDegree (padicField P.v) (completionWeilMap P.v P.v' w)).toAdd) :
        ℂˣ) : ℂ) = (η' w : ℂ)
    rw [inv_zpow, ← mul_assoc, mul_comm _ (η' w), mul_assoc, inv_mul_cancel, mul_one]
  rw [hd, hwc, ExactGrothendieckGroup.continuousTwist_continuousInduceAlong,
    ExactGrothendieckGroup.continuousTwist_characterClass, hlu, hY]

/-- One Brauer generator at the common place `v₀`: if a paired-place configuration for `F'`
has place `v₀` and its isomorphism `F₀_{v₀} ≅ K` agrees with `ι₀` on `F₀`, then for every
extension `L` of `F₀_{v₀}` whose Weil group corresponds to `W_{F'}` and every modulus-one
character `η` of `W_L`, the induction `Ind_{W_L} η` is the realization of an element of the
Weil image of witnessed pairs at `v₀`. -/
private theorem exists_weilImage_realizeExact_generatorTC
    (hRealize : HarrisDatumCharacterRealizationExactStabilizerStatement.{uK, 0, 0, 0})
    (hHarris : Harris.Proposition48ExactStabilizerStatement.{uK, 0, 0, 0, uP})
    (hccre : LocalClassField.CommonClosureReciprocityExistence.{uK})
    (hlir : LocalInducedRestrictionStatement.{uW, 0})
    (hacc : AssociatedCentralCharacterStatement.{0, uW, uP})
    (hasi : AssociatedSupercuspidalInductionTCStatement.{0, uW, uP, uP})
    (htransfer : LocalTransferReciprocityStatement.{0})
    {c : FundamentalClass.ClassFamily.{0}} (hc : IsArithmeticClassFamily c)
    {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    {F₀ : Type} [Field F₀] [NumberField F₀] [IsCMField F₀] [CompactSpace (AdeleQuotient F₀)]
    (v₀ : FinitePlace F₀) (ι₀ : FiniteCompletion F₀ v₀ ≃+* K.Carrier)
    (hι₀ : letI := K.canonicalTopology; Continuous ι₀)
    (hι₀s : letI := K.canonicalTopology; Continuous ι₀.symm)
    (h : residuePrime v₀ = p)
    (F' : Extension K) {E' Lg : Type} [Field E'] [Field Lg] [NumberField E'] [NumberField Lg]
    [IsCMField E'] [IsCMField Lg] [Algebra F₀ E'] [Algebra F₀ Lg] [Algebra E' Lg]
    (K₀ : IntermediateField ℚ F₀) (P Ps : Harris.PlaceDatum K F' F₀ E' Lg)
    (φ : FiniteCompletion E' P.v' ≃+* F'.field) (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
    (θ : (Lg ≃ₐ[F₀] Lg) ≃*
      ((galoisClosure K F').field ≃ₐ[K.Carrier] (galoisClosure K F').field))
    (hconf : Harris.IsPairedPlaceConfiguration K₀ P Ps φ φs θ) (hPv : P.v = v₀)
    (hPiso : ∀ x : F₀, P.iso (algebraMap F₀ (FiniteCompletion F₀ P.v) x) =
      ι₀ (algebraMap F₀ (FiniteCompletion F₀ v₀) x))
    {𝔼 : Type} [Field 𝔼] [NumberField 𝔼] [Algebra F₀ 𝔼] [Algebra E' 𝔼]
    [IsScalarTower F₀ E' 𝔼] [IsGalois F₀ 𝔼]
    (L : Extension (padicField v₀))
    (hL : ∀ y : localWeilGroup K,
      completionWeilTransport v₀ h K (completionAlgEquivOfContinuous v₀ K h ι₀ hι₀s) y ∈
          weilSubgroup (padicField v₀) L ↔
        y ∈ weilSubgroup K F')
    (η : weilSubgroup (padicField v₀) L →ₜ* ℂˣ) (hη : ∀ a, ‖(η a : ℂ)‖ = 1) :
    ∃ y ∈ weilImage.{0, uW, uP} F₀ 𝔼 c v₀,
      haveI := weilSubgroup_finiteIndex (padicField v₀) L
      LocalWeil.realizeExact (padicField v₀) (LocalWeil.includeUnitary (padicField v₀) y) =
        ExactGrothendieckGroup.continuousInduce (weilSubgroup (padicField v₀) L)
          (weilSubgroup_open _ L) (ExactGrothendieckGroup.characterClass.{0, uW} η) := by
  subst hPv
  have hcont : letI := K.canonicalTopology; Continuous P.iso := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hQ, -⟩ := hconf
    exact (hQ P (List.mem_cons_self ..)).2.1
  have hext := completion_ringHom_ext P.v K ι₀.toRingHom P.iso.toRingHom hι₀ hcont
    (fun x => (hPiso x).symm)
  have hf : letI := (padicFieldAt P.v h).algebra
      ∀ x : FiniteCompletion F₀ P.v,
        (completionAlgEquivOfContinuous P.v K h ι₀ hι₀s).symm x = P.iso x := by
    intro x
    rw [completionAlgEquivOfContinuous_symm_apply]
    exact congrArg (fun g : FiniteCompletion F₀ P.v →+* K.Carrier => g x) hext
  exact exists_weilImage_realizeExact_continuousInduceTC hRealize hHarris hccre
    localRelativeWeilMapExistence hlir cuspidalAllLocalIrreduciblePresentationExistence hacc
    hasi htransfer hc K F' K₀ P Ps φ φs θ hconf h _ hf L hL η hη

/-- The common CM base in Henniart's globalization is totally complex. The proof uses
the exact-stabilizer character realization and Harris proposition, and requires
Théorème 2.4 only over totally complex fields. -/
theorem henniartGlobalizationExactStabilizerTC_of_inputs
    (hRealize : HarrisDatumCharacterRealizationExactStabilizerStatement.{uK, 0, 0, 0})
    (hccre : LocalClassField.CommonClosureReciprocityExistence.{uK})
    (hlir : LocalInducedRestrictionStatement.{uW, 0})
    (hacc : AssociatedCentralCharacterStatement.{0, uW, uP})
    (hasi : AssociatedSupercuspidalInductionTCStatement.{0, uW, uP, uP})
    (htransfer : LocalTransferReciprocityStatement.{0}) :
    Harris.Proposition48ExactStabilizerStatement.{uK, 0, 0, 0, uP} →
      RelativeGaloisGlobalizationTC.{uK, uQ, uW, uP} := by
  intro hHarris c hc p _ K Q _ _ q
  have : CharZero K.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) K.Carrier).injective
  have : IsGalois K.Carrier (AlgebraicClosure K.Carrier) := ⟨⟩
  -- Choose the fixed field of an open normal Galois subgroup whose preimage in the
  -- Weil group lies in the closure of the kernel of the map induced by `q`.
  obtain ⟨U, hUn, hUo, hUN⟩ := exists_open_normal_le K (factoringKernelClosure K q)
    (factoringKernelClosure_isOpen K q)
  have := hUn
  let Uc : ClosedSubgroup (Field.absoluteGaloisGroup K.Carrier) :=
    ⟨U, U.isClosed_of_isOpen hUo⟩
  have hM : (IntermediateField.fixedField U).fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField Uc
  have : FiniteDimensional K.Carrier (IntermediateField.fixedField U) :=
    (InfiniteGalois.isOpen_iff_finite _).mp (by rw [hM]; exact hUo)
  let M : Extension K := ⟨IntermediateField.fixedField U, inferInstance⟩
  -- The common CM base `F₀`, its place `v₀`, `ι₀ : F₀_{v₀} ≅ K`, and a paired-place
  -- configuration of every subextension `F'` of `M`.
  obtain ⟨F₀, _, _, _, v₀, ι₀, hι₀, hι₀s, hconfs⟩ := henniartCommonBaseRealization p K M
  choose E' Lg iE' iLg nE' nLg cE' cLg aE' aLg aE'Lg K₀ P Ps φ φs θ hconf hPv hPiso
    using hconfs
  have h : residuePrime v₀ = p := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hplaces, -⟩ := hconf M le_rfl
    have hmem := (hplaces (P M le_rfl).v (List.mem_cons_self ..)).1
    rw [hPv M le_rfl] at hmem
    exact residuePrime_eq_of_natCast_mem v₀ hmem
  subst h
  let f := completionAlgEquivOfContinuous v₀ K rfl ι₀ hι₀s
  -- A Galois extension `𝔼` of `F₀` containing every `E'`.
  have : Finite {F' : Extension K // F'.field ≤ M.field} := finite_extension_le K M
  let 𝔼 := familyGaloisOverfield F₀
    (fun i : {F' : Extension K // F'.field ≤ M.field} => E' i.1 i.2)
  refine ⟨F₀, 𝔼.carrier, inferInstance, inferInstance, IsCMField.isTotallyComplex F₀,
    inferInstance, inferInstance, inferInstance, inferInstance, v₀, rfl, f, ?_⟩
  intro _ x hx
  let T := completionWeilTransportEquiv v₀ rfl K f
  -- Transport the Brauer span along `T`.
  obtain ⟨z, hz, hzx⟩ :=
    realizeExact_includeUnitary_mem_map_span.{uK, 0, uW, uQ} K q (padicField v₀) T x hx
  have hspan : Submodule.span ℤ (inducedCharacterClassesAbove.{0, uW} (padicField v₀)
      ((factoringKernelClosure K q).comap
        (T.symm : localWeilGroup (padicField v₀) →* localWeilGroup K))) ≤
      (weilImage.{0, uW, uP} F₀ 𝔼.carrier c v₀).map
        ((LocalWeil.realizeExact (padicField v₀)).comp
          (LocalWeil.includeUnitary (padicField v₀))) := by
    rw [Submodule.span_le]
    rintro _ ⟨L, hNL, η, hηN, rfl⟩
    -- The subextension `F'` of `M` whose Weil group corresponds to `W_L`.
    obtain ⟨F', hF'M, hF'⟩ := exists_extension_eq K U hUo
      ((weilSubgroup (padicField v₀) L).comap
        (T : localWeilGroup K →* localWeilGroup (padicField v₀)))
      (fun w hw => by
        rw [Subgroup.mem_comap]
        apply hNL
        rw [Subgroup.mem_comap]
        simpa using hUN w hw)
    have hL : ∀ y : localWeilGroup K,
        completionWeilTransport v₀ rfl K f y ∈ weilSubgroup (padicField v₀) L ↔
          y ∈ weilSubgroup K F' := by
      intro y
      rw [hF']
      exact Iff.rfl
    have hη : ∀ a, ‖(η a : ℂ)‖ = 1 :=
      norm_eq_one_of_trivial_on_finiteIndex _ η.toMonoidHom hηN
    let := 𝔼.algebraMember ⟨F', hF'M⟩
    have := 𝔼.tower ⟨F', hF'M⟩
    obtain ⟨y, hy, hyη⟩ := exists_weilImage_realizeExact_generatorTC hRealize hHarris hccre
      hlir hacc hasi htransfer hc K v₀ ι₀ hι₀ hι₀s rfl F' (K₀ F' hF'M) (P F' hF'M) (Ps F' hF'M)
      (φ F' hF'M) (φs F' hF'M) (θ F' hF'M) (hconf F' hF'M) (hPv F' hF'M) (hPiso F' hF'M)
      (𝔼 := 𝔼.carrier) L hL η hη
    exact ⟨y, hy, hyη⟩
  obtain ⟨y, hy, hyz⟩ := hspan hz
  refine ⟨y, hy, ?_⟩
  rw [← hzx, ← hyz]
  rfl

end Langlands.Global
