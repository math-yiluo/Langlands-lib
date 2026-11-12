import Langlands.Global.Arithmetic.HenniartInducedGenerator
import Langlands.Global.Arithmetic.HenniartLocalCharacter
import Langlands.Global.Arithmetic.HenniartCompletionConjugation
import Langlands.Global.Arithmetic.HenniartHarrisDatumProof
import Langlands.Global.Arithmetic.HarrisProposition48Statement
import Langlands.Global.Arithmetic.HarrisUniquePlace
import Langlands.Global.Arithmetic.HarrisDatumLocal
import Langlands.Global.Arithmetic.HenniartGlobalizationStatement
import Langlands.Global.HeckeConjugateInverseUnitary
import Langlands.ClassFieldTheory.Local.ReciprocitySystemStatement
import Langlands.VirtualRepresentation.ExactInductionConjugation

/-!
# Induced generators above `W_{F'}` in the Weil image of witnessed pairs

Henniart (2000), §3.4, for one Brauer generator: let `K` be a p-adic field, `F'` a finite
extension of `K`, and `(E'/E, P, ...)` a paired-place configuration for `F'` whose place
`P.v` carries the isomorphism `f : K ≅ E_{P.v}`. For every finite extension `L` of `E_{P.v}`
whose Weil group corresponds to `W_{F'}`, and every modulus-one character `η` of `W_L`,
`Ind_{W_L}^{W_{E_v}} η` is the realization of an element of the Weil image of witnessed
relative pairs at `P.v`, for any Galois extension of `E` containing `E'`.
-/

noncomputable section

set_option autoImplicit false

universe uK uW uP

namespace Langlands.Global

open NumberField Langlands.Weil.Local Langlands.Global.CompletionPadic
open Langlands.ClassField.Global Langlands.ClassField.Global.RelativeWeilGroup
open Langlands.LocalFactor.CommonClosure Langlands.VirtualRepresentation
open Langlands.VirtualRepresentation.RelativeGlobal Langlands.Automorphic
open GeneralPosition
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

/-- Through a ring isomorphism `E'_u ≅ F'` with continuous inverse, elements of valuation one
go to elements of normalized valuation one. -/
theorem discreteValuation_eq_one_of_valued_eq_one {p : ℕ} [Fact p.Prime]
    {K : PadicField.{uK} p} (F' : Extension K) {E' : Type} [Field E'] [NumberField E']
    (u : FinitePlace E') (φ : u.adicCompletion E' ≃+* F'.field)
    (hφs : letI := (fieldData K F').topology; Continuous φ.symm)
    {a : u.adicCompletion E'} (ha : Valued.v a = 1) :
    (fieldData K F').discreteValuation (φ a) = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hy0 : φ a ≠ 0 := by simpa using ha0
  rw [HarrisDatum.discreteValuation_eq_one_iff, HarrisDatum.canonicalNorm_eq_one_iff hy0]
  obtain ⟨h1, h2⟩ := (HarrisDatum.valued_eq_one_iff u ha0).mp ha
  refine ⟨fun h => h1 ?_, fun h => h2 ?_⟩
  · rw [HarrisDatum.canonicalNorm_lt_one_iff_tendsto (fieldData K F')] at h
    rw [HarrisDatum.valued_lt_one_iff_tendsto u]
    have := @HarrisDatum.tendsto_pow_map _ _ _ _ (fieldData K F').topology _
      φ.symm.toRingHom hφs _ h
    simpa using this
  · rw [HarrisDatum.canonicalNorm_lt_one_iff_tendsto (fieldData K F')] at h
    rw [HarrisDatum.valued_lt_one_iff_tendsto u]
    have := @HarrisDatum.tendsto_pow_map _ _ _ _ (fieldData K F').topology _
      φ.symm.toRingHom hφs _ h
    simpa [map_inv₀] using this

/-- Henniart (2000), §3.4, for one generator: on a paired-place configuration for `F'`
whose place `P.v` carries `f : K ≅ E_{P.v}`, the induction to `W_{E_{P.v}}` of a modulus-one
character of `W_L`, with `W_L` the transport of `W_{F'}`, is the realization of an element
of the Weil image of witnessed pairs at `P.v`. -/
theorem exists_weilImage_realizeExact_continuousInduce
    (hHarris : Harris.Proposition48Statement.{uK, 0, 0, 0, uP})
    (hccre : LocalClassField.CommonClosureReciprocityExistence.{uK})
    (hlrm : LocalRelativeWeilMapExistenceStatement.{0})
    (hlir : LocalInducedRestrictionStatement.{uW, 0})
    (hcalip : CuspidalAllLocalIrreduciblePresentationExistenceStatement.{0, uP})
    (hacc : AssociatedCentralCharacterStatement.{0, uW, uP})
    (hasi : AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP})
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
    harrisDatumCharacterRealization K F' F₀ E' Lg K₀ P Ps φ φs θ hconf e he χ₀
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
  obtain ⟨d, hd⟩ := exists_witnessedGenerator_inducedReciprocity (L := 𝔼) hlrm hlir hcalip hacc
    hasi htransfer hc ξ hreg hconj π hπ P.v P.v' eu heu z⁻¹ (by simpa using hz)
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

end Langlands.Global
