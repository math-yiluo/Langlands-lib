import Langlands.Automorphic.AssociatedGammaOutsideStability
import Langlands.Automorphic.AssociatedGammaHeckeReduction
import Langlands.Automorphic.AssociatedGammaCommonInputs
import Langlands.Automorphic.AssociatedGammaPreservation
import Langlands.Automorphic.AssociatedGammaArithmeticGamma
import Langlands.Automorphic.AssociatedPresentationSpectrum
import Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentationProof
import Langlands.Automorphic.CuspidalContragredientExistenceProof
import Langlands.Automorphic.CuspidalDualPresentationExistenceProof
import Langlands.Automorphic.Unramified.ContragredientAssociation
import Langlands.Automorphic.PrincipalSeriesGammaMatchProof
import Langlands.Correspondence.ArithmeticPairEpsilonExistenceProof
import Langlands.Automorphic.AssociatedCentralCharacterProof
import Langlands.ClassFieldTheory.Global.LocalRelativeWeilMapExistenceProof
import Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceProof
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof
import Langlands.LocalFactor.NonabelianSystemExistsProof
import Langlands.Global.Factors.CuspidalPairPartialGammaReduction

/-!
# Assembly of the associated gamma comparison

For a cuspidal pair and weakly associated relative Weil representations, the automorphic and
arithmetic Hecke Euler families of the supporting modules satisfy all inputs of the two-twist
comparison engine. This yields a gamma certificate at every finite place and hence the pair
gamma match, assuming the global pair functional equation and the stable local comparison.
-/

noncomputable section

set_option autoImplicit false

universe u uQ uV uE uP

namespace Langlands.ClassFieldTheory.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison Langlands.Global.AdelicFunctoriality
open Langlands.Global.CuspidalPairFunctionalEquation

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- Twisting by a character trivial along the local map does not change the local class. -/
theorem localPairClass_twist_of_trivial
    (S₀ : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)) {z : FinitePlace F}
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    (χ : RelativeWeilGroup c F E →* ℂˣ) (h : ∀ g, χ (ι g) = 1) :
    localPairClass (FiniteRepresentation.twist χ S₀) ι = localPairClass S₀ ι := by
  let e : FiniteRepresentation.Equiv (localComponent (FiniteRepresentation.twist χ S₀) ι)
      (localComponent S₀ ι) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun g => by
      change Langlands.twist χ S₀.representation (ι g) = S₀.representation (ι g)
      ext x
      change ((χ (ι g) : ℂˣ) : ℂ) • S₀.representation (ι g) x = S₀.representation (ι g) x
      rw [h g, Units.val_one, one_smul])
  apply Quotient.sound
  exact ⟨WeilDeligneRepresentation.Equiv.ofIso
    ((WeilDeligneRepresentation.zeroMonodromyFunctor _).mapIso
      (FiniteRepresentation.isoOfEquiv e))⟩

/-- The reciprocity character of the trivial Hecke character is trivial. -/
theorem reciprocityCharacter_one_apply (g : RelativeWeilGroup c F E) :
    reciprocityCharacter c F E 1 g = 1 := by
  rw [reciprocityCharacter_apply]
  simp

/-- The base quasi-character of the trivial local character is trivial. -/
theorem quasicharacterBase_one (z : FinitePlace F) :
    quasicharacterBase z (1 : (FiniteCompletion F z)ˣ →ₜ* ℂˣ) = 1 := by
  rfl

/-- **Gamma certificate from the two setups.** -/
theorem hasHeckeGammaCertificate_setups
    (hFE : CuspidalPairGlobalFunctionalEquationStatement.{u, uQ})
    (hL1 : StableTwistPairGammaMatchStatement.{u, uV, uE})
    (hPS : PrincipalSeriesPairGammaMatchStatement.{u, uV, uE})
    (hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE})
    (hGen : Automorphic.CuspidalLocalGenericityStatement.{u, uQ})
    (hc : IsArithmeticClassFamily c)
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} [CompactSpace (AdeleQuotient F)]
    (hψ : ∃ x : Adeles F, ψ x ≠ 1) (hdiag : ∀ x : F, ψ (diagonal F x) = 1) {r t : ℕ}
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (D : AutomorphicTwistSetup.{u, uQ} ψ r t) (A : ArithmeticTwistSetup.{u, uV, uE} ψ S S')
    (hadd : ∀ z, A.additive z = D.additive z)
    (hW : IsWeaklyAssociated S D.P.spectralSystem)
    (hW' : IsWeaklyAssociated S' D.P'.spectralSystem)
    (hWd : IsWeaklyAssociated S.dual D.Pd.spectralSystem)
    (hWd' : IsWeaklyAssociated S'.dual D.Pd'.spectralSystem)
    (ω ω' : HeckeCharacter F) (hω : D.T.realization.HasCentralCharacter ω)
    (hω' : D.T'.realization.HasCentralCharacter ω')
    (hdet : FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E ω)
    (hdet' : FiniteRepresentation.determinantCharacter S' = reciprocityCharacter c F E ω')
    (v : FinitePlace F) :
    HasHeckeGammaCertificate.{u, uV, uE} v (D.additive v) (D.measure v) (A.family v)
      (A.system v) (A.system_spec v) (localClass D.P D.h v) (localClass D.P' D.h' v)
      (localPairClass S (A.localMap v)) (localPairClass S' (A.localMap v)) := by
  classical
  obtain ⟨T₀, arch, hAin⟩ := A.exists_engineInputs hEps hc hψ hdiag
  obtain ⟨W₁, hW₁e, hW₁⟩ := exists_finset_isUnramifiedMatchAt hW
  obtain ⟨W₂, hW₂e, hW₂⟩ := exists_finset_isUnramifiedMatchAt hW'
  let Tb : Finset (FinitePlace F) := insert v (W₁ ∪ W₂)
  have hT : ∀ z ∉ Tb, ∃ (hz : z ∉ D.P.exceptional) (hz' : z ∉ D.P'.exceptional),
      IsUnramifiedMatchAt S z (D.P.spectralSystem.eulerPolynomial z hz) ∧
        IsUnramifiedMatchAt S' z (D.P'.spectralSystem.eulerPolynomial z hz') := by
    intro z hz
    simp only [Tb, Finset.mem_insert, Finset.mem_union, not_or] at hz
    have h1 : z ∉ D.P.exceptional := fun h => hz.2.1 (hW₁e h)
    have h2 : z ∉ D.P'.exceptional := fun h => hz.2.2 (hW₂e h)
    exact ⟨h1, h2, hW₁ z h1 hz.2.1, hW₂ z h2 hz.2.2⟩
  obtain ⟨depth, hram⟩ := ramifiedGammaStability_families hL1 hGen D A hEps arch hadd ω ω'
    hω hω' hdet hdet' hW.2.1 hW'.2.1 Tb
  -- the automorphic gamma factor at `v`
  have hd := Correspondence.twistedPairData_spec (D.additive v) (D.measure_spec v)
    (localClass D.P D.h v) (localClass D.P' D.h' v)
    (quasicharacterBase v ((1 : HeckeCharacter F).finiteComponent v))
  obtain ⟨πη, htw, hG⟩ := IsTwistedPairData.exists_gamma hd
  have htw1 := htw
  rw [HeckeCharacter.finiteComponent_one, quasicharacterBase_one] at htw1
  obtain rfl := htw1.unique (Correspondence.isCharacterTwist_one _)
  -- the arithmetic gamma factor at `v`
  have hfs := A.finiteFactors_spec hEps 1 v
  rw [localPairClass_dual, localPairClass_dual] at hfs
  obtain ⟨H, hH, hHc⟩ := hfs.exists_gamma
  change Correspondence.IsArithmeticPairGammaFactor _ _ _ _ _
    (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E 1) S) (A.localMap v))
    (localPairClass S' (A.localMap v)) H at hH
  rw [localPairClass_twist_of_trivial S (A.localMap v) _
    (fun g => reciprocityCharacter_one_apply _), hadd] at hH
  exact ⟨Tb, Finset.mem_insert_self v _, depth,
    HeckeEulerFamily.ofLocalFactors D.localFactors,
    HeckeEulerFamily.ofLocalFactors (A.localFactors arch), _, H, hG, hH,
    hasRationalContinuation_pairDataFactors_gamma hd htw hG, hHc,
    commonTwistEulerInputs_families hFE hEps hψ hdiag D A hW hW' hWd hWd' T₀ arch hAin Tb,
    infinityGammaPreservation_families D A arch, finiteGammaPreservation_families D A arch v,
    hram, outsideGammaStability_families hPS hGen D A hEps arch hadd hW.2.1 hW'.2.1 Tb hT⟩

/-- Two canonical finite components of a global additive character at the same place agree. -/
theorem isCanonicalFiniteAdditiveComponent_unique
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {v : FinitePlace F}
    {ψv ψv' : Correspondence.NontrivialAdditiveCharacter (padicField v)}
    (h : IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h' : IsCanonicalFiniteAdditiveComponent ψ v ψv') : ψv = ψv' := by
  rcases ψv with ⟨χ, hc, hn⟩
  rcases ψv' with ⟨χ', hc', hn'⟩
  have hχ : χ = χ' := DFunLike.ext χ χ' fun x => (h x).trans (h' x).symm
  subst hχ
  rfl

/-- Local-to-relative Weil map data exist at every finite place. -/
theorem exists_localWeilData (hc : IsArithmeticClassFamily c) (z : FinitePlace F) :
    Nonempty (Σ' (w : FinitePlacesAbove E z)
      (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w.1))
      (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E),
      IsLocalRelativeWeilMap z w.1 e ι) := by
  let w : FinitePlacesAbove E z := Classical.arbitrary _
  obtain ⟨e, he, -⟩ := LocalClassField.geometricWeilReciprocityExistenceUniqueness
    (residuePrime z) (towerPadicField z w.1) (towerPadicField z w.1).canonicalTopologicalData
  obtain ⟨I, hI, hgen, hres, hinf, hloc⟩ := hc
  obtain ⟨ι, hι⟩ := localRelativeWeilMapExistence I hI c ⟨hgen, hres, hinf, hloc⟩ F E z w.1 e he
  exact ⟨⟨w, e, ι, hι⟩⟩

/-- Local-constant systems exist over every p-adic field. -/
theorem exists_localSystem {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p) :
    Nonempty (Σ' (eC : LocalFactor.CommonClosure.ReciprocityFamily K)
      (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} K),
      LocalFactor.NonabelianSystem.IsSystem K eC ε) := by
  obtain ⟨eC, heC⟩ : ∃ eC : LocalFactor.CommonClosure.ReciprocityFamily K,
      LocalFactor.CommonClosure.NormalizedReciprocity K eC :=
    LocalClassField.commonClosureReciprocityExistence p K K.canonicalTopologicalData
  obtain ⟨ε, hε⟩ := LocalFactor.NonabelianSystem.exists_system.{u, uE} K eC heC
  exact ⟨⟨eC, ε, hε⟩⟩

/-- **Henniart (2000), Théorème 2.3**, assuming the completed global Rankin–Selberg functional
equation for cuspidal pairs and the stable local comparison under highly ramified twists. The
principal-series comparison, arithmetic pair epsilon factors, local genericity and the
presentation and contragredient existence results are proved Library theorems. -/
theorem associatedGamma_of_inputs
    (hFE : CuspidalPairGlobalFunctionalEquationStatement.{u, u})
    (hL1 : StableTwistPairGammaMatchStatement.{u, uV, uE}) :
    AssociatedGammaStatement.{u, uV, uP, uQ, uE} := by
  classical
  have hGen := Automorphic.CuspidalPairPartialGamma.localGenericity.{u, u}
  have hPS : PrincipalSeriesPairGammaMatchStatement.{u, uV, uE} :=
    @principalSeriesPairGammaMatchStatement.{u, uV, uE}
  have hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE} :=
    @Correspondence.arithmeticPairEpsilonExistence.{u, uV, uE}
  have hPres : Automorphic.CuspidalAllLocalIrreduciblePresentationExistenceStatement.{u, uQ} :=
    @Automorphic.cuspidalAllLocalIrreduciblePresentationExistence.{u, uQ}
  have hDual : Automorphic.CuspidalDualPresentationExistenceStatement.{u, uQ, uQ} :=
    @Automorphic.cuspidalDualPresentationExistence.{u, uQ, uQ}
  have hContra : PresentedContragredientAssociationStatement.{u, uV, u, u} :=
    @presentedContragredientAssociation.{u, uV, u, u}
  intro c hc F E _ _ _ _ _ _ _ ψ hdiag r t S S' T T' hS hS' P P' v hI hA hI' hA' w e ι hι
    ψv hψv eC ε hε
  -- presentations with irreducible admissible local components, and contragredients
  obtain ⟨Q, hQ⟩ := hPres F r T P
  obtain ⟨Q', hQ'⟩ :=
    hPres F t T' P'
  obtain ⟨Td, hTd⟩ := Automorphic.cuspidalContragredientExistence F r T
  obtain ⟨Td', hTd'⟩ := Automorphic.cuspidalContragredientExistence F t T'
  obtain ⟨Pd₀⟩ := hDual F r T Td hTd P
  obtain ⟨Pd₀'⟩ := hDual F t T' Td' hTd' P'
  obtain ⟨Qd, hQd⟩ :=
    hPres F r Td Pd₀
  obtain ⟨Qd', hQd'⟩ :=
    hPres F t Td' Pd₀'
  -- weak association and central characters
  have hW := IsWeaklyAssociatedClass.presentation hS Q
  have hW' := IsWeaklyAssociatedClass.presentation hS' Q'
  have hWd := hContra c F E S T Td Q Qd hTd hW
  have hWd' := hContra c F E S' T' Td' Q' Qd' hTd' hW'
  obtain ⟨ω, hω, hdet, -⟩ := associatedCentralCharacter c hc F E S T hS
  obtain ⟨ω', hω', hdet', -⟩ := associatedCentralCharacter c hc F E S' T' hS'
  -- the global additive character is nontrivial
  have hψ : ∃ x : Adeles F, ψ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rcases ψv with ⟨χ0, hc0, hn0⟩
    exact hn0 (DFunLike.ext χ0 1 fun x => (hψv x).trans (hcon _))
  -- choices supplied by the global functional equation
  obtain ⟨⟨⟨ch⟩, hreal, hcomplex⟩, -⟩ :=
    hFE F ψ hψ hdiag r t T Td T' Td' hTd hTd' Q Q' Qd Qd' hQ hQ' hQd hQd'
  choose aR haR using fun x => (hreal x).1
  choose dR hdR using fun x => (hreal x).2.1
  choose dR' hdR' using fun x => (hreal x).2.2.1
  choose dRd hdRd using fun x => (hreal x).2.2.2.1
  choose dRd' hdRd' using fun x => (hreal x).2.2.2.2
  choose aC haC using fun x => (hcomplex x).1
  choose dC hdC using fun x => (hcomplex x).2.1
  choose dC' hdC' using fun x => (hcomplex x).2.2.1
  choose dCd hdCd using fun x => (hcomplex x).2.2.2.1
  choose dCd' hdCd' using fun x => (hcomplex x).2.2.2.2
  have hadd_v : ch.additive v = ψv :=
    isCanonicalFiniteAdditiveComponent_unique (ch.additive_spec v) hψv
  have hν₀ : Correspondence.IsSelfDualMeasure (padicField v) ψv (ch.measure v) :=
    hadd_v ▸ ch.measure_spec v
  refine isPairGammaMatch_of_heckeGammaCertificate v ψv eC ε hε _ _ _ _ ⟨_, hν₀⟩
    fun ν hν => ?_
  -- the two setups, with the given local data at `v`
  let meas := Function.update ch.measure v ν
  have hmeas : ∀ z, Correspondence.IsSelfDualMeasure (padicField z) (ch.additive z)
      (meas z) := by
    intro z
    rcases eq_or_ne z v with rfl | hz
    · simp only [meas, Function.update_self]
      rw [hadd_v]
      exact hν
    · simp only [meas, Function.update_of_ne hz]
      exact ch.measure_spec z
  let D : AutomorphicTwistSetup.{u, u} ψ r t :=
    { T := T, T' := T', Td := Td, Td' := Td', hTd := hTd, hTd' := hTd', P := Q, P' := Q',
      Pd := Qd, Pd' := Qd', h := hQ, h' := hQ', hd := hQd, hd' := hQd',
      additive := ch.additive, additive_spec := ch.additive_spec, measure := meas,
      measure_spec := hmeas, aR := aR, aR_spec := haR, aC := aC, aC_spec := haC,
      dR := dR, dR' := dR', dRd := dRd, dRd' := dRd', dR_spec := hdR, dR'_spec := hdR',
      dRd_spec := hdRd, dRd'_spec := hdRd', dC := dC, dC' := dC', dCd := dCd, dCd' := dCd',
      dC_spec := hdC, dC'_spec := hdC', dCd_spec := hdCd, dCd'_spec := hdCd',
      w₀ := Classical.arbitrary _ }
  let ld := Function.update (fun z => Classical.choice (exists_localWeilData (E := E) hc z)) v
    ⟨w, e, ι, hι⟩
  let ls := Function.update
    (fun z => Classical.choice (exists_localSystem.{u, uE} (padicField z))) v ⟨eC, ε, hε⟩
  let A : ArithmeticTwistSetup.{u, uV, uE} ψ S S' :=
    { hS := hW.1, hS' := hW'.1, place := fun z => (ld z).1, candidate := fun z => (ld z).2.1,
      localMap := fun z => (ld z).2.2.1, localMap_spec := fun z => (ld z).2.2.2,
      additive := ch.additive, additive_spec := ch.additive_spec,
      family := fun z => (ls z).1, system := fun z => (ls z).2.1,
      system_spec := fun z => (ls z).2.2 }
  have hcert := hasHeckeGammaCertificate_setups hFE hL1 hPS hEps hGen hc hψ hdiag D A
    (fun _ => rfl) hW hW' hWd hWd' ω ω' hω hω' hdet hdet' v
  have hcl : localClass Q hQ v = (P.localComponent v).padicClass hI hA :=
    Automorphic.CuspidalSpectralPresentation.localComponent_padicClass_eq Q P v _ _ hI hA
  have hcl' : localClass Q' hQ' v = (P'.localComponent v).padicClass hI' hA' :=
    Automorphic.CuspidalSpectralPresentation.localComponent_padicClass_eq Q' P' v _ _ hI' hA'
  change HasHeckeGammaCertificate.{u, uV, uE} v (ch.additive v) (meas v) (ls v).1 (ls v).2.1
    (ls v).2.2 (localClass Q hQ v) (localClass Q' hQ' v) (localPairClass S (ld v).2.2.1)
    (localPairClass S' (ld v).2.2.1) at hcert
  rw [hcl, hcl'] at hcert
  have hmv : meas v = ν := Function.update_self _ _ _
  have hldv : ld v = ⟨w, e, ι, hι⟩ := Function.update_self _ _ _
  have hlsv : ls v = ⟨eC, ε, hε⟩ := Function.update_self _ _ _
  have key : ∀ (a : Correspondence.NontrivialAdditiveCharacter (padicField v))
      (m : Correspondence.LocalAdditiveHaarMeasure (padicField v))
      (s : Σ' (eC' : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
        (ε' : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField v)),
        LocalFactor.NonabelianSystem.IsSystem (padicField v) eC' ε')
      (d : Σ' (w' : FinitePlacesAbove E v)
        (e' : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w'.1))
        (ι' : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E),
        IsLocalRelativeWeilMap v w'.1 e' ι'),
      a = ψv → m = ν → s = ⟨eC, ε, hε⟩ → d = ⟨w, e, ι, hι⟩ →
      HasHeckeGammaCertificate.{u, uV, uE} v a m s.1 s.2.1 s.2.2
        ((P.localComponent v).padicClass hI hA) ((P'.localComponent v).padicClass hI' hA')
        (localPairClass S d.2.2.1) (localPairClass S' d.2.2.1) →
      HasHeckeGammaCertificate.{u, uV, uE} v ψv ν eC ε hε
        ((P.localComponent v).padicClass hI hA) ((P'.localComponent v).padicClass hI' hA')
        (localPairClass S ι) (localPairClass S' ι) := by
    rintro a m s d rfl rfl rfl rfl h
    exact h
  exact key _ _ _ _ hadd_v hmv hlsv hldv hcert

end Langlands.ClassFieldTheory.Global.RelativeWeilGroup
