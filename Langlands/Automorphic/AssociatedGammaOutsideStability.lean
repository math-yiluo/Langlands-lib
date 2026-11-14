import Langlands.Automorphic.AssociatedGammaRamifiedStability
import Langlands.Automorphic.AssociatedGammaPrincipalSeries
import Langlands.Automorphic.AssociatedGammaTriangular
import Langlands.Automorphic.LocalSphericalHecke
import Langlands.Correspondence.UnramifiedReciprocityBridge
import Langlands.Weil.Representation.TwistProperties

/-!
# Gamma stability outside a finite set for the two Hecke families

At a finite place `z` where both presentations are unramified and both relative Weil
representations are unramified with matching Euler polynomials, the published
principal-series comparison `PrincipalSeriesPairGammaMatchStatement` applies to the twisted
pair `(π_z ⊗ χ_z, π'_z)` and `(S ⊗ χ, S')` along the local map, for every finite-order Hecke
character `χ`. Hence the gamma factors of the two Hecke families agree at `z`.
-/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u uQ uV uE

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison Langlands.Global.AdelicFunctoriality
open Langlands.Global.CuspidalPairFunctionalEquation

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- **Automorphic side.** Outside the exceptional set, the local class of a presentation has
a generic representative that is a subquotient of the unramified principal series of a tuple
of Satake parameters. -/
theorem exists_principalSeries_localClass [CompactSpace (AdeleQuotient F)] {r : ℕ}
    {T : Automorphic.CuspidalOperatorRealization F r}
    (hGen : Automorphic.CuspidalLocalGenericityStatement.{u, uQ})
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (h : HasIrreducibleAdmissibleComponents P) (z : FinitePlace F) (hz : z ∉ P.exceptional)
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField z)) :
    ∃ x : Fin (r + 1) → ℂˣ,
      Unramified.Eigenvalues.ofTuple x = P.spectralSystem.eigenvalues z hz ∧
        ∃ A : Correspondence.AutomorphicObject.{u, u} (padicField z) r.succPNat,
          Correspondence.automorphicClassOf _ A = localClass P h z ∧
            (letI := (padicField z).canonicalTopologicalData.topology
             letI := (padicField z).canonicalGeneralLinearTopology (r + 1)
             Whittaker.IsGeneric ψ r A.obj.representation ∧
               Correspondence.IsSubquotientOf
                 (Correspondence.principalSeries (padicField z) r
                   (Unramified.characterTuple _ x))
                 A.obj.representation) := by
  set O := (P.localComponent z).padicObject (h z).1 (h z).2
  have hO : Unramified.HasSphericalHeckeSpectrum (padicField z) O
      (P.spectralSystem.eigenvalues z hz) :=
    (Unramified.hasSphericalHeckeSpectrumClass_classOf _ O _).mp
      (((P.localComponent z).hasSphericalHeckeSpectrumClass_iff (h z).1 (h z).2 _).mpr
        (P.hasSpectrum z hz))
  obtain ⟨x, hx, -, hsub⟩ :=
    Unramified.hasSphericalSpectrum_of_hasSphericalHeckeSpectrum _ O _ hO
  exact ⟨x, hx, O, rfl, hGen F r T P z (h z).1 (h z).2 ψ, hsub⟩

/-- **Arithmetic side.** An unramified local component whose Euler polynomial is
`∏ (1 - x_i X)` has a basis in which every Weil element acts upper triangularly with diagonal
entries `x_(σ i) ^ deg g`. -/
theorem exists_localComponent_basis
    (S₀ : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)) {z : FinitePlace F}
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E) {n : ℕ}
    (hn : S₀.rank = n)
    (hU : (localComponent S₀ ι).IsUnramified (Weil.Local.localInertia (padicField z)))
    (x : Fin n → ℂˣ) (hx : localEulerPolynomial S₀ ι = ∏ i, (1 - C (x i : ℂ) * X)) :
    ∃ (b : Module.Basis (Fin n) ℂ S₀) (σ : Equiv.Perm (Fin n)),
      ∀ g : Weil.Local.localWeilGroup (padicField z),
        (∀ i j : Fin n, j < i → b.repr (S₀.representation (ι g) (b j)) i = 0) ∧
          ∀ i : Fin n, b.repr (S₀.representation (ι g) (b i)) i =
            ((x (σ i) ^ Weil.Local.localDegreeInt (padicField z) g : ℂˣ) : ℂ) :=
  Weil.Local.exists_triangular_basis_of_eulerPolynomial (padicField z) hn
    (localComponent S₀ ι).representation (fun i hi => hU ⟨i, hi⟩) x hx

/-- **Outside gamma stability** for the two families, from the principal-series comparison. -/
theorem outsideGammaStability_families
    (hPS : PrincipalSeriesPairGammaMatchStatement.{u, uV, uE})
    (hGen : Automorphic.CuspidalLocalGenericityStatement.{u, uQ})
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    [CompactSpace (AdeleQuotient F)] {r t : ℕ}
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (D : AutomorphicTwistSetup.{u, uQ} ψ r t) (A : ArithmeticTwistSetup.{u, uV, uE} ψ S S')
    (hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE})
    (arch : NumberField.InfinitePlace F → LocalFactors)
    (hadd : ∀ z, A.additive z = D.additive z)
    (hrank : S.rank = r + 1) (hrank' : S'.rank = t + 1) (T : Finset (FinitePlace F))
    (hT : ∀ z ∉ T, ∃ (hz : z ∉ D.P.exceptional) (hz' : z ∉ D.P'.exceptional),
      IsUnramifiedMatchAt S z (D.P.spectralSystem.eulerPolynomial z hz) ∧
        IsUnramifiedMatchAt S' z (D.P'.spectralSystem.eulerPolynomial z hz')) :
    OutsideGammaStability F T (HeckeEulerFamily.ofLocalFactors D.localFactors)
      (HeckeEulerFamily.ofLocalFactors (A.localFactors arch)) := by
  intro χ _ z hzT
  obtain ⟨hz, hz', hS, hS'⟩ := hT z hzT
  set η := quasicharacterBase z (χ.finiteComponent z)
  set e := Correspondence.baseReciprocityCandidate _ (A.family z)
  have he : Correspondence.IsGeometricReciprocity (padicField z) e :=
    Correspondence.isGeometricReciprocity_of_isBaseReciprocity _ _ _
      (Correspondence.baseReciprocityCandidate_spec _ (A.family z)) (A.system_spec z).1
  have hw : ∀ (y : ℂˣ) (g : Weil.Local.localWeilGroup (padicField z)),
      Correspondence.weilCharacter (padicField z) e (Unramified.character _ y) g =
        y ^ Weil.Local.localDegreeInt (padicField z) g := by
    intro y g
    rw [Correspondence.weilCharacter_apply_of_isUnramified _ he
      (Unramified.character_isUnramified _ y), Unramified.character_uniformizer]
  -- automorphic side
  obtain ⟨πη, htw⟩ := exists_isCharacterTwist η (localClass D.P D.h z)
  obtain ⟨x, hx, hπ⟩ := exists_principalSeries_localClass hGen D.P D.h z hz (D.additive z)
  obtain ⟨x', hx', hπ'⟩ := exists_principalSeries_localClass hGen D.P' D.h' z hz' (D.additive z)
  have hπη := Correspondence.exists_generic_subquotient_twist _ (D.additive z) _ η hπ htw
  have hπ1 := Correspondence.exists_generic_subquotient_twist _ (D.additive z) _ 1 hπ'
    (Correspondence.isCharacterTwist_one _)
  -- arithmetic side
  set ι := A.localMap z
  obtain ⟨hU, hE⟩ := (hS (A.place z)).2 (A.candidate z) ι (A.localMap_spec z)
  obtain ⟨hU', hE'⟩ := (hS' (A.place z)).2 (A.candidate z) ι (A.localMap_spec z)
  have hEx : localEulerPolynomial S ι = ∏ i, (1 - C (x i : ℂ) * X) := by
    rw [hE, ← Unramified.Eigenvalues.eulerPolynomial_ofTuple, hx]
    rfl
  have hEx' : localEulerPolynomial S' ι = ∏ i, (1 - C (x' i : ℂ) * X) := by
    rw [hE', ← Unramified.Eigenvalues.eulerPolynomial_ofTuple, hx']
    rfl
  obtain ⟨b, σ, hb⟩ := exists_localComponent_basis S ι hrank hU x hEx
  obtain ⟨b', σ', hb'⟩ := exists_localComponent_basis S' ι hrank' hU' x' hEx'
  set ηW := localTwistCharacter (A.family z) χ
  have hX : ∃ B : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} (padicField z),
      WeilDeligneRepresentation.classOf B =
        localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) ι ∧
        B.monodromy = 0 ∧ B.toFiniteRepresentation.IsContinuous ∧
        ∃ (b : Module.Basis (Fin (r + 1)) ℂ B) (σ : Equiv.Perm (Fin (r + 1))),
          ∀ g : Weil.Local.localWeilGroup (padicField z),
            (∀ i j : Fin (r + 1), j < i → b.repr (B.representation g (b j)) i = 0) ∧
              ∀ i : Fin (r + 1), b.repr (B.representation g (b i)) i =
                ((Correspondence.weilCharacter (padicField z) e
                  ((fun i => Unramified.characterTuple _ x i * η) (σ i)) g : ℂˣ) : ℂ) := by
    refine ⟨WeilDeligneRepresentation.zeroMonodromy
      (Weil.Local.localNormCharacter (padicField z)).toMonoidHom
      (FiniteRepresentation.twist ηW.toMonoidHom (localComponent S ι)),
      (localPairClass_twist_eq S ι _ ηW.toMonoidHom
        (reciprocityCharacter_apply_localMap (A.localMap_spec z) (A.family z)
          (A.system_spec z).1 χ)).symm, rfl,
      FiniteRepresentation.isContinuous_twist ηW (localComponent_isContinuous ι A.hS),
      b, σ, fun g => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
    · change b.repr (((ηW g : ℂˣ) : ℂ) • S.representation (ι g) (b j)) i = 0
      rw [map_smul, Finsupp.smul_apply, (hb g).1 i j hij, smul_zero]
    · change b.repr (((ηW g : ℂˣ) : ℂ) • S.representation (ι g) (b i)) i =
        ((Correspondence.weilCharacter (padicField z) e (Unramified.character _ (x (σ i))) g *
          Correspondence.weilCharacter (padicField z) e η g : ℂˣ) : ℂ)
      rw [map_smul, Finsupp.smul_apply, (hb g).2 i, hw, smul_eq_mul, Units.val_mul, mul_comm]
      rfl
  have hY : ∃ B : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} (padicField z),
      WeilDeligneRepresentation.classOf B = localPairClass S' ι ∧
        B.monodromy = 0 ∧ B.toFiniteRepresentation.IsContinuous ∧
        ∃ (b : Module.Basis (Fin (t + 1)) ℂ B) (σ : Equiv.Perm (Fin (t + 1))),
          ∀ g : Weil.Local.localWeilGroup (padicField z),
            (∀ i j : Fin (t + 1), j < i → b.repr (B.representation g (b j)) i = 0) ∧
              ∀ i : Fin (t + 1), b.repr (B.representation g (b i)) i =
                ((Correspondence.weilCharacter (padicField z) e
                  ((fun i => Unramified.characterTuple _ x' i * 1) (σ i)) g : ℂˣ) : ℂ) := by
    refine ⟨WeilDeligneRepresentation.zeroMonodromy
      (Weil.Local.localNormCharacter (padicField z)).toMonoidHom (localComponent S' ι),
      rfl, rfl, localComponent_isContinuous ι A.hS', b', σ', fun g =>
        ⟨(hb' g).1, fun i => ?_⟩⟩
    change b'.repr (S'.representation (ι g) (b' i)) i =
      ((Correspondence.weilCharacter (padicField z) e (Unramified.character _ (x' (σ' i))) g *
        1 : ℂˣ) : ℂ)
    rw [(hb' g).2 i, hw, mul_one]
  have hmatch := hPS (padicField z) (A.family z) (A.system z) (A.system_spec z) e
    (Correspondence.baseReciprocityCandidate_spec _ (A.family z)) (D.additive z)
    (fun i => Unramified.characterTuple _ x i * η)
    (fun i => Unramified.characterTuple _ x' i * 1) πη (localClass D.P' D.h' z)
    (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) ι)
    (localPairClass S' ι) hπη hπ1 hX hY
  exact meromorphicEq_gamma_of_isPairGammaMatch D A hEps arch χ z (hadd z) htw hmatch

end Langlands.ClassField.Global.RelativeWeilGroup
