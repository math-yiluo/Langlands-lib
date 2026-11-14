import Langlands.Automorphic.StableTwist.ClassStability
import Langlands.Automorphic.StableTwist.PrincipalSeriesModel
import Langlands.Automorphic.StableTwist.DiagonalModel
import Langlands.Automorphic.ArithmeticStableTwistGammaStatement
import Langlands.Automorphic.PrincipalSeriesGammaMatchStatement
import Langlands.Automorphic.StableTwistGammaMatchStatement
import Langlands.Correspondence.AssemblyDeterminant

/-!
# Stable pair gamma comparison from its three inputs

Henniart (1986), Lemma 4.2: the stable comparison of pair gamma factors under highly
ramified twists follows from
* the twist-exchange identity for JPSS pair gamma factors (through representation-side
  stability, `classPairGammaStability`),
* arithmetic stability of pair gamma factors under highly ramified twists, and
* the comparison for generic principal-series constituents and diagonal parameters.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Automorphic.StableTwist

open Langlands.Correspondence
open Langlands.ClassField.Global.RelativeWeilGroup

universe u uV uE

variable {p : ℕ} [Fact p.Prime]

local instance assemblyTopology (K : PadicField.{u} p) : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance assemblyGLTopology (K : PadicField.{u} p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopology n

local instance assemblyGLTopologicalGroup (K : PadicField.{u} p) (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopologicalGroup n

/-- **Stable pair gamma comparison, conditional form.** The twist-exchange statement, the
arithmetic stability statement and the principal-series comparison together imply the
stable pair gamma comparison under highly ramified twists. -/
theorem stableTwistPairGammaMatch_of
    (hR1 : RankinSelberg.PairGammaTwistExchangeStatement.{u, u, u})
    (hA : ArithmeticStableTwistGammaStatement.{u, uV, uE})
    (hPS : PrincipalSeriesPairGammaMatchStatement.{u, uV, uE}) :
    StableTwistPairGammaMatchStatement.{u, uV, uE} := by
  intro p _ K eC ε hε e he ψ r t π π' ω ω' X Y hπ hπ' hω hω' hX hY
  obtain ⟨A, hAπ, hAgen⟩ := hπ
  obtain ⟨A', hA'π', hA'gen⟩ := hπ'
  -- Principal-series models with the same central characters.
  obtain ⟨μ, A₀, hμ, hA₀gen, hA₀sub, hA₀cc⟩ := exists_generic_principalSeries_object K ψ r ω
  obtain ⟨μ', A₀', hμ', hA₀'gen, hA₀'sub, hA₀'cc⟩ :=
    exists_generic_principalSeries_object K ψ t ω'
  -- Diagonal Weil–Deligne models.
  have hB₀ := localDiagonal_spec.{u, uV} K e μ
  have hB₀' := localDiagonal_spec.{u, uV} K e μ'
  rw [hμ] at hB₀
  rw [hμ'] at hB₀'
  -- Arithmetic stability.
  obtain ⟨N₁, hN₁⟩ := hA K eC ε hε e he ψ ω ω' X
    (WeilDeligneRepresentation.classOf (localDiagonal.{u, uV} K e μ)) Y
    (WeilDeligneRepresentation.classOf (localDiagonal.{u, uV} K e μ')) hX
    ⟨_, rfl, hB₀.1, hB₀.2.2.1, hB₀.2.2.2.1⟩ hY
    ⟨_, rfl, hB₀'.1, hB₀'.2.2.1, hB₀'.2.2.2.1⟩
  -- Representation-side stability.
  have hcA : RankinSelberg.SameGLCentralCharacter K A.obj.representation
      A₀.obj.representation :=
    ⟨ω.toMonoidHom, fun a v =>
      AssemblyDeterminant.centralActsBy_apply K (hω a) A hAπ v, hA₀cc⟩
  have hcA' : RankinSelberg.SameGLCentralCharacter K A'.obj.representation
      A₀'.obj.representation :=
    ⟨ω'.toMonoidHom, fun a v =>
      AssemblyDeterminant.centralActsBy_apply K (hω' a) A' hA'π' v, hA₀'cc⟩
  obtain ⟨N₂, hN₂⟩ := classPairGammaStability hR1 K ψ A A₀ A' A₀' hAgen hA₀gen hA'gen
    hA₀'gen hcA hcA'
  subst hAπ
  subst hA'π'
  refine ⟨max N₁ N₂, fun χ hχ πχ htw => ?_⟩
  obtain ⟨π₀χ, h₀tw⟩ := exists_isCharacterTwist K χ (automorphicClassOf K A₀)
  have hBχ := localDiagonal_spec.{u, uV} K e (fun i => μ i * χ)
  have hmatch := hPS K eC ε hε e he ψ (fun i => μ i * χ) μ' π₀χ (automorphicClassOf K A₀')
    (WeilDeligneRepresentation.classOf (localDiagonal.{u, uV} K e (fun i => μ i * χ)))
    (WeilDeligneRepresentation.classOf (localDiagonal.{u, uV} K e μ'))
    (exists_generic_subquotient_twist K ψ μ χ ⟨A₀, rfl, hA₀gen, hA₀sub⟩ h₀tw)
    ⟨A₀', rfl, hA₀'gen, hA₀'sub⟩
    ⟨_, rfl, hBχ.2.1, hBχ.2.2.1, hBχ.2.2.2.2⟩
    ⟨_, rfl, hB₀'.2.1, hB₀'.2.2.1, hB₀'.2.2.2.2⟩
  rw [← twistClass_localDiagonal] at hmatch
  obtain ⟨hex, hall⟩ := hmatch
  refine ⟨hex, fun ν hν => ?_⟩
  obtain ⟨G, hG₁, hG₂⟩ := hall ν hν
  exact ⟨G, hN₂ χ (le_trans (le_max_right _ _) hχ) πχ π₀χ htw h₀tw ν hν G hG₁,
    hN₁ χ (le_trans (le_max_left _ _) hχ) G hG₂⟩

end Langlands.Automorphic.StableTwist
