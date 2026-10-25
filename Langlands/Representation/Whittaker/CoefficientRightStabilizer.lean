import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.NormalizedCharacter

/-!
# Common right stabilizers for actual coefficient functions

Smoothness gives a common compact open right stabilizer in every prescribed
identity neighborhood. The p-adic specialization uses the supplied topology
and puts that stabilizer in the normalized determinant kernel.
-/

noncomputable section

namespace Langlands.Whittaker

open Topology
open scoped NNReal

universe uR uG uV uW uF

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W]
variable {N N' : Subgroup G} {θ : N →* Rˣ} {θ' : N' →* Rˣ}

/-- Each of two specified actual coefficient functions is right invariant
under the given subgroup. The functions and functionals remain fixed. -/
def IsCommonCoefficientRightStabilizer
    {ρ : Representation R G V} {σ : Representation R G W}
    {ℓ : functionals N θ ρ} {ℓ' : functionals N' θ' σ}
    (f : (coefficientModel ρ ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule) (J : Subgroup G) : Prop :=
  (∀ g : G, ∀ j : J, f.val.val (g * j.val) = f.val.val g) ∧
  (∀ g : G, ∀ j : J, f'.val.val (g * j.val) = f'.val.val g)

/-- Two actual coefficient vectors of smooth representations have a common
compact open right stabilizer inside any identity neighborhood. -/
theorem exists_compactOpen_coefficientRightStabilizer
    [TopologicalSpace G] [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
    (ρ : Representation R G V) (σ : Representation R G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (ℓ : functionals N θ ρ) (ℓ' : functionals N' θ' σ)
    (f : (coefficientModel ρ ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (U : Set G) (hU : U ∈ 𝓝 (1 : G)) :
    ∃ J : OpenSubgroup G, IsCompact (J : Set G) ∧ (J : Set G) ⊆ U ∧
      IsCommonCoefficientRightStabilizer f f' J.toSubgroup := by
  obtain ⟨K, hK⟩ := model_isSmooth ρ hρ ℓ f
  obtain ⟨L, hL⟩ := model_isSmooth σ hσ ℓ' f'
  obtain ⟨J, hJ, hJU⟩ := compactOpenSubgroupBasis G
    ((U ∩ (K : Set G)) ∩ (L : Set G))
    (Filter.inter_mem (Filter.inter_mem hU K.mem_nhds_one) L.mem_nhds_one)
  refine ⟨J, hJ, fun g hg => (hJU hg).1.1, ?_, ?_⟩
  · intro g j
    have hfix := hK ⟨j.val, (hJU j.property).1.2⟩
    exact congrArg
      (fun w : (coefficientModel ρ ℓ).toSubmodule => w.val.val g) hfix
  · intro g j
    have hfix := hL ⟨j.val, (hJU j.property).2⟩
    exact congrArg
      (fun w : (coefficientModel σ ℓ').toSubmodule => w.val.val g) hfix

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For every supplied local-field topology, two actual Whittaker coefficient
vectors have a common compact open right stabilizer on which the supplied
normalized determinant absolute value is one. Rank one is included. -/
theorem exists_compactOpen_glCoefficientRightStabilizer (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
      IsSmooth π → IsSmooth σ →
      ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
        (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule),
      ∃ J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
        IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∧
        IsCommonCoefficientRightStabilizer f f' J.toSubgroup ∧
        ∀ j : J, T.normalizedAbs (Matrix.det j.val.val) = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ W _ _ π σ hπ hσ ℓ ℓ' f f'
  let := T.generalLinearNonarchimedean (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    ⟨(T.determinantNorm (n + 1)).ker, T.isOpen_ker_determinantNorm (n + 1)⟩
  obtain ⟨J, hJ, hJK, hfix⟩ := exists_compactOpen_coefficientRightStabilizer
    π σ hπ hσ ℓ ℓ' f f' (K : Set _) K.mem_nhds_one
  refine ⟨J, hJ, hfix, ?_⟩
  intro j
  have hj : T.determinantNorm (n + 1) j.val = 1 := hJK j.property
  have heq := congrArg (fun a : ℝ≥0ˣ => ((a : ℝ≥0) : ℝ)) hj
  exact heq

end Padic

end Langlands.Whittaker
