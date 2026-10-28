import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Whittaker.MirabolicFunctionalTransfer
import Langlands.Representation.Classification.FiniteLengthProof
import Langlands.Group.GL.BlockIwahoriBasis

/-! Supplied-topology inputs for the unequal-rank finite-length assembly. -/

noncomputable section

namespace Langlands.RankinSelberg.UnequalRankAssembly

open GeneralLinear Whittaker

universe uF uV

variable {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Whittaker type supplies finite length over the original general linear
group, for the topology actually supplied by `T`. -/
theorem finiteLength_of_whittakerType
    (θ : upperUnipotent (n + 1) F.Carrier →* ℂˣ)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) :
    letI := T.topology
    IsOfWhittakerType n θ π →
      IsFiniteLength (MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
        π.asModule := by
  let := T.topology
  intro hπ
  exact glAdmissibleFiniteLength p F (n + 1) (Nat.succ_pos n) V π
    (by rw [← T.topology_eq_canonicalModule]; exact hπ.1) hπ.2.1

/-- Choose the one-dimensional functional-space equivalence on the actual
mirabolic restriction from the full Whittaker-type hypothesis. -/
def mirabolicFunctionalEquivOfWhittakerType
    (θ : upperUnipotent (n + 1) F.Carrier →* ℂˣ)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) :
    letI := T.topology
    IsOfWhittakerType n θ π →
      functionals (Mirabolic.upperUnipotent n F.Carrier)
        (θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom)
        (π.comp (mirabolic n F.Carrier).subtype) ≃ₗ[ℂ] ℂ := by
  let := T.topology
  intro hπ
  exact (mirabolicFunctionalsEquiv θ π).symm.trans (Classical.choice hπ.2.2)

/-- The actual mirabolic restriction is smooth, and its transported
functional character is locally constant. -/
theorem mirabolic_smooth_and_character_locallyConstant_of_whittakerType
    (θ : upperUnipotent (n + 1) F.Carrier →* ℂˣ)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) :
    letI := T.topology
    IsOfWhittakerType n θ π →
      IsSmooth (π.comp (mirabolic n F.Carrier).subtype) ∧
        IsLocallyConstant (fun u : Mirabolic.upperUnipotent n F.Carrier =>
          (θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom u : ℂ)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hπ
  let ρP := π.comp (mirabolic n F.Carrier).subtype
  let θP := θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom
  have hρP : IsSmooth ρP := isSmooth_comp _ continuous_subtype_val hπ.1.1
  let eP := mirabolicFunctionalEquivOfWhittakerType F T n θ π hπ
  have hfun : HasFunctional (N := Mirabolic.upperUnipotent n F.Carrier)
      (θ := θP) ρP :=
    (functionalLength_ne_zero_iff _ _ _).mp (by
      rw [functionalLength_eq_one_of_equiv _ _ _ eP]
      exact one_ne_zero)
  exact ⟨hρP, character_isLocallyConstant_of_hasFunctional _ _ _ hρP hfun⟩

/-- The original general linear character is locally constant as well,
including the inverse-standard character used by the smaller factor. -/
theorem character_locallyConstant_of_whittakerType
    (θ : upperUnipotent (n + 1) F.Carrier →* ℂˣ)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) :
    letI := T.topology
    IsOfWhittakerType n θ π →
      IsLocallyConstant (fun u : upperUnipotent (n + 1) F.Carrier => (θ u : ℂ)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hπ
  obtain ⟨e⟩ := hπ.2.2
  have hfun : HasFunctional (N := upperUnipotent (n + 1) F.Carrier) (θ := θ) π :=
    (functionalLength_ne_zero_iff _ _ _).mp (by
      rw [functionalLength_eq_one_of_equiv _ _ _ e]
      exact one_ne_zero)
  exact character_isLocallyConstant_of_hasFunctional _ _ _ hπ.1.1 hfun

/-- Every open subgroup of the smaller general linear group contains a
compact open subgroup for the topology supplied by `T`. -/
theorem generalLinear_compactOpen_cofinal :
    letI := T.topology
    ∀ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
      ∃ K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
        IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∧ K ≤ L := by
  let := T.topology
  intro L
  let B : BlockShape (n + 1) := ⟨1, fun _ => n + 1, fun _ => Nat.succ_pos n, by simp⟩
  obtain ⟨K, hK, hKL, -⟩ :=
    BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization B T
      (L.isOpen.mem_nhds L.one_mem)
  exact ⟨K, hK, hKL⟩

end Langlands.RankinSelberg.UnequalRankAssembly
