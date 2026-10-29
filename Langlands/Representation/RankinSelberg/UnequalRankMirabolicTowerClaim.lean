import Langlands.Representation.RankinSelberg.UnequalRankMirabolicTowerFinite
import Langlands.Representation.Whittaker.MirabolicPairingRigidityStep
import Langlands.Representation.Derivative.MirabolicMinusIrreducibleProof
import Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof
import Langlands.Representation.Whittaker.MirabolicFunctionalMultiplicityProof

/-!
# Rigidity of pairings with tower data

Let `η` be an admissible irreducible representation of `GL_(N+1)` and let
`(ρ, q)` be a smooth tower datum for `η` at level `j ≤ N`. Outside finitely many
spectral values `q^(-s)`, a nonzero twisted form between a smooth irreducible
representation `X` of `P_j` and `ρ` forces `X` to be the compact mirabolic model
and `η` to have a standard Whittaker functional. The proof is by induction on `j`,
applying `Φ⁻` on both sides of the form.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnequalRankTower

open GeneralLinear HarmonicAnalysis Whittaker Polynomial
open Whittaker.MirabolicRigidity

universe uF uU uV uW

section Eigen

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- If a functional `f` satisfies `f (S y) = l f(y)`, then `f (P(S) y) = P(l) f(y)`. -/
theorem apply_aeval_of_eigen (f : M →ₗ[ℂ] ℂ) {S : Module.End ℂ M} {l : ℂ}
    (h : ∀ y, f (S y) = l * f y) (P : ℂ[X]) (y : M) :
    f (aeval S P y) = P.eval l * f y := by
  have hc : f ∘ₗ S = algebraMap ℂ (Module.End ℂ ℂ) l ∘ₗ f := by
    apply LinearMap.ext
    intro y
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h, Module.algebraMap_end_apply, smul_eq_mul]
  have key := LinearMap.congr_fun (comp_aeval f hc P) y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, aeval_algebraMap_apply_eq_algebraMap_eval,
    Module.algebraMap_end_apply, smul_eq_mul] at key
  exact key

end Eigen

/-- Claim `C(j)`: rigidity of twisted forms between an irreducible representation
of `P_j` and a smooth tower datum at level `j`. -/
theorem towerClaim {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (j : ℕ) :
    letI := T.topology
    letI : IsTopologicalRing F.Carrier := by
      let := T.valuativeRel
      let := T.localField
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) {N : ℕ} (h : j ≤ N)
      {W : Type uU} [AddCommGroup W] [Module ℂ W]
      (η : Representation ℂ (Langlands.GeneralLinear (N + 1) F.Carrier) W),
      IsAdmissible η → η.IsIrreducible →
      ∀ (A : Type uW) [AddCommGroup A] [Module ℂ A]
        (ρ : Representation ℂ (mirabolic j F.Carrier) A), IsSmooth ρ →
      ∀ q : W →ₗ[ℂ] A, IsTower ψ η h ρ q →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (X : Representation ℂ (mirabolic j F.Carrier) V), IsSmooth X → X.IsIrreducible →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        ∀ β : InvariantBilinear.forms X ρ
            (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)),
          β ≠ 0 →
            Nonempty (X.Equiv (mirabolicCompactInduced ψ j)) ∧
            HasFunctional (N := upperUnipotent (N + 1) F.Carrier)
              (θ := standardCharacter ψ N) η := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hq : 0 < T.residueCardinality :=
    lt_trans Nat.zero_lt_one T.residueCardinality_gt_one
  induction j with
  | zero =>
    intro ψ N h W _ _ η _ _ A _ _ ρ _ q hT V _ _ X _ hirr
    refine ⟨∅, fun s _ β hβ => ⟨rankOne_equiv ψ X hirr, ?_⟩⟩
    obtain ⟨x, hx⟩ : ∃ x, β.val x ≠ 0 := by
      by_contra! h0
      exact hβ (Subtype.ext (LinearMap.ext h0))
    exact hT.hasFunctional (β.val x) hx
  | succ j ih =>
    intro ψ N h W _ _ η hadm hirrη A _ _ ρ hρ q hT V _ _ X hs hirr
    rcases radicalTrivial_or_radicalGenerated X hirr with ht | hg
    · -- `X` is radical-trivial: spectral finiteness from the tower.
      have : SecondCountableTopology
          (Langlands.GeneralLinear (j + 1 + 1) F.Carrier) :=
        T.generalLinearSecondCountableTopology (j + 1 + 1)
      have : SecondCountableTopology (mirabolic (j + 1) F.Carrier) :=
        Topology.IsEmbedding.subtypeVal.secondCountableTopology
      let ϖ := LocalFactor.PadicAbelian.uniformizerUnit T
      have hϖ : normalizedAbsoluteValue T (ϖ : F.Carrier) =
          (T.residueCardinality : ℝ) ^ (-1 : ℤ) := by
        rw [normalizedAbsoluteValue_apply, LocalFactor.PadicAbelian.uniformizerUnit_coe]
        exact T.normalizedAbs_uniformizer
      let z : mirabolic (j + 1) F.Carrier := leviScalar ϖ
      obtain ⟨c, hc⟩ := exists_scalar_of_commute X (rank_le_aleph0 X hs hirr) hirr z
        (apply_mul_leviScalar ht ϖ)
      obtain ⟨P, hP0, hP⟩ := IsTower.exists_polynomial T h hT hadm hirrη ϖ
      classical
      refine ⟨P.roots.toFinset.biUnion
        (fun l => (nthRoots (j + 1) (l * c)⁻¹).toFinset), fun s hsE β hβ => ?_⟩
      exfalso
      obtain ⟨x, y, hxy⟩ : ∃ x y, β.val x y ≠ 0 := by
        by_contra! h0
        exact hβ (Subtype.ext (LinearMap.ext fun x => LinearMap.ext fun y => h0 x y))
      have hc0 : c ≠ 0 := by
        rintro rfl
        have hx0 : x = 0 := by
          have h1 : X z⁻¹ (X z x) = x := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
            rfl
          rw [← h1, hc x, zero_smul, map_zero]
        apply hxy
        rw [hx0, map_zero, LinearMap.zero_apply]
      -- the functional `β x` kills the radical span of `ρ`
      have hker : ∀ y' ∈ (radicalSpan ρ).toSubmodule, β.val x y' = 0 := by
        intro y' hy'
        have hle : (radicalSpan ρ).toSubmodule ≤ LinearMap.ker (β.val x) := by
          change Submodule.span ℂ _ ≤ _
          rw [Submodule.span_le]
          rintro _ ⟨⟨u, y''⟩, rfl⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker]
          change β.val x (ρ (u : mirabolic (j + 1) F.Carrier) y'' - y'') = 0
          have h1 := β.property u x y''
          rw [ht u x] at h1
          change _ = determinantWeight (normalizedAbsoluteValue T)
            (u : mirabolic (j + 1) F.Carrier).val (-s) * _ at h1
          rw [determinantWeight_radical _ u (-s), one_mul] at h1
          rw [map_sub, h1, sub_self]
        exact LinearMap.mem_ker.mp (hle hy')
      -- eigenvalue of `ρ z` seen through `β x`
      set μ : ℂ := (spectralPoint T.residueCardinality s ^ (j + 1))⁻¹ with hμ
      have heig : ∀ y', β.val x (ρ z y') = (μ / c) * β.val x y' := by
        intro y'
        have h1 : β.val (X z x) (ρ z y') =
            determinantWeight (normalizedAbsoluteValue T) z.val (-s) * β.val x y' :=
          β.property z x y'
        rw [hc x, determinantWeight_leviScalar _ _ hq ϖ hϖ s, map_smul,
          LinearMap.smul_apply, smul_eq_mul] at h1
        rw [div_mul_eq_mul_div, eq_div_iff hc0, mul_comm, h1]
      have hroot : P.eval (μ / c) = 0 := by
        have h1 := apply_aeval_of_eigen (β.val x) heig P y
        rw [hker _ (hP y)] at h1
        exact (mul_eq_zero.mp h1.symm).resolve_right hxy
      apply hsE
      refine Finset.mem_biUnion.mpr ⟨μ / c, ?_, ?_⟩
      · rw [Multiset.mem_toFinset, mem_roots hP0]
        exact hroot
      · rw [Multiset.mem_toFinset, mem_nthRoots (Nat.succ_pos j), div_mul_cancel₀ _ hc0, hμ,
          inv_inv]
    · -- `X` is radical-generated: transfer through `Φ⁻` on both sides.
      let Xs := SmoothRep.of X hs
      let ρs := SmoothRep.of ρ hρ
      let X' := (Derivative.Mirabolic.phiMinusUnnormalized T ψ j).obj Xs
      let ρ' := (Derivative.Mirabolic.phiMinusUnnormalized T ψ j).obj ρs
      let π := Derivative.Mirabolic.phiMinusQuotient T ψ j ρs
      have hT' : IsTower ψ η (Nat.le_of_succ_le h) ρ'.representation (π ∘ₗ q) := by
        refine hT.descend h ρ'.representation π
          (Derivative.Mirabolic.phiMinusQuotient_surjective T ψ j ρs)
          (fun p x => (Derivative.Mirabolic.phiMinusUnnormalized_action T ψ j ρs p x).symm)
          (fun c x => ?_)
        have e := Derivative.Mirabolic.phiMinusQuotient_radical T ψ j ρs
          (Mirabolic.radicalElement c) x
        rw [show (T.mirabolicTheta ψ j (Mirabolic.radicalElement c) : ℂ) =
          ψ.complex (c (Fin.last j)) from
            Derivative.Mirabolic.theta_radicalElement ψ j c] at e
        exact e
      by_cases hX : (⊥ : Subrepresentation X'.representation) = ⊤
      · refine ⟨∅, fun s _ β hβ => ?_⟩
        obtain ⟨β', hβ'⟩ := Derivative.Mirabolic.phiMinusPairingTransfer F T j ψ V A X ρ hs hρ
          hg s β hβ
        exact absurd (forms_eq_zero_of_bot_eq_top_left hX β') hβ'
      have hXi : X'.representation.IsIrreducible :=
        isIrreducible_of_dichotomy
          (Derivative.Mirabolic.phiMinusIrreducible F T j ψ V X hs hirr) hX
      obtain ⟨E, hE⟩ := ih ψ (Nat.le_of_succ_le h) η hadm hirrη ρ' ρ'.representation
        ρ'.isSmooth (π ∘ₗ q) hT' X' X'.representation X'.isSmooth hXi
      refine ⟨E.image (fun w => w / (T.residueCardinality : ℂ)), fun s hsE β hβ => ?_⟩
      have hsE' : spectralPoint T.residueCardinality (s - 1) ∉ E := by
        intro hmem
        apply hsE
        refine Finset.mem_image.mpr ⟨_, hmem, ?_⟩
        have hq' : (T.residueCardinality : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
        rw [spectralPoint_sub_one hq, mul_div_cancel_left₀ _ hq']
      obtain ⟨β', hβ'⟩ := Derivative.Mirabolic.phiMinusPairingTransfer F T j ψ V A X ρ hs hρ
        hg s β hβ
      obtain ⟨eX, hF⟩ := hE (s - 1) hsE' β' hβ'
      exact ⟨nonempty_equiv_of_phiMinus T j (mirabolicFunctionalMultiplicity F T j)
        (mirabolicFunctionalMultiplicity F T (j + 1)) ψ V X hs hirr hXi eX, hF⟩

end Langlands.RankinSelberg.UnequalRankTower
