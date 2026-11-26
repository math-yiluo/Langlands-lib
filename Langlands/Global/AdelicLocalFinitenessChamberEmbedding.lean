import Langlands.Global.AdelicLocalFinitenessOrthantCombination

/-! # The weighted Siegel norm is controlled by boxes and residuals of components

For a finite family of components `φ_P`, each invariant under `P₀(F) U_{J_P}(𝔸)`, whose sum is
`f` almost everywhere for the Siegel weight, the Siegel norm of `f` is bounded by the norms of
the components on boxes and of their difference residuals on positive regions, for all
sufficiently large rates (Bernstein–Lapid §§7.5–7.7).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Global.StandardConstantTerm

open Langlands.GroupScheme AdelicSubgroupPoints AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

private instance : IsClosedImmersion (Standard.parabolicHom i ν ∅).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom i ν ∅

private instance : IsAffine (Standard.parabolicScheme i ν ∅).X.left :=
  isAffine_of_isAffineHom (Standard.parabolicHom i ν ∅).hom.hom.left

variable {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  [Fintype (simpleRelativeRoots i ν)] [DecidableEq (simpleRelativeRoots i ν)] {r : ℕ}
  (e : RealCharacterDual F (Standard.parabolicScheme i ν ∅) ≃L[ℝ]
    ((simpleRelativeRoots i ν → ℝ) × (Fin r → ℝ)))

/-- The box `{0 < htₖ ≤ mₖ for all directions k}` of the orthant heights. -/
def orthantBox {X D : Type*} {r : ℕ} (c : X → (D → ℝ) × (Fin r → ℝ)) (τ : D → ℝ) (J : D → Prop)
    (ε : Fin r → Bool) (m : ({β : D // ¬ J β} ⊕ Fin r) → ℕ) : Set X :=
  {g | ∀ k, 0 < orthantHeight c τ J ε k g ∧ orthantHeight c τ J ε k g ≤ m k}

open scoped Classical in
include hG hi hν in
/-- **Siegel norm from boxes and residuals.** Let `a_β`, `z_j` shift the chamber coordinates by
unit vectors, with `a_β` (for `β ∉ J`) and `z_j` commuting with `L_J(𝔸)` and normalizing
`U_J(𝔸)` for every `J ⊆ Δ`. For a finite family of index sets `J_P ⊆ Δ`, thresholds `τ` and a
coefficient bound `M`, there is `R₀` such that for all rates at least `R₀` and all coefficient
families bounded by `M` there is `C ≥ 0` with the following property. If `f` is almost
everywhere the sum of measurable components `φ_P`, each invariant under `Λ₀ ⊔ U_{J_P}(𝔸)`,
whose boxes and residuals are square integrable for the Siegel weight, then `f` is square
integrable for the Siegel weight and its norm is at most `C` times the sum over the components
and orthants of the box norms and residual norms. -/
theorem exists_chamberEmbedding (a : simpleRelativeRoots i ν → AdelicGroupPoints F G)
    (z : Fin r → AdelicGroupPoints F G)
    (hca : ∀ β g, chamberCoords hK e (a β * g) = chamberCoords hK e g + (Pi.single β 1, 0))
    (hcz : ∀ j g, chamberCoords hK e (z j * g) = chamberCoords hK e g + (0, Pi.single j 1))
    (haN : ∀ (β : simpleRelativeRoots i ν) (J : Set (characterLattice T)),
      J ⊆ simpleRelativeRoots i ν → β.val ∉ J →
      (∀ x ∈ adelicPoints F G (standardLevi i ν J), a β * x = x * a β) ∧
      (∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
        a β * w * (a β)⁻¹ ∈ adelicPoints F G (standardUnipotent i ν J)) ∧
      (∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
        (a β)⁻¹ * w * a β ∈ adelicPoints F G (standardUnipotent i ν J)))
    (hzN : ∀ (j : Fin r) (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
      (∀ x ∈ adelicPoints F G (standardLevi i ν J), z j * x = x * z j) ∧
      (∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
        z j * w * (z j)⁻¹ ∈ adelicPoints F G (standardUnipotent i ν J)) ∧
      (∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
        (z j)⁻¹ * w * z j ∈ adelicPoints F G (standardUnipotent i ν J)))
    {Idx : Type*} [Fintype Idx] (J : Idx → Set (characterLattice T))
    (hJ : ∀ P, J P ⊆ simpleRelativeRoots i ν) (τ : simpleRelativeRoots i ν → ℝ) (M : ℝ) :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ (ra : simpleRelativeRoots i ν → ℝ) (rb : Fin r → ℝ),
      (∀ β, R₀ ≤ ra β) → (∀ j, R₀ ≤ rb j) →
    ∀ (m : ∀ (P : Idx) (_ε : Fin r → Bool),
        ({β : simpleRelativeRoots i ν // ¬ (fun β : simpleRelativeRoots i ν => β.val ∈ J P) β} ⊕
          Fin r) → ℕ)
      (p : ∀ P ε k, Fin (m P ε k) → ℂ), (∀ P ε k, ∑ q, ‖p P ε k q‖ ≤ M) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : AdelicGroupPoints F G → ℂ) (φ : Idx → AdelicGroupPoints F G → ℂ),
      Measurable f → (∀ P, Measurable (φ P)) →
      (∀ P, ∀ h ∈ cosetSubgroup F G i ν (J P), ∀ g, φ P (h * g) = φ P g) →
      f =ᵐ[domainWeightedHaar F G i ν (siegelWeight (chamberCoords hK e) ra rb τ)]
        (fun g => ∑ P, φ P g) →
      (∀ P ε, MemLp (φ P) 2 ((domainWeightedHaar F G i ν
        (siegelWeight (chamberCoords hK e) ra rb τ)).restrict
          (orthantBox (chamberCoords hK e) τ (fun β => β.val ∈ J P) ε (m P ε)))) →
      (∀ P ε k, MemLp (residualFun F G (orthantShift a z (fun β => β.val ∈ J P) ε k)
          (p P ε k) (φ P)) 2 ((domainWeightedHaar F G i ν
            (siegelWeight (chamberCoords hK e) ra rb τ)).restrict
              (orthantPos (chamberCoords hK e) τ (fun β => β.val ∈ J P) ε))) →
      MemLp f 2 (domainWeightedHaar F G i ν (siegelWeight (chamberCoords hK e) ra rb τ)) ∧
      lpNorm f 2 (domainWeightedHaar F G i ν (siegelWeight (chamberCoords hK e) ra rb τ)) ≤
        C * ∑ P, ∑ ε : Fin r → Bool,
          (lpNorm (φ P) 2 ((domainWeightedHaar F G i ν
            (siegelWeight (chamberCoords hK e) ra rb τ)).restrict
              (orthantBox (chamberCoords hK e) τ (fun β => β.val ∈ J P) ε (m P ε))) +
          ∑ k, lpNorm (residualFun F G (orthantShift a z (fun β => β.val ∈ J P) ε k)
            (p P ε k) (φ P)) 2 ((domainWeightedHaar F G i ν
              (siegelWeight (chamberCoords hK e) ra rb τ)).restrict
                (orthantPos (chamberCoords hK e) τ (fun β => β.val ∈ J P) ε))) := by
  classical
  set c := chamberCoords hK e with hc
  set ν₀ : Measure (AdelicGroupPoints F G) := (Measure.haar : Measure (AdelicGroupPoints F G)).restrict
    (LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
      (isDiscrete_minimalParabolicImage F G i ν)) with hν₀
  have hdef : ∀ W, domainWeightedHaar F G i ν W = ν₀.withDensity W := fun W => rfl
  have hcm : Measurable c := (continuous_chamberCoords hK e).measurable
  have hR (P : Idx) (ε : Fin r → Bool) := exists_orthantSlabEstimate hK hG hi hν e a z hca hcz (hJ P)
    (fun β hβ => (haN β (J P) (hJ P) hβ).1) (fun β hβ => (haN β (J P) (hJ P) hβ).2.1)
    (fun β hβ => (haN β (J P) (hJ P) hβ).2.2) (fun j => (hzN j (J P) (hJ P)).1)
    (fun j => (hzN j (J P) (hJ P)).2.1) (fun j => (hzN j (J P) (hJ P)).2.2) τ ε M
  choose R hRest using hR
  have hR₀ : 0 ≤ ∑ P, ∑ ε, |R P ε| := by positivity
  refine ⟨∑ P, ∑ ε, |R P ε|, hR₀, fun ra rb hra hrb m p hp => ?_⟩
  have hRle (P : Idx) (ε : Fin r → Bool) : R P ε ≤ ∑ P, ∑ ε, |R P ε| :=
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun ε => |R P ε|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ ε)).trans
      (Finset.single_le_sum (f := fun P => ∑ ε, |R P ε|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ P)))
  have hest (P : Idx) (ε : Fin r → Bool) := hRest P ε ra rb (fun β => (hRle P ε).trans (hra β))
    (fun j => (hRle P ε).trans (hrb j)) (m P ε) (p P ε) (hp P ε)
  choose Cpe hCpe1 hCpe using hest
  set Ctot := ∑ P, ∑ ε, Cpe P ε with hCtot
  have hCpe_le (P : Idx) (ε : Fin r → Bool) : Cpe P ε ≤ Ctot :=
    (Finset.single_le_sum (f := fun ε => Cpe P ε)
      (fun ε _ => (zero_le_one.trans (hCpe1 P ε))) (Finset.mem_univ ε)).trans
      (Finset.single_le_sum (f := fun P => ∑ ε, Cpe P ε)
        (fun P _ => Finset.sum_nonneg fun ε _ => zero_le_one.trans (hCpe1 P ε)) (Finset.mem_univ P))
  have hCtot0 : 0 ≤ Ctot := Finset.sum_nonneg fun P _ => Finset.sum_nonneg fun ε _ =>
    zero_le_one.trans (hCpe1 P ε)
  have hrb0 : ∀ j, 0 ≤ rb j := fun j => hR₀.trans (hrb j)
  refine ⟨Real.exp (2 * ∑ j, rb j) * Ctot, by positivity,
    fun f φ hf hφm hφH hdec hbox hres => ?_⟩
  have hhtm (P : Idx) (ε : Fin r → Bool) (k) :
      Measurable (orthantHeight c τ (fun β => β.val ∈ J P) ε k) := by
    rcases k with β | j
    · exact (((measurable_pi_apply β.1).comp measurable_fst).comp hcm).sub_const _
    · refine Measurable.add_const ?_ _
      unfold orthantCoord
      by_cases hε : ε j
      · simp only [hε, ↓reduceIte]
        exact ((measurable_pi_apply j).comp measurable_snd).comp hcm
      · simp only [hε, Bool.false_eq_true, ↓reduceIte]
        exact (((measurable_pi_apply j).comp measurable_snd).comp hcm).neg
  have hboxm (P : Idx) (ε : Fin r → Bool) : MeasurableSet
      {g | ∀ k, 0 < orthantHeight c τ (fun β => β.val ∈ J P) ε k g ∧
        orthantHeight c τ (fun β => β.val ∈ J P) ε k g ≤ m P ε k} := by
    have h : {g | ∀ k, 0 < orthantHeight c τ (fun β => β.val ∈ J P) ε k g ∧
        orthantHeight c τ (fun β => β.val ∈ J P) ε k g ≤ m P ε k} =
        ⋂ k, ({g | 0 < orthantHeight c τ (fun β => β.val ∈ J P) ε k g} ∩
          {g | orthantHeight c τ (fun β => β.val ∈ J P) ε k g ≤ m P ε k}) := by
      ext g; simp
    rw [h]
    exact MeasurableSet.iInter fun k =>
      (measurableSet_lt measurable_const (hhtm P ε k)).inter
        (measurableSet_le (hhtm P ε k) measurable_const)
  have hboxsub (P : Idx) (ε : Fin r → Bool) :
      {g | ∀ k, 0 < orthantHeight c τ (fun β => β.val ∈ J P) ε k g ∧
        orthantHeight c τ (fun β => β.val ∈ J P) ε k g ≤ m P ε k} ⊆
        orthantPos c τ (fun β => β.val ∈ J P) ε := fun g hg k => (hg k).1
  simp only [hdef] at hdec hbox hres hCpe ⊢
  have hP (P : Idx) := siegel_estimate_of_orthants ν₀ hcm ra rb hrb0 τ (fun β => β.val ∈ J P)
    (I := fun _ => {β : simpleRelativeRoots i ν // ¬ (fun β : simpleRelativeRoots i ν => β.val ∈ J P) β} ⊕ Fin r)
    (fun ε => {g | ∀ k, 0 < orthantHeight c τ (fun β => β.val ∈ J P) ε k g ∧
        orthantHeight c τ (fun β => β.val ∈ J P) ε k g ≤ m P ε k})
    (hboxm P) (hboxsub P) (Cpe P) (fun ε => zero_le_one.trans (hCpe1 P ε)) (hφm P)
    (fun ε k => residualFun F G (orthantShift a z (fun β => β.val ∈ J P) ε k) (p P ε k) (φ P))
    (fun ε hb hr => hCpe P ε (hφm P) (hφH P) hb hr) (hbox P) (hres P)
  choose hmemP hboundP using hP
  have hsum_mem : MemLp (fun g => ∑ P, φ P g) 2 (ν₀.withDensity (siegelWeight c ra rb τ)) := by
    have := memLp_finsetSum' Finset.univ fun P _ => hmemP P
    convert this using 1
    funext g
    simp [Finset.sum_apply]
  refine ⟨hsum_mem.ae_eq hdec.symm, ?_⟩
  have h1 : lpNorm f 2 (ν₀.withDensity (siegelWeight c ra rb τ)) ≤
      ∑ P, lpNorm (φ P) 2 (ν₀.withDensity (siegelWeight c ra rb τ)) := by
    unfold lpNorm
    rw [eLpNorm_congr_ae hdec, ← ENNReal.toReal_sum fun P _ => (hmemP P).eLpNorm_ne_top]
    refine ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun P _ => (hmemP P).eLpNorm_ne_top) ?_
    have h := eLpNorm_sum_le («μ» := ν₀.withDensity (siegelWeight c ra rb τ)) (p := 2)
      (s := Finset.univ) (f := φ) (by norm_num)
    convert h using 2
    funext g
    simp [Finset.sum_apply]
  refine h1.trans ?_
  have hexp : 0 ≤ Real.exp (2 * ∑ j, rb j) := (Real.exp_pos _).le
  have hnn (P : Idx) (ε : Fin r → Bool) : 0 ≤ lpNorm (φ P) 2 ((ν₀.withDensity (siegelWeight c ra rb τ)).restrict
      {g | ∀ k, 0 < orthantHeight c τ (fun β => β.val ∈ J P) ε k g ∧
        orthantHeight c τ (fun β => β.val ∈ J P) ε k g ≤ m P ε k}) +
      ∑ k, lpNorm (residualFun F G (orthantShift a z (fun β => β.val ∈ J P) ε k) (p P ε k) (φ P)) 2
        ((ν₀.withDensity (siegelWeight c ra rb τ)).restrict
          (orthantPos c τ (fun β => β.val ∈ J P) ε)) :=
    add_nonneg lpNorm_nonneg (Finset.sum_nonneg fun _ _ => lpNorm_nonneg)
  have key (P : Idx) : lpNorm (φ P) 2 (ν₀.withDensity (siegelWeight c ra rb τ)) ≤
      Real.exp (2 * ∑ j, rb j) * Ctot * ∑ ε : Fin r → Bool,
        (lpNorm (φ P) 2 ((ν₀.withDensity (siegelWeight c ra rb τ)).restrict
          {g | ∀ k, 0 < orthantHeight c τ (fun β => β.val ∈ J P) ε k g ∧
            orthantHeight c τ (fun β => β.val ∈ J P) ε k g ≤ m P ε k}) +
        ∑ k, lpNorm (residualFun F G (orthantShift a z (fun β => β.val ∈ J P) ε k) (p P ε k)
          (φ P)) 2 ((ν₀.withDensity (siegelWeight c ra rb τ)).restrict
            (orthantPos c τ (fun β => β.val ∈ J P) ε))) := by
    refine (hboundP P).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hexp
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun ε _ => mul_le_mul_of_nonneg_right (hCpe_le P ε) (hnn P ε)
  calc ∑ P, lpNorm (φ P) 2 (ν₀.withDensity (siegelWeight c ra rb τ))
      ≤ ∑ P, Real.exp (2 * ∑ j, rb j) * Ctot * ∑ ε : Fin r → Bool,
        (lpNorm (φ P) 2 ((ν₀.withDensity (siegelWeight c ra rb τ)).restrict
          {g | ∀ k, 0 < orthantHeight c τ (fun β => β.val ∈ J P) ε k g ∧
            orthantHeight c τ (fun β => β.val ∈ J P) ε k g ≤ m P ε k}) +
        ∑ k, lpNorm (residualFun F G (orthantShift a z (fun β => β.val ∈ J P) ε k) (p P ε k)
          (φ P)) 2 ((ν₀.withDensity (siegelWeight c ra rb τ)).restrict
            (orthantPos c τ (fun β => β.val ∈ J P) ε))) := Finset.sum_le_sum fun P _ => key P
    _ = _ := (Finset.mul_sum _ _ _).symm

end Langlands.Global.StandardConstantTerm
