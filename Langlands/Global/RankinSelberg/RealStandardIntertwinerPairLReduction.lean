import Langlands.Global.RankinSelberg.RealStandardPairingPremises
import Langlands.LocalFactor.RealPairLFactorNormalization
import Langlands.Representation.Archimedean.RealLinkedJacquetPairReduction
import Langlands.Representation.Archimedean.RealStandardParameterUniqueStatement

/-! # Reduction of real pair-factor invariance to positive-weight uniqueness

Normalizing a block list preserves the rank and the standard module as a space of
functions. A nonzero intertwiner between irreducible modules then gives a bijective
intertwiner between their normalized lists. See the paired Markdown.
-/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

private theorem realPositionCharacter_map_positiveWeight (ds : List RealBlock) (p : ℕ) :
    realPositionCharacter (ds.map RealBlock.positiveWeight) p = realPositionCharacter ds p := by
  induction ds generalizing p with
  | nil => rfl
  | cons x ds ih =>
    rcases x with c | d
    · cases p with
      | zero => rfl
      | succ p => exact ih p
    · by_cases h : d.weight < 0
      · rw [List.map_cons, RealBlock.positiveWeight, ite_eq_left h]
        rcases p with _ | _ | p
        · funext x
          simp [realPositionCharacter, realInducedFirstCharacter, ComplexCharacterData.conj]
        · funext x
          simp [realPositionCharacter, realInducedSecondCharacter, ComplexCharacterData.conj]
        · exact ih p
      · rw [List.map_cons, RealBlock.positiveWeight, ite_eq_right h]
        rcases p with _ | _ | p
        · rfl
        · rfl
        · exact ih p

private theorem realInducedBlockAt_abs_map_positiveWeight (ds : List RealBlock) (p : ℕ) :
    (realInducedBlockAt (ds.map RealBlock.positiveWeight) p).map (fun d => |d.weight|) =
      (realInducedBlockAt ds p).map (fun d => |d.weight|) := by
  induction ds generalizing p with
  | nil => rfl
  | cons x ds ih =>
    rcases x with c | d
    · cases p with
      | zero => rfl
      | succ p => exact ih p
    · by_cases h : d.weight < 0
      · rw [List.map_cons, RealBlock.positiveWeight, ite_eq_left h]
        rcases p with _ | _ | p
        · simp [realInducedBlockAt, ComplexCharacterData.conj]
        · rfl
        · exact ih p
      · rw [List.map_cons, RealBlock.positiveWeight, ite_eq_right h]
        rcases p with _ | _ | p
        · rfl
        · rfl
        · exact ih p

private theorem fourierCondition_of_abs_eq (n : ℕ) {ds es : List RealBlock}
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (h : ∀ p, (realInducedBlockAt ds p).map (fun d => |d.weight|) =
      (realInducedBlockAt es p).map (fun d => |d.weight|))
    (hf : f ∈ realStandardModule n ds) (p : ℕ) (e : ComplexCharacterData)
    (he : realInducedBlockAt es p = some e) (k : ℤ) (hk : |k| < |e.weight|)
    (g : Langlands.GeneralLinear n ℝ) : blockFourierCoefficient n p k f g = 0 := by
  have hp := h p
  rw [he, Option.map_some, Option.map_eq_some_iff] at hp
  obtain ⟨d, hd, hw⟩ := hp
  exact ((mem_realStandardModule_iff n ds f).mp hf).2 p d hd k (hw ▸ hk) g

private theorem realStandardModule_map_positiveWeight (n : ℕ) (ds : List RealBlock) :
    realStandardModule n (ds.map RealBlock.positiveWeight) = realStandardModule n ds := by
  have hpos := funext (realPositionCharacter_map_positiveWeight ds)
  have hw := realInducedBlockAt_abs_map_positiveWeight ds
  ext f
  constructor <;> intro hf
  · refine (mem_realStandardModule_iff n ds f).mpr ⟨?_, fourierCondition_of_abs_eq n hw hf⟩
    rw [← hpos]
    exact ((mem_realStandardModule_iff _ _ _).mp hf).1
  · refine (mem_realStandardModule_iff _ _ f).mpr
      ⟨?_, fourierCondition_of_abs_eq n (fun p => (hw p).symm) hf⟩
    rw [hpos]
    exact ((mem_realStandardModule_iff _ _ _).mp hf).1

private theorem flatMap_normalize_eq_map_expand (ds : List RealBlock) :
    ds.flatMap realBlockNormalize = (ds.flatMap realBlockExpand).map RealBlock.positiveWeight := by
  rw [List.map_flatMap]
  rfl

/-- The normalized list gives the same standard module as a space of functions. -/
theorem realStandardModule_flatMap_normalize (n : ℕ) (ds : List RealBlock) :
    realStandardModule n (ds.flatMap realBlockNormalize) = realStandardModule n ds := by
  rw [flatMap_normalize_eq_map_expand, realStandardModule_map_positiveWeight]
  simpa only [List.nil_append] using (realStandardModule_append_flatMap_expand n ds []).symm

private theorem positiveWeight_rank (x : RealBlock) : x.positiveWeight.rank = x.rank := by
  rcases x with c | d
  · rfl
  · by_cases h : d.weight < 0 <;> simp [RealBlock.positiveWeight, h, RealBlock.rank]

private theorem realRank_map_positiveWeight (ds : List RealBlock) :
    realRank (ds.map RealBlock.positiveWeight) = realRank ds := by
  simp only [realRank, List.map_map, Function.comp_def, positiveWeight_rank]

/-- Normalization preserves the total real rank. -/
theorem realRank_flatMap_normalize (ds : List RealBlock) :
    realRank (ds.flatMap realBlockNormalize) = realRank ds := by
  rw [flatMap_normalize_eq_map_expand, realRank_map_positiveWeight, realRank_flatMap_expand]

private theorem positiveWeight_of_nonzero {x : RealBlock} (hx : IsRealBlockNondegenerate x)
    {d : ComplexCharacterData} (hd : x.positiveWeight = .induced d) : 0 < d.weight := by
  rcases x with c | e
  · cases hd
  · by_cases he : e.weight < 0
    · simp only [RealBlock.positiveWeight, ite_eq_left he, RealBlock.induced.injEq] at hd
      rw [← hd]
      exact neg_pos.mpr he
    · simp only [RealBlock.positiveWeight, ite_eq_right he, RealBlock.induced.injEq] at hd
      rw [← hd]
      exact lt_of_le_of_ne (le_of_not_gt he) (Ne.symm hx)

/-- Every induced block of a normalized list has positive weight. -/
theorem weight_pos_of_mem_flatMap_normalize {ds : List RealBlock} {d : ComplexCharacterData}
    (hd : .induced d ∈ ds.flatMap realBlockNormalize) : 0 < d.weight := by
  rw [flatMap_normalize_eq_map_expand, List.mem_map] at hd
  obtain ⟨x, hx, hx'⟩ := hd
  obtain ⟨y, _, hy⟩ := List.mem_flatMap.mp hx
  exact positiveWeight_of_nonzero (isRealBlockNondegenerate_of_mem_expand (x := y) hy) hx'

private theorem injective_of_irreducible {n : ℕ} {ds es : List RealBlock}
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds))
    {T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)}
    (hT : IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T)
    (hT0 : T ≠ 0) : Function.Injective T := by
  have hKer := hT.isGKSubmodule_ker
  rcases hirr.2 _ hKer.1 hKer.2 with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exact (hT0 (LinearMap.ker_eq_top.mp h)).elim

private theorem irreducible_of_eq_module {n : ℕ} {ds es : List RealBlock}
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds))
    (h : realStandardModule n ds = realStandardModule n es) :
    IsIrreducibleGKModule (realStandardRep n es) (realStandardLie n es) := by
  obtain ⟨A, hAs, hA⟩ := RealSurjectiveIntertwinerExists.of_eq h
  have hK := congrArg (fun V => kFiniteFunctions V (unitaryCompact ℝ n)) h
  have hne : Nontrivial (kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :=
    hK ▸ hirr.1
  refine ⟨hne, fun W hWk hWl => ?_⟩
  have hcomap := hirr.2 (W.comap A)
    (fun k f hf => by
      change A (realStandardRep n ds k f) ∈ W
      rw [hA.map_realStandardRep]
      exact hWk k _ hf)
    (fun X f hf => by
      change A (realStandardLie n ds X f) ∈ W
      rw [hA.map_realStandardLie]
      exact hWl X _ hf)
  rw [← Submodule.map_comap_eq_of_surjective hAs W]
  rcases hcomap with hbot | htop
  · left
    rw [hbot, Submodule.map_bot]
  · right
    rw [htop, Submodule.map_top, LinearMap.range_eq_top.mpr hAs]

end Langlands.Archimedean

namespace Langlands.Global.RankinSelbergGlobal

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean

/-- Positive-weight parameter uniqueness implies the real pair-factor comparison. -/
def RealStandardIntertwinerPairLReductionStatement : Prop :=
  RealPositiveWeightStandardUniqueStatement → RealStandardIntertwinerPairLStatement

theorem realStandardIntertwinerPairLReduction : RealStandardIntertwinerPairLReductionStatement := by
  intro hUnique n ds es hd he hdI heI T hT hT0 xs
  have hdM := realStandardModule_flatMap_normalize n ds
  have heM := realStandardModule_flatMap_normalize n es
  have hdI' := irreducible_of_eq_module hdI hdM.symm
  have heI' := irreducible_of_eq_module heI heM.symm
  have hinj : RealInjectiveIntertwinerExists n ds es :=
    ⟨T, injective_of_irreducible hdI hT hT0, hT⟩
  obtain ⟨S, hSi, hS⟩ := RealInjectiveIntertwinerExists.of_eq hdM.symm heM.symm hinj
  have hS0 : S ≠ 0 := by
    intro h
    have := hdI'.1
    obtain ⟨f, hf⟩ := exists_ne (0 : Langlands.Automorphic.realStandardKFinite n
      (ds.flatMap realBlockNormalize))
    apply hf
    apply hSi
    simp [h]
  have hPerm := hUnique n _ _ ((realRank_flatMap_normalize ds).trans hd)
    ((realRank_flatMap_normalize es).trans he)
    (fun _ => weight_pos_of_mem_flatMap_normalize) (fun _ => weight_pos_of_mem_flatMap_normalize)
    hdI' heI' S hS ⟨hSi, hS.surjective heI' hS0⟩
  exact ⟨congrArg ReciprocalEntire.denominator
      (realPairLFactor_eq_of_normalize_perm hPerm (List.Perm.refl _)),
    congrArg ReciprocalEntire.denominator
      (realPairLFactor_eq_of_normalize_perm (List.Perm.refl _) hPerm)⟩

end Langlands.Global.RankinSelbergGlobal
