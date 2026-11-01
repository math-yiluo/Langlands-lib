import Langlands.Representation.Filtration.GrothendieckStatement
import Langlands.Representation.Category.Subquotients

/-!
# Exact classes of actual natural finite filtrations

Adjacent actual inclusions and quotient projections give the exact relations.
The sum telescopes, and a finite permutation does not change it.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

universe uR uG uV uC vC

namespace Langlands.SmoothRep.FiltrationGrothendieckProof

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  {C : Type uC} [Category.{vC} C]
  {F : C ⥤ SmoothRep.{uR, uG, uV} R G} {n : ℕ}

private theorem zero_class (A : SmoothRep.{uR, uG, uV} R G)
    (hA : A.HasFiniteLength) [Subsingleton A.obj] :
    FiniteLengthGrothendieckGroup.ofRepresentation A hA = 0 := by
  let z : A.representation.IntertwiningMap A.representation := 0
  have hz : IsShortExact z z := by
    refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun a => ⟨0, Subsingleton.elim _ _⟩, ?_⟩
    ext a
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    exact iff_of_true ⟨0, Subsingleton.elim _ _⟩ (Subsingleton.elim _ _)
  have h := FiniteLengthGrothendieckGroup.ofRepresentation_shortExact hA hA hA hz
  exact add_left_cancel (show
      FiniteLengthGrothendieckGroup.ofRepresentation A hA +
          FiniteLengthGrothendieckGroup.ofRepresentation A hA =
        FiniteLengthGrothendieckGroup.ofRepresentation A hA + 0 by
    simpa only [add_zero] using h.symm)

/-- Evaluate an ordered natural filtration, derive all piece lengths, and
telescope its adjacent actual short exact sequences. -/
theorem orderedFiltration_sum
    (s : RepFunctorFiltration (F ⋙ toRep) n)
    (P : Fin n → C ⥤ SmoothRep.{uR, uG, uV} R G)
    (hs : s.HasGradedPieces (fun i => P i ⋙ toRep))
    (X : C) (hF : (F.obj X).HasFiniteLength) :
    ∃ hP : ∀ i, ((P i).obj X).HasFiniteLength,
      FiniteLengthGrothendieckGroup.ofRepresentation (F.obj X) hF =
        ∑ i, FiniteLengthGrothendieckGroup.ofRepresentation ((P i).obj X) (hP i) := by
  classical
  let A (j : Fin (n + 1)) := subrepresentation (F.obj X) ((s.step j).obj X)
  have hA (j : Fin (n + 1)) : (A j).HasFiniteLength :=
    hF.of_injective
      (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (hom (subtype (F.obj X) ((s.step j).obj X))))
      (subtype_injective (F.obj X) ((s.step j).obj X))
  let e (i : Fin n) :=
    Representation.equivOfIso ((Classical.choice (hs i)).app X)
  let q (i : Fin n) : (A i.succ).representation.IntertwiningMap
      ((P i).obj X).representation :=
    (e i).toIntertwiningMap.comp
      (((s.step i.castSucc).quotientProjection (s.step i.succ) X).hom)
  have hq (i : Fin n) : Function.Surjective (q i) :=
    (e i).surjective.comp
      ((s.step i.castSucc).quotientProjection_surjective (s.step i.succ) X)
  let hP (i : Fin n) : ((P i).obj X).HasFiniteLength :=
    (hA i.succ).of_surjective
      (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (q i)) (hq i)
  let f (j : Fin (n + 1)) : FiniteLengthGrothendieckGroup.{uR, uG, uV} R G :=
    FiniteLengthGrothendieckGroup.ofRepresentation (A j) (hA j)
  have hgrade (i : Fin n) :
      FiniteLengthGrothendieckGroup.ofRepresentation ((P i).obj X) (hP i) =
        f i.succ - f i.castSucc := by
    let hle := s.step_le_next X i
    let ι : (A i.castSucc).representation.IntertwiningMap (A i.succ).representation :=
      { toLinearMap := Submodule.inclusion hle
        isIntertwining' _ := rfl }
    have hker : LinearMap.ker (q i).toLinearMap =
        LinearMap.ker
          (((s.step i.castSucc).quotientProjection (s.step i.succ) X).hom.toLinearMap) := by
      ext a
      change (e i) ((((s.step i.castSucc).quotientProjection
        (s.step i.succ) X).hom) a) = 0 ↔
          (((s.step i.castSucc).quotientProjection (s.step i.succ) X).hom) a = 0
      exact EmbeddingLike.map_eq_zero_iff
    have hι : IsShortExact
        (A := A i.castSucc) (B := A i.succ) (C := (P i).obj X) ι (q i) := by
      refine ⟨Submodule.inclusion_injective hle, hq i, ?_⟩
      rw [hker]
      change LinearMap.range (Submodule.inclusion hle) =
        LinearMap.ker (((s.step i.castSucc).obj X).toSubmodule.comap
          ((s.step i.succ).obj X).toSubmodule.subtype).mkQ
      rw [Submodule.range_inclusion, Submodule.ker_mkQ]
    have heq := FiniteLengthGrothendieckGroup.ofRepresentation_shortExact
      (hA i.castSucc) (hA i.succ) (hP i) hι
    change f i.succ = f i.castSucc + _ at heq
    rw [heq]
    abel
  have hzero : f 0 = 0 := by
    change FiniteLengthGrothendieckGroup.ofRepresentation
      (subrepresentation (F.obj X) ((s.step 0).obj X)) _ = 0
    simp only [s.zero X]
    have : Subsingleton (subrepresentation (F.obj X) ⊥).obj := by
      change Subsingleton (⊥ : Submodule R (F.obj X).obj)
      exact Submodule.subsingleton_iff_eq_bot.mpr rfl
    exact zero_class _ _
  have hlast : f (Fin.last n) =
      FiniteLengthGrothendieckGroup.ofRepresentation (F.obj X) hF := by
    change FiniteLengthGrothendieckGroup.ofRepresentation
      (subrepresentation (F.obj X) ((s.step (Fin.last n)).obj X)) _ = _
    simp only [s.top X]
    apply FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv _ hF
    exact (hom (subtype (F.obj X) ⊤)).ofBijective
      ⟨subtype_injective (F.obj X) ⊤, fun a => ⟨⟨a, Submodule.mem_top⟩, rfl⟩⟩
  refine ⟨hP, ?_⟩
  symm
  calc
    (∑ i, FiniteLengthGrothendieckGroup.ofRepresentation ((P i).obj X) (hP i)) =
        ∑ i : Fin n, (f i.succ - f i.castSucc) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hgrade i
    _ = f (Fin.last n) - f 0 := by
      rw [Finset.sum_sub_distrib]
      calc
        (∑ i : Fin n, f i.succ) - ∑ i : Fin n, f i.castSucc =
            (f 0 + ∑ i : Fin n, f i.succ) -
              ((∑ i : Fin n, f i.castSucc) + f 0) := by abel
        _ = ((∑ i : Fin n, f i.castSucc) + f (Fin.last n)) -
            ((∑ i : Fin n, f i.castSucc) + f 0) := by
          rw [← Fin.sum_univ_succ, Fin.sum_univ_castSucc]
        _ = f (Fin.last n) - f 0 := by abel
    _ = FiniteLengthGrothendieckGroup.ofRepresentation (F.obj X) hF := by
      rw [hzero, hlast, sub_zero]

end Langlands.SmoothRep.FiltrationGrothendieckProof

namespace Langlands.SmoothRep

variable (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]

/-- Every actual natural gluing gives the sum of its smooth pieces in exact
finite-length K0, with their finite lengths derived from the ambient value. -/
theorem filtrationGrothendieckStatement :
    FiltrationGrothendieckStatement.{uR, uG, uV, uC, vC} R G := by
  classical
  intro C _ F n P h X hF
  obtain ⟨e, s, hs⟩ := h
  obtain ⟨hPe, heq⟩ := FiltrationGrothendieckProof.orderedFiltration_sum s
    (fun i => P (e i)) hs X hF
  let hP (i : Fin n) : ((P i).obj X).HasFiniteLength := by
    simpa only [e.apply_symm_apply] using hPe (e.symm i)
  refine ⟨hP, heq.trans ?_⟩
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end Langlands.SmoothRep
