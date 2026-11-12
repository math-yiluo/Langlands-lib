import Langlands.Representation.Exponents.SplitComponentDecomposition
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof
import Langlands.Representation.Filtration.SubsingletonProof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Smooth.Factorization.MultiplicityDefinitions

/-! # Exclusion of an isolated exponent from quotients of a filtered representation

Let `V` be an admissible representation of a locally profinite group `M`, and let a central
map `ι : A → M` act on it. Suppose `V` has a finite filtration whose graded pieces carry no
generalized `ι`-eigencharacter `χ`, except one irreducible piece. Suppose a map `Φ` from `V`
to a representation carrying `χ` is nonzero on a subrepresentation `W`. Then `χ` is not a
generalized eigencharacter of any smooth quotient of `V` that kills `W`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.InducedTwistExclusion

universe uM uA uV uW uX

variable {M : Type uM} [Group M] [TopologicalSpace M]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

theorem isAdmissible_subrepresentation {π : Representation ℂ M V} (hπ : IsAdmissible π)
    (S : Subrepresentation π) : IsAdmissible S.toRepresentation :=
  isAdmissible_of_injective (ProductFactorization.subrepresentationInclusion S) Subtype.val_injective hπ

theorem isSmooth_subrepresentation {π : Representation ℂ M V} (hπ : IsSmooth π)
    (S : Subrepresentation π) : IsSmooth S.toRepresentation := by
  intro v
  obtain ⟨K, hK⟩ := hπ (v : V)
  refine ⟨K, ?_⟩
  change ∀ k : K, S.toRepresentation (k : M) v = v
  intro k
  exact Subtype.ext (hK k)

variable [NonarchimedeanGroup M] [WeaklyLocallyCompactSpace M]
  {A : Type uA} [Group A] (ι : A →* M) (hι : ∀ t : A, ι t ∈ Subgroup.center M)

/-- An intertwiner from an admissible representation to a smooth one maps the
generalized `χ`-weight space onto the generalized `χ`-weight vectors of its image. -/
theorem exists_mem_generalizedWeightSpace_map_eq {π : Representation ℂ M V}
    {σ : Representation ℂ M W} (hπ : IsAdmissible π) (hσ : IsSmooth σ)
    (f : π.IntertwiningMap σ) (χ : A →* ℂˣ) (x : V)
    (hx : f x ∈ generalizedWeightSpace σ ι χ hι) :
    ∃ x' ∈ generalizedWeightSpace π ι χ hι, f x' = f x := by
  have htop := generalizedWeightSpace_iSup_eq_top π ι hι hπ.1
    (CentralDecomposition.admissible_centerFinite π hπ)
  have hxmem : x ∈ ⨆ θ : A →* ℂˣ, (generalizedWeightSpace π ι θ hι).toSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  rw [iSup_split_single _ χ] at hxmem
  obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.mp hxmem
  refine ⟨x1, hx1, ?_⟩
  have hle : Submodule.map f.toLinearMap
      (⨆ (θ : A →* ℂˣ) (_ : θ ≠ χ), (generalizedWeightSpace π ι θ hι).toSubmodule) ≤
      ⨆ (θ : A →* ℂˣ) (_ : θ ≠ χ), (generalizedWeightSpace σ ι θ hι).toSubmodule := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun θ => ?_
    rw [Submodule.map_iSup]
    refine iSup_mono fun _ => ?_
    rintro _ ⟨v, hv, rfl⟩
    exact map_mem_generalizedWeightSpace ι θ hι f hv
  have hfx2 := hle ⟨x2, hx2, rfl⟩
  have hmem : f x2 ∈ (generalizedWeightSpace σ ι χ hι).toSubmodule := by
    have h := Submodule.sub_mem _ hx (map_mem_generalizedWeightSpace ι χ hι f hx1)
    simpa only [map_add, add_sub_cancel_left] using h
  have h0 : f x2 = 0 :=
    (Submodule.disjoint_def.mp ((generalizedWeightSpace_independent σ ι hι hσ) χ)) _ hmem hfx2
  change f x1 = f (x1 + x2)
  rw [map_add, h0, add_zero]

/-- A generalized `χ`-eigencharacter of a smooth quotient of an admissible representation
is a generalized `χ`-eigencharacter of the source. -/
theorem isGeneralizedEigencharacter_of_surjective (hι : ∀ t : A, ι t ∈ Subgroup.center M) {π : Representation ℂ M V}
    {σ : Representation ℂ M W} (hπ : IsAdmissible π) (hσ : IsSmooth σ)
    (f : π.IntertwiningMap σ) (hf : Function.Surjective f) (χ : A →* ℂˣ)
    (h : IsGeneralizedEigencharacter (σ.comp ι) χ) :
    IsGeneralizedEigencharacter (π.comp ι) χ := by
  rw [← generalizedWeightSpace_ne_bot_iff ι χ hι hσ] at h
  rw [← generalizedWeightSpace_ne_bot_iff ι χ hι hπ.1]
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp
    (fun h' => h (Subrepresentation.toSubmodule_injective h'))
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨x', hx', hfx'⟩ := exists_mem_generalizedWeightSpace_map_eq ι hι hπ hσ f χ x hy
  intro hbot
  rw [hbot] at hx'
  have hx'0 : x' = 0 := hx'
  rw [hx'0, map_zero] at hfx'
  exact hy0 hfx'.symm


end Langlands.InducedTwistExclusion

namespace Langlands.InducedTwistExclusion

variable {M : Type uM} [Group M] [TopologicalSpace M] [NonarchimedeanGroup M]
  [WeaklyLocallyCompactSpace M] {A : Type uA} [Group A] (ι : A →* M)
  (hι : ∀ t : A, ι t ∈ Subgroup.center M)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

include hι in
/-- A generalized weight vector of a smooth representation lies in one uniform character
space of the restricted action. -/
theorem exists_mem_characterSpace_of_mem_generalizedWeightSpace {π : Representation ℂ M V}
    (hπ : IsSmooth π) (χ : A →* ℂˣ) {v : V} (hv : v ∈ generalizedWeightSpace π ι χ hι) :
    ∃ d : ℕ, v ∈ characterSpace (π.comp ι) χ d := by
  obtain ⟨d, hd⟩ := (mem_generalizedWeightSpace_of_isSmooth ι χ hι hπ v).mp hv
  exact ⟨d, (mem_characterSpace (π.comp ι) χ d v).mpr hd⟩

/-- The same statement for a vector of an invariant subspace, read in the ambient space. -/
theorem exists_coe_mem_characterSpace {π : Representation ℂ M V} (S : Subrepresentation π)
    (hS : IsSmooth S.toRepresentation) (χ : A →* ℂˣ) {x : S.toSubmodule}
    (hx : x ∈ generalizedWeightSpace S.toRepresentation ι χ hι) :
    ∃ d : ℕ, (x : V) ∈ characterSpace (π.comp ι) χ d := by
  obtain ⟨d, hd⟩ := exists_mem_characterSpace_of_mem_generalizedWeightSpace ι hι hS χ hx
  exact ⟨d, (mem_characterSpace_subrepresentation_comp π S ι χ d x).mp hd⟩

variable {E : Rep.{uV} ℂ M} {n : ℕ}

omit [TopologicalSpace M] [NonarchimedeanGroup M] [WeaklyLocallyCompactSpace M] in
/-- One step down a filtration: a uniform `χ`-vector of the next step lies in the current
step when the graded piece between them has no generalized eigencharacter `χ`. -/
theorem mem_castSucc_of_mem_succ (s : ObjectRepFiltration E n) (j : Fin n) (χ : A →* ℂˣ)
    (hj : ¬ IsGeneralizedEigencharacter ((s.gradedRepresentation j).ρ.comp ι) χ)
    {v : E} (hv : v ∈ s.subrepresentation j.succ) {d : ℕ}
    (hvd : v ∈ characterSpace (E.ρ.comp ι) χ d) : v ∈ s.subrepresentation j.castSucc := by
  have hv' : (⟨v, hv⟩ : (s.subrepresentation j.succ).toSubmodule) ∈
      characterSpace ((s.subrepresentation j.succ).toRepresentation.comp ι) χ d :=
    (mem_characterSpace_subrepresentation_comp E.ρ _ ι χ d _).mpr hvd
  have himg := map_mem_characterSpace_of_intertwining
    (π := (s.subrepresentation j.succ).toRepresentation.comp ι)
    (σ := (s.gradedRepresentation j).ρ.comp ι)
    (s.gradedProjection j).hom.toLinearMap
    (fun t => ((s.gradedProjection j).hom.isIntertwining' (ι t)).symm) χ d hv'
  have hbot : characterSpace ((s.gradedRepresentation j).ρ.comp ι) χ d = ⊥ := by
    by_contra h
    exact hj ⟨d, h⟩
  rw [hbot] at himg
  exact (s.gradedProjection_eq_zero_iff j ⟨v, hv⟩).mp himg

omit [TopologicalSpace M] [NonarchimedeanGroup M] [WeaklyLocallyCompactSpace M] in
/-- A uniform `χ`-vector lies in the step just above an isolated grade `j₀`. -/
theorem mem_succ_of_mem_characterSpace (s : ObjectRepFiltration E n) (j₀ : Fin n)
    (χ : A →* ℂˣ)
    (hother : ∀ j, j ≠ j₀ → ¬ IsGeneralizedEigencharacter ((s.gradedRepresentation j).ρ.comp ι) χ)
    {v : E} {d : ℕ} (hvd : v ∈ characterSpace (E.ρ.comp ι) χ d) :
    v ∈ s.subrepresentation j₀.succ := by
  have key : ∀ m (hm : m ≤ n), j₀.val + 1 ≤ m →
      v ∈ s.subrepresentation ⟨m, Nat.lt_succ_of_le hm⟩ := by
    intro m hm
    induction hm using Nat.decreasingInduction with
    | self =>
      intro _
      have h := s.subrepresentation_last
      rw [show (⟨n, Nat.lt_succ_of_le le_rfl⟩ : Fin (n + 1)) = Fin.last n from rfl, h]
      trivial
    | of_succ k hk ih =>
      intro hle
      have hv := ih (by omega)
      have hne : (⟨k, hk⟩ : Fin n) ≠ j₀ := by
        intro h
        rw [← h] at hle
        simp at hle
      exact mem_castSucc_of_mem_succ ι s ⟨k, hk⟩ χ (hother _ hne) hv hvd
  exact key (j₀.val + 1) j₀.isLt le_rfl

omit [TopologicalSpace M] [NonarchimedeanGroup M] [WeaklyLocallyCompactSpace M] in
/-- A uniform `χ`-vector of the step below an isolated grade `j₀` is zero. -/
theorem eq_zero_of_mem_castSucc (s : ObjectRepFiltration E n) (j₀ : Fin n)
    (χ : A →* ℂˣ)
    (hother : ∀ j, j ≠ j₀ → ¬ IsGeneralizedEigencharacter ((s.gradedRepresentation j).ρ.comp ι) χ)
    {v : E} {d : ℕ} (hvd : v ∈ characterSpace (E.ρ.comp ι) χ d)
    (hv : v ∈ s.subrepresentation j₀.castSucc) : v = 0 := by
  have key : ∀ m (hm : m ≤ j₀.val),
      v ∈ s.subrepresentation ⟨m, by omega⟩ → v = 0 := by
    intro m
    induction m with
    | zero =>
      intro _ h0
      have h := s.subrepresentation_zero
      rw [show (⟨0, by omega⟩ : Fin (n + 1)) = 0 from rfl, h] at h0
      exact h0
    | succ k ih =>
      intro hk hvk
      have hne : (⟨k, by omega⟩ : Fin n) ≠ j₀ := by
        intro h
        rw [← h] at hk
        simp at hk
      exact ih (by omega)
        (mem_castSucc_of_mem_succ ι s ⟨k, by omega⟩ χ (hother _ hne) hvk hvd)
  exact key j₀.val le_rfl hv

include hι in
/-- **Exclusion from an isolated irreducible grade.** Let `E` be admissible, with a finite
filtration whose graded pieces other than `j₀` carry no generalized eigencharacter `χ` of the
central map `ι`, and whose grade `j₀` is irreducible. Let `Φ : E → σ` be a map to an
irreducible smooth representation carrying `χ`, nonzero on an invariant subspace `W`. Then
every smooth quotient `q : E ↠ τ` that kills `W` has no generalized eigencharacter `χ`. -/
theorem not_isGeneralizedEigencharacter_of_isolatedGrade (hE : IsAdmissible E.ρ)
    (s : ObjectRepFiltration E n) (j₀ : Fin n) (χ : A →* ℂˣ)
    (hother : ∀ j, j ≠ j₀ → ¬ IsGeneralizedEigencharacter ((s.gradedRepresentation j).ρ.comp ι) χ)
    (hgr : Representation.IsIrreducible (s.gradedRepresentation j₀).ρ)
    {X : Type uX} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ M X) (hσ : IsSmooth σ)
    (hσirr : Representation.IsIrreducible σ)
    (hσχ : IsGeneralizedEigencharacter (σ.comp ι) χ)
    (Φ : E.ρ.IntertwiningMap σ) (Wsub : Subrepresentation E.ρ) (hW : ∃ w ∈ Wsub, Φ w ≠ 0)
    {Y : Type uW} [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ M Y) (hτ : IsSmooth τ)
    (q : E.ρ.IntertwiningMap τ) (hq : Function.Surjective q) (hqW : ∀ w ∈ Wsub, q w = 0) :
    ¬ IsGeneralizedEigencharacter (τ.comp ι) χ := by
  have := hσirr
  have := hgr
  set S0 := s.subrepresentation j₀.castSucc with hS0
  set S1 := s.subrepresentation j₀.succ with hS1
  -- Step 1: `Φ` vanishes on the step below the isolated grade.
  have hΦ0 : ∀ u ∈ S0, Φ u = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu, hΦu⟩ := hcon
    let g := Φ.comp (ProductFactorization.subrepresentationInclusion S0)
    have hg : g ≠ 0 := by
      intro h
      apply hΦu
      have := congrArg (fun f : S0.toRepresentation.IntertwiningMap σ => f ⟨u, hu⟩) h
      exact this
    have hsurj : Function.Surjective g :=
      (Representation.IsIrreducible.surjective_or_eq_zero (ρ := σ) g).resolve_right hg
    obtain ⟨d, hd⟩ := isGeneralizedEigencharacter_of_surjective ι hι
      (isAdmissible_subrepresentation hE S0) hσ g hsurj χ hσχ
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hd
    have hxE := (mem_characterSpace_subrepresentation_comp E.ρ S0 ι χ d x).mp hx
    exact hx0 (Subtype.ext (eq_zero_of_mem_castSucc ι s j₀ χ hother hxE x.property))
  -- Step 2: `Φ` is nonzero on a vector of `W` in the step above the isolated grade.
  have hW1 : ∃ w ∈ Wsub, w ∈ S1 ∧ Φ w ≠ 0 := by
    obtain ⟨w, hw, hΦw⟩ := hW
    let g := Φ.comp (ProductFactorization.subrepresentationInclusion Wsub)
    have hg : g ≠ 0 := by
      intro h
      apply hΦw
      exact congrArg (fun f : Wsub.toRepresentation.IntertwiningMap σ => f ⟨w, hw⟩) h
    have hsurj : Function.Surjective g :=
      (Representation.IsIrreducible.surjective_or_eq_zero (ρ := σ) g).resolve_right hg
    have hne := (generalizedWeightSpace_ne_bot_iff ι χ hι hσ).mpr hσχ
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp
      (fun h => hne (Subrepresentation.toSubmodule_injective h))
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨x', hx', hgx'⟩ := exists_mem_generalizedWeightSpace_map_eq ι hι
      (isAdmissible_subrepresentation hE Wsub) hσ g χ x hy
    obtain ⟨d, hd⟩ := exists_coe_mem_characterSpace ι hι Wsub
      (isAdmissible_subrepresentation hE Wsub).1 χ hx'
    refine ⟨x', x'.property, mem_succ_of_mem_characterSpace ι s j₀ χ hother hd, ?_⟩
    change g x' ≠ 0
    rw [hgx']
    exact hy0
  -- Step 3: `W ∩ S1` maps onto the isolated grade.
  have hcover : ∀ v ∈ S1, ∃ w' ∈ Wsub, w' ∈ S1 ∧ v - w' ∈ S0 := by
    obtain ⟨w, hw, hw1, hΦw⟩ := hW1
    let T : Subrepresentation E.ρ := Wsub ⊓ S1
    let incl : T.toRepresentation.IntertwiningMap S1.toRepresentation :=
      { toLinearMap := Submodule.inclusion (inf_le_right : T.toSubmodule ≤ S1.toSubmodule)
        isIntertwining' := fun _ => rfl }
    let g := (s.gradedProjection j₀).hom.comp incl
    have hrange : g.range = ⊤ := by
      rcases (IsSimpleOrder.eq_bot_or_eq_top g.range) with h | h
      · exfalso
        have hmem : g ⟨w, hw, hw1⟩ ∈ g.range := ⟨⟨w, hw, hw1⟩, rfl⟩
        rw [h] at hmem
        have h0 : (s.gradedProjection j₀).hom ⟨w, hw1⟩ = 0 := hmem
        exact hΦw (hΦ0 w ((s.gradedProjection_eq_zero_iff j₀ ⟨w, hw1⟩).mp h0))
      · exact h
    intro v hv
    have hmem : (s.gradedProjection j₀).hom ⟨v, hv⟩ ∈ g.range := by
      rw [hrange]
      exact Submodule.mem_top
    obtain ⟨⟨w', hw'T⟩, hw'⟩ := hmem
    have hw'W : w' ∈ Wsub := (Submodule.mem_inf.mp hw'T).1
    have hw'1 : w' ∈ S1 := (Submodule.mem_inf.mp hw'T).2
    refine ⟨w', hw'W, hw'1, ?_⟩
    have hw'' : (s.gradedProjection j₀).hom ⟨w', hw'1⟩ =
        (s.gradedProjection j₀).hom ⟨v, hv⟩ := hw'
    have hsub : (⟨v - w', S1.toSubmodule.sub_mem hv hw'1⟩ :
        S1.toSubmodule) = ⟨v, hv⟩ - ⟨w', hw'1⟩ := rfl
    apply (s.gradedProjection_eq_zero_iff j₀ ⟨v - w', S1.toSubmodule.sub_mem hv hw'1⟩).mp
    rw [hsub, map_sub, hw'', sub_self]
  -- Step 4: a generalized `χ`-vector of the quotient would come from `S0`.
  intro hτχ
  have hne := (generalizedWeightSpace_ne_bot_iff ι χ hι hτ).mpr hτχ
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp
    (fun h => hne (Subrepresentation.toSubmodule_injective h))
  obtain ⟨x, rfl⟩ := hq y
  obtain ⟨v, hv, hqv⟩ := exists_mem_generalizedWeightSpace_map_eq ι hι hE hτ q χ x hy
  obtain ⟨d, hd⟩ := exists_mem_characterSpace_of_mem_generalizedWeightSpace ι hι hE.1 χ hv
  have hv1 := mem_succ_of_mem_characterSpace ι s j₀ χ hother hd
  obtain ⟨w', hw'W, -, hvw⟩ := hcover v hv1
  have hqu : q (v - w') = q x := by rw [map_sub, hqW w' hw'W, sub_zero, hqv]
  let g := q.comp (ProductFactorization.subrepresentationInclusion S0)
  have hgy : g ⟨v - w', hvw⟩ ∈ generalizedWeightSpace τ ι χ hι := by
    change q (v - w') ∈ _
    rw [hqu]
    exact hy
  obtain ⟨u, hu, hgu⟩ := exists_mem_generalizedWeightSpace_map_eq ι hι
    (isAdmissible_subrepresentation hE S0) hτ g χ ⟨v - w', hvw⟩ hgy
  obtain ⟨d', hd'⟩ := exists_coe_mem_characterSpace ι hι S0
    (isAdmissible_subrepresentation hE S0).1 χ hu
  have hu0 := eq_zero_of_mem_castSucc ι s j₀ χ hother hd' u.property
  apply hy0
  rw [← hqu]
  change g ⟨v - w', hvw⟩ = 0
  rw [← hgu]
  change q (u : E) = 0
  rw [hu0, map_zero]

end Langlands.InducedTwistExclusion
