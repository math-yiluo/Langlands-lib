import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartFibreCount
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.PointAgreement

/-! # Complete tuples of points of an étale chart

Let `π : h_W → X` be a representable map from a scheme `W` over `S` to an algebraic space `X`,
and let `E` be the fibre power of `n + 1` copies of `W` over `X`, with projections
`pr₀, …, prₙ`. A point `t` of `E` is *complete* when every point `t'` of `W ×_X E` over `t`
has its new coordinate equal to one of the coordinates of `t`. At a complete point, every
field-valued point of `W` with the same image in `X` as the coordinates is one of the
coordinates (`exists_eqAt_of_mem_completeLocus`).

If `X` is quasi-separated, `π` is étale and `W` and `S` are affine, the fibres of `π` have a
uniformly bounded number of field-valued points, and for `n` large every point of `W` is the
first coordinate of a complete point (`exists_completeLocus`).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover

open ChartFibrePower EtaleChartFibreCount FieldPointEtaleLift

section Bound

variable {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S} {V : Over S}
  (a : (schemeYoneda S).obj V ⟶ X.presheaf)

/-- **Fibres of an étale affine chart are uniformly bounded**, over an affine base. If `X` is
quasi-separated and `a : h_V → X` is étale with `V` affine, there is a bound `D` such that for
every field `L`, every `L`-point `s₀` of `S` and every point `s` of `V` over `s₀`, any family
of pairwise distinct points of `V` over `s₀` with the same image in `X` as `s` has at most `D`
members. -/
theorem exists_fibre_card_le (hX : IsQuasiSeparated X) (ha : IsEtale a) [IsAffine V.left] :
    ∃ D : ℕ, ∀ (L : Type u) [Field L] (s₀ : Spec (CommRingCat.of L) ⟶ S)
      (s : Over.mk s₀ ⟶ V) (ι : Type u) [Fintype ι] (v : ι → (Over.mk s₀ ⟶ V)),
      Function.Injective v →
      (∀ i, (schemeYoneda S).map (v i) ≫ a = (schemeYoneda S).map s ≫ a) →
        Fintype.card ι ≤ D := by
  classical
  have : IsAffine (V ⊗ V).left := by
    change IsAffine (Limits.pullback V.hom V.hom)
    infer_instance
  have := compactSpace_selfPullback a hX
  have : Etale (selfSnd a).left := ha.projection a _ (selfSnd a) (selfPullback_isPullback a)
  obtain ⟨t, ht⟩ : ∃ t : Finset (selfPullback a).left.affineOpens,
      ∀ x : (selfPullback a).left, ∃ W ∈ t, x ∈ (W : (selfPullback a).left.Opens) := by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
      (fun W : (selfPullback a).left.affineOpens =>
        ((W : (selfPullback a).left.Opens) : Set (selfPullback a).left))
      (fun W => W.1.isOpen) (fun x _ => by
        obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset
          (show x ∈ (⊤ : (selfPullback a).left.Opens) from trivial)
        exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hx⟩)
    refine ⟨t, fun x => ?_⟩
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨W, hW, hx⟩ := hx
    exact ⟨W, hW, hx⟩
  choose D hD using fun W : (selfPullback a).left.affineOpens =>
    exists_card_le_of_etale_affine (selfSnd a).left W
  refine ⟨∑ W ∈ t, D W, fun L _ s₀ s ι _ v hv hva => ?_⟩
  let r : ι → (Over.mk s₀ ⟶ selfPullback a) := fun i => selfLift a (v i) s (hva i)
  have hr₁ : ∀ i, r i ≫ selfFst a = v i := fun i =>
    Functor.relativelyRepresentable.lift'_fst _ _ _ _
  have hr₂ : ∀ i, r i ≫ selfSnd a = s := fun i =>
    Functor.relativelyRepresentable.lift'_snd _ _ _ _
  have hrinj : Function.Injective fun i => (r i).left := by
    intro i j hij
    apply hv
    rw [← hr₁ i, ← hr₁ j, Over.OverMorphism.ext hij]
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
  have : Subsingleton (Spec (CommRingCat.of L)) := inferInstance
  choose w hwt hw using fun i => ht ((r i).left pt)
  have hrange : ∀ i, Set.range (r i).left ⊆ (w i : (selfPullback a).left.Opens) := by
    rintro i _ ⟨p, rfl⟩
    rw [Subsingleton.elim (α := Spec (CommRingCat.of L)) p pt]
    exact hw i
  have hfib : ∀ W ∈ t, (Finset.univ.filter fun i => w i = W).card ≤ D W := by
    intro W _
    rw [← Fintype.card_subtype]
    refine hD W L s.left {i // w i = W} (fun i => (r i.1).left) ?_ ?_ ?_
    · intro i j hij
      exact Subtype.ext (hrinj hij)
    · intro i
      exact congrArg CommaMorphism.left (hr₂ i.1)
    · intro i
      have h := hrange i.1
      rw [i.2] at h
      exact h
  calc Fintype.card ι = (Finset.univ : Finset ι).card := Finset.card_univ.symm
    _ = ∑ W ∈ t, (Finset.univ.filter fun i => w i = W).card :=
        Finset.card_eq_sum_card_fiberwise fun i _ => hwt i
    _ ≤ ∑ W ∈ t, D W := Finset.sum_le_sum hfib

end Bound

section Tuples

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {W : Over S}
  {π : (schemeYoneda S).obj W ⟶ X.presheaf} (ha : (schemeYoneda S).relativelyRepresentable π)
  {n : ℕ} (P : ChartFibrePower π (Fin (n + 1)))

/-- The complete points of a fibre power `P = W ×_X ⋯ ×_X W` with `n + 1` factors: the points
`t` such that at every point `t'` of `W ×_X P` over `t` the new coordinate agrees with one of
the coordinates of `t`. -/
def completeLocus : Set P.obj.left :=
  {t | ∀ t' : (succObj ha P).left, (succSnd ha P).left t' = t →
    ∃ i : Fin (n + 1), EqAt (succFst ha P).left (succSnd ha P ≫ P.pr i).left t'}

variable {ha P}

/-- **Completeness.** If `h : T ⟶ P` and `w : T ⟶ W` have the same image in `X` as the first
coordinate of `h`, then at every point of `T` mapped by `h` to a complete point, `w` agrees
with one of the coordinates of `h`. -/
theorem exists_eqAt_of_mem_completeLocus {T : Over S} (h : T ⟶ P.obj) (w : T ⟶ W)
    (hw : (schemeYoneda S).map w ≫ π = (schemeYoneda S).map (h ≫ P.pr 0) ≫ π)
    (τ : T.left) (hτ : h.left τ ∈ completeLocus ha P) :
    ∃ i : Fin (n + 1), EqAt w.left (h ≫ P.pr i).left τ := by
  have hw' : (schemeYoneda S).map w ≫ π = (schemeYoneda S).map h ≫ P.toBase := by
    rw [hw, Functor.map_comp_assoc]
  let l : T ⟶ succObj ha P := Functor.relativelyRepresentable.lift' ha w h hw'
  have hl₁ : l ≫ succFst ha P = w := Functor.relativelyRepresentable.lift'_fst _ _ _ _
  have hl₂ : l ≫ succSnd ha P = h := Functor.relativelyRepresentable.lift'_snd _ _ _ _
  obtain ⟨i, hi⟩ := hτ (l.left τ) (by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hl₂])
  refine ⟨i, ?_⟩
  rw [← eqAt_comp_iff, ← Over.comp_left, ← Over.comp_left, hl₁, ← Category.assoc, hl₂] at hi
  exact hi

variable (P)

/-- The pairs of distinct indices at which the coordinates of a point of a fibre power agree. -/
def coincidences (t : P.obj.left) : Set (Fin (n + 1) × Fin (n + 1)) :=
  {p | p.1 ≠ p.2 ∧ EqAt (P.pr p.1).left (P.pr p.2).left t}

variable {P}

/-- **Improvement step.** If the fibres of `π` have at most `D < n + 2` distinct points, a point
`t` that is not complete is replaced by a point with the same first coordinate and fewer
coincidences: some repeated coordinate of `t` is replaced by a new coordinate. -/
theorem exists_coincidences_lt (D : ℕ)
    (hD : ∀ (L : Type u) [Field L] (s₀ : Spec (CommRingCat.of L) ⟶ S)
      (s : Over.mk s₀ ⟶ W) (ι : Type u) [Fintype ι] (v : ι → (Over.mk s₀ ⟶ W)),
      Function.Injective v →
      (∀ i, (schemeYoneda S).map (v i) ≫ π = (schemeYoneda S).map s ≫ π) →
        Fintype.card ι ≤ D)
    (hn : D < n + 2) (t : P.obj.left) (ht : t ∉ completeLocus ha P) :
    ∃ t'' : P.obj.left, (P.pr 0).left t'' = (P.pr 0).left t ∧
      (coincidences P t'').ncard < (coincidences P t).ncard := by
  classical
  simp only [completeLocus, Set.mem_ofPred_eq, not_forall, not_exists] at ht
  obtain ⟨t', rfl, hnew⟩ := ht
  -- agreement of coordinates at `t'`
  let R : Fin (n + 2) → Fin (n + 2) → Prop := fun x y =>
    EqAt ((succ ha P).pr x).left ((succ ha P).pr y).left t'
  have hR0 : ∀ i : Fin (n + 1), ¬ R 0 i.succ := hnew
  have hRold : ∀ i j : Fin (n + 1), R i.succ j.succ ↔
      EqAt (P.pr i).left (P.pr j).left ((succSnd ha P).left t') :=
    fun i j => eqAt_comp_iff (succSnd ha P).left (P.pr i).left (P.pr j).left t'
  by_cases h0 : (coincidences P ((succSnd ha P).left t')).ncard = 0
  · -- all `n + 2` coordinates of `t'` are distinct: contradiction with the bound
    exfalso
    have hempty : coincidences P ((succSnd ha P).left t') = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite _)).mp h0
    have hdist : ∀ x y : Fin (n + 2), R x y → x = y := by
      intro x y hxy
      induction x using Fin.cases with
      | zero =>
        induction y using Fin.cases with
        | zero => rfl
        | succ j => exact absurd hxy (hR0 j)
      | succ i =>
        induction y using Fin.cases with
        | zero => exact absurd (EqAt.symm hxy) (hR0 i)
        | succ j =>
          by_contra hij
          have hij' : i ≠ j := fun h => hij (by rw [h])
          have hmem : (i, j) ∈ coincidences P ((succSnd ha P).left t') :=
            ⟨hij', (hRold i j).mp hxy⟩
          rw [hempty] at hmem
          exact hmem
    let s₀ : Spec (CommRingCat.of ((succObj ha P).left.residueField t')) ⟶ S :=
      (succObj ha P).left.fromSpecResidueField t' ≫ (succObj ha P).hom
    let v : ULift.{u} (Fin (n + 2)) → (Over.mk s₀ ⟶ W) := fun x =>
      (succ ha P).pointHom t' ≫ (succ ha P).pr x.down
    have hv : Function.Injective v := by
      intro x y hxy
      have h := congrArg CommaMorphism.left hxy
      exact ULift.ext _ _ (hdist _ _ h)
    have hva : ∀ x, (schemeYoneda S).map (v x) ≫ π = (schemeYoneda S).map (v ⟨0⟩) ≫ π := by
      intro x
      change (schemeYoneda S).map ((succ ha P).pointHom t' ≫ (succ ha P).pr x.down) ≫ π =
        (schemeYoneda S).map ((succ ha P).pointHom t' ≫ (succ ha P).pr 0) ≫ π
      rw [Functor.map_comp_assoc, Functor.map_comp_assoc, (succ ha P).w x.down 0]
    have hcard := hD _ s₀ (v ⟨0⟩) (ULift.{u} (Fin (n + 2))) v hv hva
    rw [Fintype.card_ulift, Fintype.card_fin] at hcard
    omega
  · -- a coincidence `(j, k)` with `k ≠ 0`
    obtain ⟨j, k, hjk, hk0, hjkR⟩ : ∃ j k : Fin (n + 1), j ≠ k ∧ k ≠ 0 ∧
        EqAt (P.pr j).left (P.pr k).left ((succSnd ha P).left t') := by
      obtain ⟨⟨a, b⟩, hab, habR⟩ :=
        (Set.nonempty_iff_ne_empty (s := coincidences P ((succSnd ha P).left t'))).mpr
          (fun h => h0 (by rw [h, Set.ncard_empty]))
      by_cases hb : b = 0
      · subst hb
        exact ⟨0, a, Ne.symm hab, hab, EqAt.symm habR⟩
      · exact ⟨a, b, hab, hb, habR⟩
    -- replace the coordinate `k` by the new coordinate
    let σ : Fin (n + 1) → Fin (n + 2) := fun c => if c = k then 0 else c.succ
    let m : (succ ha P).obj ⟶ P.obj := (succ ha P).mapIndex P σ
    refine ⟨m.left t', ?_, ?_⟩
    · have hσ0 : σ 0 = (0 : Fin (n + 1)).succ := by simp [σ, hk0.symm]
      have key : m ≫ P.pr 0 = succSnd ha P ≫ P.pr 0 := by
        rw [mapIndex_pr, hσ0]
        rfl
      exact congrArg (fun f => f.left t') key
    · have hm : ∀ c d : Fin (n + 1), EqAt (P.pr c).left (P.pr d).left (m.left t') ↔
          R (σ c) (σ d) :=
        fun c d => coord_mapIndex_eq_iff (succ ha P) P σ t' c d
      refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
      refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · rintro ⟨c, d⟩ ⟨hcd, hcdR⟩
        refine ⟨hcd, (hRold c d).mp ?_⟩
        have hcdR' := (hm c d).mp hcdR
        by_cases hc : c = k
        · subst hc
          have hd : d ≠ c := Ne.symm hcd
          have : R 0 d.succ := by simpa [σ, hd] using hcdR'
          exact absurd this (hR0 d)
        · by_cases hd : d = k
          · subst hd
            have : R c.succ 0 := by simpa [σ, hc] using hcdR'
            exact absurd (EqAt.symm this) (hR0 c)
          · simpa [σ, hc, hd] using hcdR'
      · intro heq
        have hmem : (j, k) ∈ coincidences P ((succSnd ha P).left t') := ⟨hjk, hjkR⟩
        rw [← heq] at hmem
        obtain ⟨-, hR⟩ := hmem
        have : R j.succ 0 := by simpa [σ, hjk] using (hm j k).mp hR
        exact hR0 j (EqAt.symm this)

/-- **Complete tuples exist** when the fibres of `π` have at most `D < n + 2` distinct points:
every point of `W` is the first coordinate of a complete point. -/
theorem exists_mem_completeLocus_of_bound (D : ℕ)
    (hD : ∀ (L : Type u) [Field L] (s₀ : Spec (CommRingCat.of L) ⟶ S)
      (s : Over.mk s₀ ⟶ W) (ι : Type u) [Fintype ι] (v : ι → (Over.mk s₀ ⟶ W)),
      Function.Injective v →
      (∀ i, (schemeYoneda S).map (v i) ≫ π = (schemeYoneda S).map s ≫ π) →
        Fintype.card ι ≤ D)
    (hn : D < n + 2) (w : W.left) :
    ∃ t ∈ completeLocus ha P, (P.pr 0).left t = w := by
  let δ : W ⟶ P.obj := P.lift (fun _ => 𝟙 W) (fun _ _ => rfl)
  have hδ : (P.pr 0).left (δ.left w) = w := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, P.lift_pr]
    rfl
  suffices h : ∀ c : ℕ, ∀ t : P.obj.left, (coincidences P t).ncard = c → (P.pr 0).left t = w →
      ∃ t ∈ completeLocus ha P, (P.pr 0).left t = w from h _ _ rfl hδ
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro t hc ht
    by_cases hG : t ∈ completeLocus ha P
    · exact ⟨t, hG, ht⟩
    · obtain ⟨t'', h₁, h₂⟩ := exists_coincidences_lt D hD hn t hG
      exact ih _ (hc ▸ h₂) t'' rfl (h₁.trans ht)

/-- **Complete tuples exist.** If `X` is quasi-separated over an affine base and `π` is étale
with `W` affine, then for some `n` every point of `W` is the first coordinate of a complete
point of the fibre power with `n + 1` factors. -/
theorem exists_completeLocus [IsAffine S] (hX : IsQuasiSeparated X) (hπ : IsEtale π)
    [IsAffine W.left] :
    ∃ n : ℕ, ∀ w : W.left, ∃ t ∈ completeLocus hπ.1 (ChartFibrePower.fin hπ.1 n),
      ((ChartFibrePower.fin hπ.1 n).pr 0).left t = w := by
  obtain ⟨D, hD⟩ := exists_fibre_card_le π hX hπ
  exact ⟨D, exists_mem_completeLocus_of_bound D hD (by omega)⟩

end Tuples

end Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover
