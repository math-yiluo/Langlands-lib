import Langlands.AlgebraicGeometry.AlgebraicSpace.TupleOrbitBasics

/-! # Closed loci and maps between fibre powers -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ChartFibrePower

variable {S : Scheme.{u}} {X : Presheaf S} {U : Over S} {f : (schemeYoneda S).obj U ⟶ X}

set_option backward.isDefEq.respectTransparency.types false in
/-- Every projection of the standard fibre powers of a finite map is finite. -/
theorem fin_pr_isFinite (hf : IsFinite f) (ha : (schemeYoneda S).relativelyRepresentable f) :
    ∀ (n : ℕ) (i : Fin (n + 1)), _root_.AlgebraicGeometry.IsFinite ((fin ha n).pr i).left
  | 0, i => by
    change _root_.AlgebraicGeometry.IsFinite (Over.Hom.left (𝟙 U))
    rw [Over.id_left]
    infer_instance
  | n + 1, i => by
    have ih := fin_pr_isFinite hf ha n
    have hsnd : _root_.AlgebraicGeometry.IsFinite (succSnd ha (fin ha n)).left :=
      hf.projection _ _ _ (succ_isPullback ha (fin ha n))
    change _root_.AlgebraicGeometry.IsFinite (succPr ha (fin ha n) i).left
    induction i using Fin.cases with
    | zero =>
      rw [succPr_zero]
      have hbase : IsFinite (toBase (fin ha n)) := IsFinite.map_comp _ (ih 0) hf
      exact hbase.projection f _ _ (succ_isPullback ha (fin ha n)).flip
    | succ i =>
      rw [succPr_succ, Over.comp_left]
      have := ih i
      infer_instance

variable {ι : Type*}

/-- The diagonal morphism from the base scheme into a fibre power. -/
def diag (P : ChartFibrePower f ι) : U ⟶ P.obj :=
  (one f).mapIndex P (fun _ => 0)

@[reassoc (attr := simp)]
theorem diag_pr (P : ChartFibrePower f ι) (i : ι) : P.diag ≫ P.pr i = 𝟙 U :=
  (one f).mapIndex_pr P _ i

theorem diag_perm (P : ChartFibrePower f ι) (σ : Equiv.Perm ι) : P.diag ≫ P.perm σ = P.diag :=
  P.hom_ext _ _ fun i => by simp

set_option backward.isDefEq.respectTransparency.types false in
theorem diag_isClosedImmersion (P : ChartFibrePower f ι) (i : ι)
    (hi : _root_.AlgebraicGeometry.IsFinite (P.pr i).left) :
    _root_.AlgebraicGeometry.IsClosedImmersion P.diag.left := by
  have h : P.diag.left ≫ (P.pr i).left = 𝟙 U.left := by
    rw [← Over.comp_left, diag_pr, Over.id_left]
  have : _root_.AlgebraicGeometry.IsClosedImmersion (P.diag.left ≫ (P.pr i).left) := by
    rw [h]; infer_instance
  exact IsClosedImmersion.of_comp P.diag.left (P.pr i).left

/-- The permutation action is by isomorphisms. -/
theorem perm_perm_inv (P : ChartFibrePower f ι) (σ : Equiv.Perm ι) :
    P.perm σ ≫ P.perm σ⁻¹ = 𝟙 P.obj := by
  rw [perm_mul, mul_inv_cancel, perm_one]

theorem pr_perm_apply (P : ChartFibrePower f ι) (σ : Equiv.Perm ι) (i : ι) (p : P.obj.left) :
    (P.pr i).left ((P.perm σ).left p) = (P.pr (σ i)).left p := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, perm_pr]

theorem isDistinct_perm_iff (P : ChartFibrePower f ι) (σ : Equiv.Perm ι) (p : P.obj.left) :
    P.IsDistinct ((P.perm σ).left p) ↔ P.IsDistinct p := by
  constructor
  · intro h a b hab
    have h1 : P.coord p (σ (σ.symm a)) = P.coord p (σ (σ.symm b)) := by
      simpa using hab
    have h2 := h ((coord_mapIndex_eq_iff P P σ p (σ.symm a) (σ.symm b)).mpr h1)
    simpa using congrArg σ h2
  · intro h k l hkl
    exact σ.injective (h ((coord_mapIndex_eq_iff P P σ p k l).mp hkl))

set_option backward.isDefEq.respectTransparency.types false in
/-- The locus where two coordinates agree is closed. -/
theorem isClosed_coord_eq (hf : IsFinite f) (Q : ChartFibrePower f ι) (a b : ι) :
    IsClosed {q | Q.coord q a = Q.coord q b} := by
  have ha : (schemeYoneda S).relativelyRepresentable f := hf.representable
  let R := fin ha 1
  let δR : U ⟶ R.obj := (one f).mapIndex R (fun _ => 0)
  have hR1 : _root_.AlgebraicGeometry.IsFinite (R.pr 1).left := fin_pr_isFinite hf ha 1 1
  have hδ : _root_.AlgebraicGeometry.IsClosedImmersion δR.left := by
    have hdp : δR ≫ R.pr 1 = 𝟙 U := (one f).mapIndex_pr R _ 1
    have h : δR.left ≫ (R.pr 1).left = 𝟙 U.left := by
      rw [← Over.comp_left, hdp, Over.id_left]
    have : _root_.AlgebraicGeometry.IsClosedImmersion (δR.left ≫ (R.pr 1).left) := by
      rw [h]; infer_instance
    exact IsClosedImmersion.of_comp δR.left (R.pr 1).left
  have hΔ : {r : R.obj.left | R.coord r 0 = R.coord r 1} = Set.range δR.left := by
    ext r
    constructor
    · intro hr
      have hm := mem_range_mapIndex (one f) R (fun _ => 0) (fun _ => 0) r (by
        intro k
        fin_cases k
        · rfl
        · exact hr)
      obtain ⟨x, hx⟩ := hm
      exact ⟨_, by rw [Over.comp_left, Scheme.Hom.comp_apply] at hx; exact hx⟩
    · rintro ⟨x, rfl⟩
      exact (coord_mapIndex_eq_iff (one f) R (fun _ => 0) x 0 1).mpr rfl
  have hset : {q | Q.coord q a = Q.coord q b} =
      (Q.mapIndex R ![a, b]).left ⁻¹' {r : R.obj.left | R.coord r 0 = R.coord r 1} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [coord_mapIndex_eq_iff Q R ![a, b] q 0 1]
    rfl
  rw [hset, hΔ]
  exact hδ.isClosedEmbedding.isClosed_range.preimage (Q.mapIndex R ![a, b]).left.continuous

/-- The locus of points with pairwise distinct coordinates is open. -/
theorem isOpen_isDistinct [Finite ι] (hf : IsFinite f) (Q : ChartFibrePower f ι) :
    IsOpen {q | Q.IsDistinct q} := by
  have : {q | Q.IsDistinct q} = ⋂ a, ⋂ b, ({q | Q.coord q a = Q.coord q b}ᶜ ∪ {_q | a = b}) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
    constructor
    · intro h a b
      by_cases hab : Q.coord q a = Q.coord q b
      · exact Or.inr (h hab)
      · exact Or.inl hab
    · intro h a b hab
      exact (h a b).resolve_left (not_not.mpr hab)
  rw [this]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
  refine (isClosed_coord_eq hf Q a b).isOpen_compl.union ?_
  by_cases hab : a = b
  · simp [hab]
  · simp [hab]

variable {P : ChartFibrePower f ι} {P2 : ChartFibrePower f (ι ⊕ ι)}

/-- Two points with the same image are the halves of a point of the doubled fibre power. -/
theorem exists_pair (P : ChartFibrePower f ι) (P2 : ChartFibrePower f (ι ⊕ ι)) (i₀ : ι)
    {w w' : P.obj.left} (h : SameImage ((schemeYoneda S).map (P.pr i₀) ≫ f) w w') :
    ∃ p, (P2.mapIndex P Sum.inl).left p = w ∧ (P2.mapIndex P Sum.inr).left p = w' := by
  obtain ⟨T, g, g', t, e, hg, hg'⟩ := h
  let fam : ι ⊕ ι → (T ⟶ U) := Sum.elim (fun i => g ≫ P.pr i) (fun i => g' ≫ P.pr i)
  have hfam : ∀ a b, (schemeYoneda S).map (fam a) ≫ f = (schemeYoneda S).map (fam b) ≫ f := by
    have key : ∀ a, (schemeYoneda S).map (fam a) ≫ f =
        (schemeYoneda S).map g ≫ (schemeYoneda S).map (P.pr i₀) ≫ f := by
      intro a
      rcases a with i | i
      · simp only [fam, Sum.elim_inl, Functor.map_comp, Category.assoc, P.w i i₀]
      · simp only [fam, Sum.elim_inr, Functor.map_comp, Category.assoc, P.w i i₀]
        rw [e]
    intro a b
    rw [key a, key b]
  let l := P2.lift fam hfam
  have hl : l ≫ P2.mapIndex P Sum.inl = g :=
    P.hom_ext _ _ fun i => by simp [l, fam]
  have hl' : l ≫ P2.mapIndex P Sum.inr = g' :=
    P.hom_ext _ _ fun i => by simp [l, fam]
  refine ⟨l.left t, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hl, hg]
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hl', hg']

/-- A point of the doubled fibre power whose right coordinates are a permutation of the left
ones lies on the graph of the permutation action. -/
theorem inr_eq_perm_inl (P : ChartFibrePower f ι) (P2 : ChartFibrePower f (ι ⊕ ι))
    (σ : Equiv.Perm ι) (p : P2.obj.left)
    (h : ∀ i, P2.coord p (Sum.inr i) = P2.coord p (Sum.inl (σ i))) :
    (P2.mapIndex P Sum.inr).left p = (P.perm σ).left ((P2.mapIndex P Sum.inl).left p) := by
  have key : P2.pointHom p ≫ P2.mapIndex P Sum.inr =
      P2.pointHom p ≫ P2.mapIndex P Sum.inl ≫ P.perm σ := by
    refine P.hom_ext _ _ fun i => ?_
    apply Over.OverMorphism.ext
    simp only [Category.assoc, mapIndex_pr, perm_pr]
    exact h i
  have key' := congrArg Over.Hom.left key
  rw [Over.comp_left, Over.comp_left, Over.comp_left] at key'
  let s0 : Spec (P2.obj.left.residueField p) := IsLocalRing.closedPoint _
  have h2 := congrArg (fun g => g s0) key'
  change (P2.mapIndex P Sum.inr).left (P2.obj.left.fromSpecResidueField p s0) =
    (P.perm σ).left ((P2.mapIndex P Sum.inl).left (P2.obj.left.fromSpecResidueField p s0)) at h2
  rwa [Scheme.fromSpecResidueField_apply] at h2

end Langlands.AlgebraicGeometry.AlgebraicSpace.ChartFibrePower
