import Langlands.Representation.Filtration.Splicing.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Refinement of actual natural filtrations by filtrations of their actual grades. -/

noncomputable section
open CategoryTheory
open scoped BigOperators

namespace Langlands

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C]
  {M Q : C ⥤ Rep.{uV} R G}

namespace RepSubfunctor

/-- The inverse-image quotient comparison only needs lifting onto the upper step. -/
def inverseImageQuotientIsoOfUpperSurjective (S T : RepSubfunctor Q) (π : M ⟶ Q)
    (hsurj : ∀ X, Function.Surjective ((T.inverseImageHom π).app X).hom) :
    (S.inverseImage π).quotientFunctor (T.inverseImage π) ≅ S.quotientFunctor T := by
  let α := T.inverseImageHom π ≫ S.quotientNatProjection T
  apply (S.inverseImage π).quotientNatIsoOfSurjective (T.inverseImage π) α
  · intro X v
    change (π.app X).hom v ∈ S.obj X ↔
      (Submodule.Quotient.mk
        (⟨(π.app X).hom v, v.property⟩ : T.representation X) :
          S.quotientObj T X) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  · intro X v
    obtain ⟨w, rfl⟩ := S.quotientProjection_surjective T X v
    obtain ⟨v, rfl⟩ := hsurj X w
    exact ⟨v, rfl⟩

/-- A full actual subfunctor has a canonical natural lift of every ambient vector. -/
def topLift (T : RepSubfunctor M) (htop : ∀ X, T.obj X = ⊤) :
    M ⟶ T.toFunctor where
  app X := Rep.ofHom
    { toLinearMap :=
        { toFun := fun v => ⟨v, by rw [htop X]; trivial⟩
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      isIntertwining' := by intro g; rfl }
  naturality _ _ _ := rfl

theorem topLift_surjective (T : RepSubfunctor M) (htop : ∀ X, T.obj X = ⊤) (X : C) :
    Function.Surjective ((T.topLift htop).app X).hom := by
  intro v
  exact ⟨(v : T.representation X).val, Subtype.ext rfl⟩

/-- The ambient quotient projection when the upper actual subfunctor is full. -/
def quotientOfTop (S T : RepSubfunctor M) (htop : ∀ X, T.obj X = ⊤) :
    M ⟶ S.quotientFunctor T :=
  T.topLift htop ≫ S.quotientNatProjection T

theorem quotientOfTop_surjective (S T : RepSubfunctor M)
    (htop : ∀ X, T.obj X = ⊤) (X : C) :
    Function.Surjective ((S.quotientOfTop T htop).app X).hom := by
  intro v
  obtain ⟨w, rfl⟩ := S.quotientProjection_surjective T X v
  obtain ⟨v, rfl⟩ := T.topLift_surjective htop X w
  exact ⟨v, rfl⟩

theorem range_inclusion_eq_ker_quotientOfTop (S T : RepSubfunctor M)
    (htop : ∀ X, T.obj X = ⊤) (X : C) :
    LinearMap.range (S.inclusion.app X).hom.toLinearMap =
      LinearMap.ker ((S.quotientOfTop T htop).app X).hom.toLinearMap := by
  apply Submodule.ext
  intro v
  change (∃ w : S.representation X, (w : M.obj X) = v) ↔
    (Submodule.Quotient.mk
      (⟨v, by rw [htop X]; trivial⟩ : T.representation X) :
        S.quotientObj T X) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change (∃ w : S.representation X, (w : M.obj X) = v) ↔ v ∈ S.obj X
  constructor
  · rintro ⟨w, rfl⟩
    exact w.property
  · intro hv
    exact ⟨⟨v, hv⟩, rfl⟩

end RepSubfunctor

namespace RepFunctorFiltration

variable {n k : ℕ}

/-- Change a filtration's length along an equality, preserving its actual steps. -/
def castLength (s : RepFunctorFiltration M n) (h : n = k) :
    RepFunctorFiltration M k := h ▸ s

/-- A length cast only casts the corresponding grade index. -/
def castLengthGradedIso (s : RepFunctorFiltration M n) (h : n = k) (i : Fin k) :
    (s.castLength h).graded i ≅ s.graded (Fin.cast h.symm i) := by
  subst k
  exact Iso.refl _

/-- The actual penultimate subfunctor, including for an outer length of one. -/
def penultimate (s : RepFunctorFiltration M (n + 1)) : RepSubfunctor M :=
  s.step (Fin.last n).castSucc

/-- The initial `n` grades as an actual flag in the penultimate subfunctor. -/
def initialFiltration (s : RepFunctorFiltration M (n + 1)) :
    RepFunctorFiltration s.penultimate.toFunctor n where
  step i := (s.step i.castSucc).inverseImage s.penultimate.inclusion
  monotone X := by
    intro i j hij v hv
    exact s.monotone X hij hv
  zero X := by
    apply SetLike.ext
    intro v
    change (v : s.penultimate.representation X).val ∈ (s.step 0).obj X ↔ v = 0
    rw [s.zero X]
    change (v : s.penultimate.representation X).val = 0 ↔ v = 0
    constructor
    · intro h
      exact Subtype.ext h
    · rintro rfl
      rfl
  top X := by
    apply SetLike.ext
    intro v
    change (v : s.penultimate.representation X).val ∈
      (s.step (Fin.last n).castSucc).obj X ↔
      v ∈ (⊤ : Subrepresentation (s.penultimate.representation X).ρ)
    exact iff_of_true v.property trivial

/-- Restricting to the penultimate subfunctor preserves all earlier actual grades. -/
def prefixGradedIso (s : RepFunctorFiltration M (n + 1)) (i : Fin n) :
    s.initialFiltration.graded i ≅ s.graded i.castSucc := by
  apply RepSubfunctor.inverseImageQuotientIsoOfUpperSurjective
    (s.step i.castSucc.castSucc) (s.step i.succ.castSucc) s.penultimate.inclusion
  intro X v
  have hv : (v : (s.step i.succ.castSucc).representation X).val ∈
      s.penultimate.obj X :=
    s.monotone X (show i.succ.castSucc ≤ (Fin.last n).castSucc by
      change i.val + 1 ≤ n; omega) v.property
  exact ⟨⟨⟨(v : (s.step i.succ.castSucc).representation X).val, hv⟩,
    v.property⟩, Subtype.ext rfl⟩

/-- The ambient natural map onto the last actual graded functor. -/
def lastProjection (s : RepFunctorFiltration M (n + 1)) :
    M ⟶ s.graded (Fin.last n) :=
  s.penultimate.quotientOfTop (s.step (Fin.last (n + 1))) s.top

theorem lastProjection_surjective (s : RepFunctorFiltration M (n + 1)) (X : C) :
    Function.Surjective (s.lastProjection.app X).hom :=
  s.penultimate.quotientOfTop_surjective (s.step (Fin.last (n + 1))) s.top X

theorem range_penultimate_eq_ker_lastProjection
    (s : RepFunctorFiltration M (n + 1)) (X : C) :
    LinearMap.range (s.penultimate.inclusion.app X).hom.toLinearMap =
      LinearMap.ker (s.lastProjection.app X).hom.toLinearMap :=
  s.penultimate.range_inclusion_eq_ker_quotientOfTop
    (s.step (Fin.last (n + 1))) s.top X

/-- Canonical flattening index: preceding block lengths plus the inner index. -/
def flattenIndex (m : Fin n → ℕ) (i : Fin n) (j : Fin (m i)) : Fin (∑ i, m i) :=
  finSigmaFinEquiv ⟨i, j⟩

/-- Every flattened index records exactly its outer and inner grade indices. -/
def refinementIndexEquiv (m : Fin n → ℕ) :
    Fin (∑ i, m i) ≃ (Σ i : Fin n, Fin (m i)) := finSigmaFinEquiv.symm

@[simp]
theorem refinementIndexEquiv_flattenIndex (m : Fin n → ℕ) (i : Fin n) (j : Fin (m i)) :
    refinementIndexEquiv m (flattenIndex m i j) = ⟨i, j⟩ :=
  finSigmaFinEquiv.symm_apply_apply ⟨i, j⟩

theorem flattenIndex_val (m : Fin n → ℕ) (i : Fin n) (j : Fin (m i)) :
    (flattenIndex m i j).val = (∑ a : Fin i.val, m (Fin.castLE i.isLt.le a)) + j.val :=
  finSigmaFinEquiv_apply ⟨i, j⟩

theorem flattenIndex_castSucc_val (m : Fin (n + 1) → ℕ)
    (i : Fin n) (j : Fin (m i.castSucc)) :
    (flattenIndex m i.castSucc j).val =
      (flattenIndex (fun i => m i.castSucc) i j).val := by
  simp only [flattenIndex_val, Fin.val_castSucc]
  congr 1

theorem flattenIndex_last_val (m : Fin (n + 1) → ℕ) (j : Fin (m (Fin.last n))) :
    (flattenIndex m (Fin.last n) j).val = (∑ i : Fin n, m i.castSucc) + j.val := by
  rw [flattenIndex_val]
  rfl

/-- Flatten the complete dependent family of inner pieces, without removing zero pieces. -/
def flattenPieces {A : Sort*} (m : Fin n → ℕ) (p : ∀ i, Fin (m i) → A) :
    Fin (∑ i, m i) → A :=
  fun j => p ((refinementIndexEquiv m) j).1 ((refinementIndexEquiv m) j).2

@[simp]
theorem flattenPieces_flattenIndex {A : Sort*} (m : Fin n → ℕ)
    (p : ∀ i, Fin (m i) → A) (i : Fin n) (j : Fin (m i)) :
    flattenPieces m p (flattenIndex m i j) = p i j := by
  unfold flattenPieces
  rw [refinementIndexEquiv_flattenIndex]

/-- Concrete refinement data together with its natural actual-grade comparisons. -/
structure GradedRefinement (s : RepFunctorFiltration M n) (m : Fin n → ℕ)
    (inner : ∀ i, RepFunctorFiltration (s.graded i) (m i)) where
  filtration : RepFunctorFiltration M (∑ i, m i)
  comparison (i : Fin n) (j : Fin (m i)) :
    filtration.graded (flattenIndex m i j) ≅ (inner i).graded j

/-- Refine the initial flag recursively, then splice in the last actual quotient. -/
def refineData (s : RepFunctorFiltration M n) (m : Fin n → ℕ)
    (inner : ∀ i, RepFunctorFiltration (s.graded i) (m i)) :
    GradedRefinement s m inner := by
  induction n generalizing M with
  | zero =>
      exact
        { filtration := s.castLength (by simp)
          comparison := fun i => Fin.elim0 i }
  | succ n ih =>
      let m' : Fin n → ℕ := fun i => m i.castSucc
      let inner' : ∀ i, RepFunctorFiltration (s.initialFiltration.graded i) (m' i) :=
        fun i => (inner i.castSucc).isoTransport (s.prefixGradedIso i).symm
      let d := ih s.initialFiltration m' inner'
      let u := splice d.filtration (inner (Fin.last n))
        s.penultimate.inclusion s.lastProjection s.range_penultimate_eq_ker_lastProjection
      have hlen : (∑ i, m' i) + m (Fin.last n) = ∑ i, m i :=
        (Fin.sum_univ_castSucc m).symm
      refine
        { filtration := u.castLength hlen
          comparison := ?_ }
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro j
        refine u.castLengthGradedIso hlen _ ≪≫ ?_
        have hj : Fin.cast hlen.symm (flattenIndex m (Fin.last n) j) =
            spliceRight (∑ i, m' i) (m (Fin.last n)) j := by
          apply Fin.ext
          exact flattenIndex_last_val m j
        exact eqToIso (congrArg u.graded hj) ≪≫
          spliceRightGradedIso d.filtration (inner (Fin.last n))
            s.penultimate.inclusion s.lastProjection
            s.range_penultimate_eq_ker_lastProjection s.lastProjection_surjective j
      · intro j
        refine u.castLengthGradedIso hlen _ ≪≫ ?_
        have hj : Fin.cast hlen.symm (flattenIndex m i.castSucc j) =
            spliceLeft (∑ i, m' i) (m (Fin.last n)) (flattenIndex m' i j) := by
          apply Fin.ext
          exact flattenIndex_castSucc_val m i j
        exact eqToIso (congrArg u.graded hj) ≪≫
          spliceLeftGradedIso d.filtration (inner (Fin.last n))
            s.penultimate.inclusion s.lastProjection
            s.range_penultimate_eq_ker_lastProjection s.penultimate.inclusion_injective
            (flattenIndex m' i j) ≪≫
          d.comparison i j ≪≫
          ((inner i.castSucc).isoTransportGradedIso (s.prefixGradedIso i).symm j).symm

/-- The actual refined filtration, of the sum of all supplied inner lengths. -/
def refine (s : RepFunctorFiltration M n) (m : Fin n → ℕ)
    (inner : ∀ i, RepFunctorFiltration (s.graded i) (m i)) :
    RepFunctorFiltration M (∑ i, m i) :=
  (refineData s m inner).filtration

/-- Every inner grade is retained at its canonical flattened index. -/
def refineGradedIso (s : RepFunctorFiltration M n) (m : Fin n → ℕ)
    (inner : ∀ i, RepFunctorFiltration (s.graded i) (m i))
    (i : Fin n) (j : Fin (m i)) :
    (s.refine m inner).graded (flattenIndex m i j) ≅ (inner i).graded j :=
  (refineData s m inner).comparison i j

/-- A natural comparison for every grade of the full flattened family. -/
def refineGradedIsoAt (s : RepFunctorFiltration M n) (m : Fin n → ℕ)
    (inner : ∀ i, RepFunctorFiltration (s.graded i) (m i))
    (j : Fin (∑ i, m i)) :
    (s.refine m inner).graded j ≅ flattenPieces m (fun i => (inner i).graded) j := by
  let a := refinementIndexEquiv m j
  have hj : flattenIndex m a.1 a.2 = j := finSigmaFinEquiv.apply_symm_apply j
  exact eqToIso (congrArg (s.refine m inner).graded hj.symm) ≪≫
    s.refineGradedIso m inner a.1 a.2

/-- Supplied identifications of all inner grades give the full ordered flattened family. -/
theorem HasGradedPieces.refine (s : RepFunctorFiltration M n) (m : Fin n → ℕ)
    (inner : ∀ i, RepFunctorFiltration (s.graded i) (m i))
    {p : ∀ i, Fin (m i) → C ⥤ Rep.{uV} R G}
    (h : ∀ i, (inner i).HasGradedPieces (p i)) :
    (s.refine m inner).HasGradedPieces (flattenPieces m p) := by
  intro j
  let a := refinementIndexEquiv m j
  obtain ⟨e⟩ := h a.1 a.2
  exact ⟨s.refineGradedIsoAt m inner j ≪≫ e⟩

/-- Inner ordered filtration existence refines a supplied actual outer filtration. -/
theorem hasOrderedFiltration_refine (s : RepFunctorFiltration M n) (m : Fin n → ℕ)
    (p : ∀ i, Fin (m i) → C ⥤ Rep.{uV} R G)
    (h : ∀ i, HasOrderedFiltration (s.graded i) (p i)) :
    HasOrderedFiltration M (flattenPieces m p) := by
  choose inner hinner using h
  exact ⟨s.refine m inner, HasGradedPieces.refine s m inner hinner⟩

/-- Permutations of inner pieces act on their complete dependent blocks. -/
theorem isGluedFrom_refine (s : RepFunctorFiltration M n) (m : Fin n → ℕ)
    (p : ∀ i, Fin (m i) → C ⥤ Rep.{uV} R G)
    (h : ∀ i, IsGluedFrom (s.graded i) (p i)) :
    IsGluedFrom M (flattenPieces m p) := by
  choose e he using h
  let a := refinementIndexEquiv m
  let ef := a.trans ((Equiv.sigmaCongrRight e).trans a.symm)
  refine ⟨ef, ?_⟩
  have hp : flattenPieces m (fun i => p i ∘ e i) = flattenPieces m p ∘ ef := by
    funext j
    simp only [flattenPieces, Function.comp_apply, ef, a, Equiv.trans_apply]
    exact (congrArg (fun a : Σ i, Fin (m i) => p a.1 a.2)
      ((refinementIndexEquiv m).apply_symm_apply
        ((Equiv.sigmaCongrRight e) ((refinementIndexEquiv m) j)))).symm
  rw [← hp]
  exact s.hasOrderedFiltration_refine m (fun i => p i ∘ e i) he

end RepFunctorFiltration

variable {n k : ℕ}
  {p : Fin n → C ⥤ Rep.{uV} R G}

/-- Unordered gluing is independent of a finite enumeration of the full family. -/
theorem IsGluedFrom.reindex (h : IsGluedFrom M p) (e : Fin k ≃ Fin n) :
    IsGluedFrom M (p ∘ e) := by
  have hlen : k = n := by simpa using Fintype.card_congr e
  subst k
  obtain ⟨d, hd⟩ := h
  refine ⟨d.trans e.symm, ?_⟩
  simpa only [Function.comp_def, Equiv.trans_apply, Equiv.apply_symm_apply] using hd

/-- Refine each named piece of an ordered filtration, retaining every inner piece. -/
theorem HasOrderedFiltration.refine (h : HasOrderedFiltration M p)
    (m : Fin n → ℕ) (q : ∀ i, Fin (m i) → C ⥤ Rep.{uV} R G)
    (hinner : ∀ i, HasOrderedFiltration (p i) (q i)) :
    HasOrderedFiltration M (RepFunctorFiltration.flattenPieces m q) := by
  obtain ⟨s, hs⟩ := h
  apply s.hasOrderedFiltration_refine m q
  intro i
  obtain ⟨e⟩ := hs i
  exact (hinner i).iso e.symm (fun _ => Iso.refl _)

/-- Refine an unordered outer family by unordered inner families, without losing pieces. -/
theorem IsGluedFrom.refine (h : IsGluedFrom M p)
    (m : Fin n → ℕ) (q : ∀ i, Fin (m i) → C ⥤ Rep.{uV} R G)
    (hinner : ∀ i, IsGluedFrom (p i) (q i)) :
    IsGluedFrom M (RepFunctorFiltration.flattenPieces m q) := by
  obtain ⟨e, s, hs⟩ := h
  have hgraded : ∀ i, IsGluedFrom (s.graded i) (q (e i)) := by
    intro i
    obtain ⟨a⟩ := hs i
    exact (hinner (e i)).iso a.symm (fun _ => Iso.refl _)
  have hf := s.isGluedFrom_refine (m ∘ e) (fun i => q (e i)) hgraded
  let ef := (RepFunctorFiltration.refinementIndexEquiv (m ∘ e)).trans
    ((Equiv.sigmaCongrLeft e).trans (RepFunctorFiltration.refinementIndexEquiv m).symm)
  have hp : RepFunctorFiltration.flattenPieces (m ∘ e) (fun i => q (e i)) ∘ ef.symm =
      RepFunctorFiltration.flattenPieces m q := by
    funext j
    obtain ⟨i, rfl⟩ := ef.surjective j
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    simp only [RepFunctorFiltration.flattenPieces, ef, Equiv.trans_apply]
    exact (congrArg (fun a : Σ i, Fin (m i) => q a.1 a.2)
      ((RepFunctorFiltration.refinementIndexEquiv m).apply_symm_apply
        ((Equiv.sigmaCongrLeft e)
          ((RepFunctorFiltration.refinementIndexEquiv (m ∘ e)) i)))).symm
  rw [← hp]
  exact hf.reindex ef.symm

end Langlands
