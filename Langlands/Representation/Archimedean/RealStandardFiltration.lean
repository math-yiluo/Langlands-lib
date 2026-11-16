import Langlands.Representation.Archimedean.RealRankOneStepFiltration
import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Mathlib.Data.Sigma.Order

/-!
# Filtrations of real standard modules by standard modules

`RealAdjacentFiltration` asks for finitely many linear maps `q j` into the `O(n)`-finite
functions of a real standard module, each an intertwiner modulo the span of the ranges of the
earlier maps (`IsRealIntertwinerModulo`), with ranges spanning everything. This file isolates
that notion for an arbitrary target list `ds`, an arbitrary finite linearly ordered index type
and an arbitrary condition `P` on the lists of the pieces (`HasFiltration`), and proves the
rules used to build such filtrations:

* `HasFiltration.self`: the one-piece filtration by the identity;
* `HasFiltration.mono`: weakening the condition on the pieces;
* `HasFiltration.bind`: refinement — filtering every piece again and ordering the new pieces
  lexicographically;
* `HasFiltration.map`: pushforward along a surjective intertwiner;
* `HasFiltration.congr`: transport between two lists with the same `O(n)`-finite functions;
* `realAdjacentFiltration_iff`: `RealAdjacentFiltration n pre post x y` is `HasFiltration` for
  the condition `IsAdjacentPiece pre post x y`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace RealStandardFiltration

/-- The `O(n)`-finite functions of the standard module of the real blocks `ds` on
`GL_n(ℝ)`. -/
abbrev KF (n : ℕ) (ds : List RealBlock) : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) :=
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

variable {n : ℕ}

/-! ## Intertwiners modulo a subspace -/

/-- Enlarging the subspace keeps an intertwiner modulo it. -/
theorem modulo_mono {ds es : List RealBlock} {M M' : Submodule ℂ (KF n es)}
    {q : KF n ds →ₗ[ℂ] KF n es} (hq : IsRealIntertwinerModulo n ds es M q) (h : M ≤ M') :
    IsRealIntertwinerModulo n ds es M' q :=
  ⟨fun k f => let ⟨hf, hg, hm⟩ := hq.1 k f; ⟨hf, hg, h hm⟩,
    fun X f => let ⟨hf, hg, hm⟩ := hq.2 X f; ⟨hf, hg, h hm⟩⟩

/-- The composite of an intertwiner `q` modulo `M` with an intertwiner `r` modulo `M'` is an
intertwiner modulo `M ⊔ q(M')`. -/
theorem modulo_comp {fs es ds : List RealBlock} {M : Submodule ℂ (KF n ds)}
    {M' : Submodule ℂ (KF n es)} {q : KF n es →ₗ[ℂ] KF n ds} {r : KF n fs →ₗ[ℂ] KF n es}
    (hq : IsRealIntertwinerModulo n es ds M q) (hr : IsRealIntertwinerModulo n fs es M' r) :
    IsRealIntertwinerModulo n fs ds (M ⊔ M'.map q) (q ∘ₗ r) := by
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, hg, hm'⟩ := hr.1 k f
    obtain ⟨hg', hh, hm⟩ := hq.1 k (r f)
    refine ⟨hf, hh, ?_⟩
    have heq : (q ∘ₗ r) ⟨_, hf⟩ - ⟨_, hh⟩ =
        (q ⟨_, hg'⟩ - ⟨_, hh⟩) + q (r ⟨_, hf⟩ - ⟨_, hg'⟩) := by
      rw [map_sub, LinearMap.comp_apply]
      abel
    have hmem : (q ∘ₗ r) ⟨_, hf⟩ - ⟨_, hh⟩ ∈ M ⊔ M'.map q := by
      rw [heq]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hm)
        (Submodule.mem_sup_right (Submodule.mem_map_of_mem hm'))
    exact hmem
  · obtain ⟨hf, hg, hm'⟩ := hr.2 X f
    obtain ⟨hg', hh, hm⟩ := hq.2 X (r f)
    refine ⟨hf, hh, ?_⟩
    have heq : (q ∘ₗ r) ⟨_, hf⟩ - ⟨_, hh⟩ =
        (q ⟨_, hg'⟩ - ⟨_, hh⟩) + q (r ⟨_, hf⟩ - ⟨_, hg'⟩) := by
      rw [map_sub, LinearMap.comp_apply]
      abel
    have hmem : (q ∘ₗ r) ⟨_, hf⟩ - ⟨_, hh⟩ ∈ M ⊔ M'.map q := by
      rw [heq]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hm)
        (Submodule.mem_sup_right (Submodule.mem_map_of_mem hm'))
    exact hmem

/-- The composite of an intertwiner `q` modulo `M` with an exact intertwiner `r` (modulo `⊥`)
is an intertwiner modulo `M`. -/
theorem modulo_comp_bot {fs es ds : List RealBlock} {M : Submodule ℂ (KF n ds)}
    {q : KF n es →ₗ[ℂ] KF n ds} {r : KF n fs →ₗ[ℂ] KF n es}
    (hq : IsRealIntertwinerModulo n es ds M q) (hr : IsRealIntertwinerModulo n fs es ⊥ r) :
    IsRealIntertwinerModulo n fs ds M (q ∘ₗ r) :=
  modulo_mono (modulo_comp hq hr) (by rw [Submodule.map_bot, sup_bot_eq])

/-- The identity is an exact intertwiner. -/
theorem modulo_id (ds : List RealBlock) :
    IsRealIntertwinerModulo n ds ds ⊥ (LinearMap.id : KF n ds →ₗ[ℂ] KF n ds) :=
  ⟨fun k f => ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule n ds f.2 k.2,
      rightTranslation_mem_kFiniteFunctions_realStandardModule n ds f.2 k.2, by simp⟩,
    fun X f => ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule n ds f.2 X,
      rightDerivative_mem_kFiniteFunctions_realStandardModule n ds f.2 X, by simp⟩⟩

/-- The identification of the `O(n)`-finite functions of two lists with the same
`O(n)`-finite functions. -/
def ofEqMap {ds es : List RealBlock} (h : KF n ds = KF n es) : KF n ds →ₗ[ℂ] KF n es :=
  (LinearEquiv.ofEq _ _ h).toLinearMap

@[simp]
theorem ofEqMap_apply_coe {ds es : List RealBlock} (h : KF n ds = KF n es) (f : KF n ds) :
    ((ofEqMap h f : KF n es) : Langlands.GeneralLinear n ℝ → ℂ) = f :=
  rfl

theorem ofEqMap_surjective {ds es : List RealBlock} (h : KF n ds = KF n es) :
    Function.Surjective (ofEqMap h) :=
  (LinearEquiv.ofEq _ _ h).surjective

/-- The identification of equal spaces of `O(n)`-finite functions is an exact intertwiner. -/
theorem modulo_ofEqMap {ds es : List RealBlock} (h : KF n ds = KF n es) :
    IsRealIntertwinerModulo n ds es ⊥ (ofEqMap h) :=
  ⟨fun k f => ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule n ds f.2 k.2,
      rightTranslation_mem_kFiniteFunctions_realStandardModule n es (ofEqMap h f).2 k.2, by
        rw [Submodule.mem_bot, sub_eq_zero]
        rfl⟩,
    fun X f => ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule n ds f.2 X,
      rightDerivative_mem_kFiniteFunctions_realStandardModule n es (ofEqMap h f).2 X, by
        rw [Submodule.mem_bot, sub_eq_zero]
        rfl⟩⟩

/-- **Descent.** Let `q` be an intertwiner modulo `M` out of `K(es)` that factors as
`q = q' ∘ π` through a surjective exact intertwiner `π : K(es) → K(es')`. Then `q'` is an
intertwiner modulo `M`. -/
theorem modulo_of_comp_surjective {es es' ds : List RealBlock} {M : Submodule ℂ (KF n ds)}
    {q : KF n es →ₗ[ℂ] KF n ds} {π : KF n es →ₗ[ℂ] KF n es'} {q' : KF n es' →ₗ[ℂ] KF n ds}
    (hq : IsRealIntertwinerModulo n es ds M q) (hπ : IsRealIntertwinerModulo n es es' ⊥ π)
    (hsurj : Function.Surjective π) (hfac : q' ∘ₗ π = q) :
    IsRealIntertwinerModulo n es' ds M q' := by
  have hfac' : ∀ f, q' (π f) = q f := fun f => by rw [← hfac, LinearMap.comp_apply]
  refine ⟨fun k g => ?_, fun X g => ?_⟩
  · obtain ⟨f, rfl⟩ := hsurj g
    obtain ⟨hf, hg, hm0⟩ := hπ.1 k f
    obtain ⟨_, hh, hm⟩ := hq.1 k f
    rw [Submodule.mem_bot, sub_eq_zero] at hm0
    have hh' : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (q' (π f) : Langlands.GeneralLinear n ℝ → ℂ) ∈
          KF n ds := by rw [hfac']; exact hh
    refine ⟨hg, hh', ?_⟩
    have h1 : q' ⟨_, hg⟩ = q ⟨_, hf⟩ := by rw [← hm0, hfac']
    have h2 : (⟨_, hh'⟩ : KF n ds) = ⟨_, hh⟩ := Subtype.ext (by simp only [hfac'])
    rw [h1, h2]
    exact hm
  · obtain ⟨f, rfl⟩ := hsurj g
    obtain ⟨hf, hg, hm0⟩ := hπ.2 X f
    obtain ⟨_, hh, hm⟩ := hq.2 X f
    rw [Submodule.mem_bot, sub_eq_zero] at hm0
    have hh' : rightDerivative (matrixModel ℝ n) X
        (q' (π f) : Langlands.GeneralLinear n ℝ → ℂ) ∈ KF n ds := by rw [hfac']; exact hh
    refine ⟨hg, hh', ?_⟩
    have h1 : q' ⟨_, hg⟩ = q ⟨_, hf⟩ := by rw [← hm0, hfac']
    have h2 : (⟨_, hh'⟩ : KF n ds) = ⟨_, hh⟩ := Subtype.ext (by simp only [hfac'])
    rw [h1, h2]
    exact hm

/-! ## Filtrations -/

/-- A filtration of the `O(n)`-finite functions of the standard module of `ds`, indexed by a
linear order `ι`: linear maps `q j` out of the `O(n)`-finite functions of the standard modules
of the lists `es j`, every `q j` an intertwiner modulo the span of the ranges of the `q i` with
`i < j`, and the ranges of all `q j` spanning everything. -/
def IsFiltration {ι : Type} [LinearOrder ι] (n : ℕ) (ds : List RealBlock)
    (es : ι → List RealBlock) (q : ∀ j, KF n (es j) →ₗ[ℂ] KF n ds) : Prop :=
  (∀ j, IsRealIntertwinerModulo n (es j) ds
      (⨆ (i : ι) (_ : i < j), LinearMap.range (q i)) (q j)) ∧
    ⨆ j, LinearMap.range (q j) = ⊤

/-- The `O(n)`-finite functions of the standard module of `ds` on `GL_n(ℝ)` have a filtration
(`IsFiltration`) indexed by a finite linear order whose pieces come from lists satisfying
`P`. -/
def HasFiltration (n : ℕ) (ds : List RealBlock) (P : List RealBlock → Prop) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : LinearOrder ι) (es : ι → List RealBlock)
    (q : ∀ j, KF n (es j) →ₗ[ℂ] KF n ds), (∀ j, P (es j)) ∧ IsFiltration n ds es q

/-- **One piece.** The identity is a filtration with the single piece `ds`. -/
theorem HasFiltration.self {ds : List RealBlock} {P : List RealBlock → Prop} (h : P ds) :
    HasFiltration n ds P := by
  refine ⟨Unit, inferInstance, inferInstance, fun _ => ds, fun _ => LinearMap.id,
    fun _ => h, fun j => modulo_mono (modulo_id ds) bot_le, ?_⟩
  exact eq_top_iff.2 fun f _ =>
    Submodule.mem_iSup_of_mem () ⟨f, rfl⟩

/-- **Weakening.** -/
theorem HasFiltration.mono {ds : List RealBlock} {P Q : List RealBlock → Prop}
    (h : HasFiltration n ds P) (hPQ : ∀ es, P es → Q es) : HasFiltration n ds Q := by
  obtain ⟨ι, hι, hlo, es, q, hP, hq⟩ := h
  exact ⟨ι, hι, hlo, es, q, fun j => hPQ _ (hP j), hq⟩

/-- The ranges of the composites `q ∘ r i` span the range of `q` when the ranges of the `r i`
span everything. -/
theorem iSup_range_comp {κ : Type} {fs : κ → List RealBlock} {es ds : List RealBlock}
    (q : KF n es →ₗ[ℂ] KF n ds) (r : ∀ i, KF n (fs i) →ₗ[ℂ] KF n es)
    (hr : ⨆ i, LinearMap.range (r i) = ⊤) :
    ⨆ i, LinearMap.range (q ∘ₗ r i) = LinearMap.range q := by
  rw [← Submodule.map_top, ← hr, Submodule.map_iSup]
  simp only [LinearMap.range_comp]

/-- **Refinement.** Filtering every piece of a filtration again gives a filtration, the new
pieces ordered lexicographically. -/
theorem HasFiltration.bind {ds : List RealBlock} {P Q : List RealBlock → Prop}
    (h : HasFiltration n ds P) (hP : ∀ es, P es → HasFiltration n es Q) :
    HasFiltration n ds Q := by
  obtain ⟨ι, hι, hlo, es, q, hPes, hq, hspan⟩ := h
  choose κ hκF hκL fs r hfsQ hr using fun j => hP (es j) (hPes j)
  let : ∀ j, Fintype (κ j) := hκF
  let : ∀ j, LinearOrder (κ j) := hκL
  let fs' : Lex (Σ j, κ j) → List RealBlock := fun p => fs (ofLex p).1 (ofLex p).2
  let q' : ∀ p : Lex (Σ j, κ j), KF n (fs' p) →ₗ[ℂ] KF n ds :=
    fun p => q (ofLex p).1 ∘ₗ r (ofLex p).1 (ofLex p).2
  -- the range of `q j` is spanned by the ranges of the new pieces over `j`
  have hrange : ∀ j, LinearMap.range (q j) = ⨆ i, LinearMap.range (q' (toLex ⟨j, i⟩)) :=
    fun j => (iSup_range_comp (q j) (r j) (hr j).2).symm
  refine ⟨Lex (Σ j, κ j), inferInstance, inferInstance, fs', q', fun p => hfsQ _ _, fun p => ?_, ?_⟩
  · obtain ⟨j, i⟩ := p
    have hcomp := modulo_comp (hq j) ((hr j).1 i)
    refine modulo_mono hcomp (sup_le ?_ ?_)
    · refine iSup₂_le fun j' hj' => ?_
      rw [hrange j']
      refine iSup_le fun i' => ?_
      exact le_iSup₂_of_le (toLex ⟨j', i'⟩) (Sigma.Lex.left (r := (· < ·)) (s := fun _ => (· < ·)) _ _ hj') le_rfl
    · rw [Submodule.map_iSup]
      refine iSup_le fun i' => ?_
      rw [Submodule.map_iSup]
      refine iSup_le fun hi' => ?_
      rw [← LinearMap.range_comp]
      exact le_iSup₂_of_le (toLex ⟨j, i'⟩) (Sigma.Lex.right (r := (· < ·)) (s := fun _ => (· < ·)) _ _ hi') le_rfl
  · refine eq_top_iff.2 ?_
    rw [← hspan]
    refine iSup_le fun j => ?_
    rw [hrange j]
    exact iSup_le fun i => le_iSup_of_le (toLex ⟨j, i⟩) le_rfl

/-- **Pushforward.** A filtration of `K(ds)` pushed forward along a surjective exact
intertwiner `T : K(ds) → K(ds')` is a filtration of `K(ds')` with the same pieces. -/
theorem HasFiltration.map {ds ds' : List RealBlock} {P : List RealBlock → Prop}
    (h : HasFiltration n ds P) (T : KF n ds →ₗ[ℂ] KF n ds')
    (hT : IsRealIntertwinerModulo n ds ds' ⊥ T) (hsurj : Function.Surjective T) :
    HasFiltration n ds' P := by
  obtain ⟨ι, hι, hlo, es, q, hPes, hq, hspan⟩ := h
  refine ⟨ι, hι, hlo, es, fun j => T ∘ₗ q j, hPes, fun j => ?_, ?_⟩
  · refine modulo_mono (modulo_comp hT (hq j)) (sup_le bot_le ?_)
    rw [Submodule.map_iSup]
    refine iSup_le fun i => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hi => ?_
    rw [← LinearMap.range_comp]
    exact le_iSup₂_of_le i hi le_rfl
  · have := iSup_range_comp (fs := es) T q hspan
    rw [this, LinearMap.range_eq_top.2 hsurj]

/-- **Transport.** Two lists with the same `O(n)`-finite functions have the same
filtrations. -/
theorem HasFiltration.congr {ds ds' : List RealBlock} {P : List RealBlock → Prop}
    (h : HasFiltration n ds P) (hKF : KF n ds = KF n ds') : HasFiltration n ds' P :=
  h.map (ofEqMap hKF) (modulo_ofEqMap hKF) (ofEqMap_surjective hKF)

/-- **Descent of pieces.** If every piece list `es` satisfying `P` has the same `O(n)`-finite
functions as some list satisfying `Q`, a filtration with `P`-pieces gives one with
`Q`-pieces. -/
theorem HasFiltration.of_eq_pieces {ds : List RealBlock} {P Q : List RealBlock → Prop}
    (h : HasFiltration n ds P) (hPQ : ∀ es, P es → ∃ es', Q es' ∧ KF n es' = KF n es) :
    HasFiltration n ds Q :=
  h.bind fun es hes =>
    let ⟨_, hQ, hKF⟩ := hPQ es hes
    (HasFiltration.self hQ).congr hKF

/-! ## Reindexing and adjacent filtrations -/

/-- Reindexing a filtration along an order isomorphism. -/
theorem IsFiltration.reindex {ι ι' : Type} [LinearOrder ι] [LinearOrder ι'] {ds : List RealBlock}
    {es : ι → List RealBlock} {q : ∀ j, KF n (es j) →ₗ[ℂ] KF n ds}
    (h : IsFiltration n ds es q) (e : ι' ≃o ι) :
    IsFiltration n ds (fun j => es (e j)) (fun j => q (e j)) := by
  obtain ⟨hq, hspan⟩ := h
  refine ⟨fun j => modulo_mono (hq (e j)) ?_, ?_⟩
  · refine iSup₂_le fun i hi => ?_
    have hi' : e.symm i < j := by rwa [← e.lt_iff_lt, e.apply_symm_apply]
    refine le_iSup₂_of_le (e.symm i) hi' ?_
    show LinearMap.range (q i) ≤ LinearMap.range (q (e (e.symm i)))
    rw [e.apply_symm_apply]
  · rw [← hspan]
    exact e.toEquiv.iSup_comp (g := fun i => LinearMap.range (q i))

/-- A piece of an adjacent filtration of `pre ++ x :: y :: post`: a list `pre ++ ws ++ post`
with `ws = [y, x]`, or with the exponent support of `ws` a permutation of that of `[x, y]` and
a strictly larger sum of squared weights, as in `RealAdjacentFiltration`. -/
def IsAdjacentPiece (pre post : List RealBlock) (x y : RealBlock) (es : List RealBlock) :
    Prop :=
  ∃ ws : List RealBlock, es = pre ++ ws ++ post ∧
    (ws = [y, x] ∨ ((realExponentSupport ws).Perm (realExponentSupport [x, y]) ∧
      realWeightSquareSum [x, y] < realWeightSquareSum ws))

/-- `RealAdjacentFiltration` is `HasFiltration` with adjacent pieces. -/
theorem realAdjacentFiltration_iff (n : ℕ) (pre post : List RealBlock) (x y : RealBlock) :
    RealAdjacentFiltration n pre post x y ↔
      HasFiltration n (pre ++ x :: y :: post) (IsAdjacentPiece pre post x y) := by
  constructor
  · rintro ⟨k, ws, q, hws, hq, hspan⟩
    exact ⟨Fin k, inferInstance, inferInstance, fun j => pre ++ ws j ++ post, q,
      fun j => ⟨ws j, rfl, hws j⟩, hq, hspan⟩
  · rintro ⟨ι, hι, hlo, es, q, hP, hfilt⟩
    choose ws hws hwsP using hP
    let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
    have hfilt' := hfilt.reindex e
    have hKF : ∀ j : Fin (Fintype.card ι), KF n (pre ++ ws (e j) ++ post) = KF n (es (e j)) :=
      fun j => by rw [← hws (e j)]
    let q' : ∀ j : Fin (Fintype.card ι),
        KF n (pre ++ ws (e j) ++ post) →ₗ[ℂ] KF n (pre ++ x :: y :: post) :=
      fun j => q (e j) ∘ₗ ofEqMap (hKF j)
    have hrange : ∀ j, LinearMap.range (q' j) = LinearMap.range (q (e j)) := fun j => by
      simp only [q', LinearMap.range_comp, LinearMap.range_eq_top.2 (ofEqMap_surjective (hKF j)),
        Submodule.map_top]
    refine ⟨Fintype.card ι, fun j => ws (e j), q', fun j => hwsP (e j), fun j => ?_, ?_⟩
    · have := modulo_comp_bot (hfilt'.1 j) (modulo_ofEqMap (hKF j))
      simpa only [hrange] using this
    · simpa only [hrange] using hfilt'.2

end RealStandardFiltration

end Langlands.Archimedean
