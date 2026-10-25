import Langlands.Global.AdelicFunctoriality.IdeleClassNormLawsStatement
import Langlands.Global.AdelicFunctoriality.FinitePlaceDegreeTransfer

/-! # The norm of an included idele class, and lifting ideles through the norm -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped NumberField

universe u v

section Inclusion

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The completed embedding used by the finite-adele inclusion at `q` is the completed
embedding at any finite place of `K` below `q`. -/
theorem completionMap_under_eq (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [q.asIdeal.LiesOver p.asIdeal] (x : FiniteAdeleRing (𝓞 K) K) :
    FiniteExtension.completionMap (q.under (𝓞 K)) q (x (q.under (𝓞 K))) =
      FiniteExtension.completionMap p q (x p) := by
  have h : q.under (𝓞 K) = p := HeightOneSpectrum.ext (q.asIdeal.over_def p.asIdeal).symm
  subst h
  rfl

omit [NumberField K] [NumberField L] in
/-- The completed embedding used by the infinite-adele inclusion at `q` is the completed
embedding at the infinite place of `K` below `q`. -/
theorem infiniteCompletionMap_comap_eq (p : InfinitePlace K) (q : InfinitePlace L)
    [q.LiesOver p] (x : InfiniteAdeleRing K) :
    infiniteCompletionMap (algebraMap K L) q (x (q.comap (algebraMap K L))) =
      NumberField.LiesOver.completionMap (x p) := by
  have h : q.comap (algebraMap K L) = p := InfinitePlace.LiesOver.comap_eq q p
  subst h
  rfl

open scoped FiniteExtension in
/-- The finite-adele norm of an included finite adele is its `[L : K]`-th power. -/
theorem finiteAdeleNorm_finiteAdeleInclusion (x : FiniteAdeleRing (𝓞 K) K) :
    finiteAdeleNorm (K := K) (L := L) (finiteAdeleInclusion x) = x ^ Module.finrank K L := by
  apply FiniteAdeleRing.ext
  intro p
  rw [finiteAdeleNorm_apply]
  calc ∏ q : FinitePlacesAbove L p,
        FiniteExtension.localNorm p q.1 (finiteAdeleInclusion x q.1)
      = ∏ q : FinitePlacesAbove L p,
          x p ^ Module.finrank (p.adicCompletion K) (q.1.adicCompletion L) := by
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [finiteAdeleInclusion_apply, completionMap_under_eq p q.1 x,
          FiniteExtension.localNorm_algebraMap]
    _ = x p ^ Module.finrank K L := by
        rw [Finset.prod_pow_eq_pow_sum, finiteLocalDegree_sum]
    _ = (x ^ Module.finrank K L) p := rfl

open scoped NumberField.LiesOver InfiniteExtension in
/-- The infinite-adele norm of an included infinite adele is its `[L : K]`-th power. -/
theorem infiniteAdeleNorm_infiniteAdeleMap (x : InfiniteAdeleRing K) :
    infiniteAdeleNorm (K := K) (L := L) (infiniteAdeleMap (algebraMap K L) x) =
      x ^ Module.finrank K L := by
  funext p
  change ∏ q : InfinitePlacesAbove L p, InfiniteExtension.localNorm p q.1
      (infiniteCompletionMap (algebraMap K L) q.1 (x (q.1.comap (algebraMap K L)))) = _
  calc ∏ q : InfinitePlacesAbove L p, InfiniteExtension.localNorm p q.1
        (infiniteCompletionMap (algebraMap K L) q.1 (x (q.1.comap (algebraMap K L))))
      = ∏ q : InfinitePlacesAbove L p, x p ^ Module.finrank p.Completion q.1.Completion := by
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [infiniteCompletionMap_comap_eq p q.1 x, InfiniteExtension.localNorm_algebraMap]
    _ = x p ^ Module.finrank K L := by
        rw [Finset.prod_pow_eq_pow_sum, infiniteLocalDegree_sum]
    _ = (x ^ Module.finrank K L) p := rfl

/-- The adelic norm of an included adele is its `[L : K]`-th power. -/
theorem adeleNorm_adeleInclusion (x : AdeleRing (𝓞 K) K) :
    adeleNorm (K := K) (L := L) (adeleInclusion x) = x ^ Module.finrank K L :=
  Prod.ext (infiniteAdeleNorm_infiniteAdeleMap x.1) (finiteAdeleNorm_finiteAdeleInclusion x.2)

/-- The norm of an included idele is its `[L : K]`-th power. -/
theorem ideleNorm_ideleInclusion (a : IdeleGroup (𝓞 K) K) :
    ideleNorm (K := K) (L := L) (ideleInclusion a) = a ^ Module.finrank K L := by
  apply Units.ext
  rw [ideleNorm_val, ideleInclusion_val, adeleNorm_adeleInclusion, Units.val_pow_eq_pow_val]

end Inclusion

/-- The norm of the class of an included idele class is its `[L : K]`-th power. -/
theorem ideleClassNormInclusionPower : IdeleClassNormInclusionPower.{u, v} := by
  intro K L _ _ _ _ _ x
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [ideleClassInclusion_mk, ideleClassNorm_mk, ideleNorm_ideleInclusion]
    rfl

section Construction

variable {E : Type v} [Field E] [NumberField E]

/-- The idele with infinite coordinates `a w` and finite coordinates `c w`, for a family `c`
of local units which, together with their inverses, are integral at almost all places. -/
def ideleOfLocalUnits (a : ∀ w : InfinitePlace E, (w.Completion)ˣ)
    (c : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (hc : ∀ᶠ w in cofinite, (c w : w.adicCompletion E) ∈ w.adicCompletionIntegers E)
    (hc' : ∀ᶠ w in cofinite,
      (((c w)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ∈ w.adicCompletionIntegers E) :
    IdeleGroup (𝓞 E) E where
  val := ((fun w => (a w : w.Completion) : InfiniteAdeleRing E),
    (RestrictedProduct.mk (fun w => (c w : w.adicCompletion E)) hc : FiniteAdeleRing (𝓞 E) E))
  inv := ((fun w => (((a w)⁻¹ : (w.Completion)ˣ) : w.Completion) : InfiniteAdeleRing E),
    (RestrictedProduct.mk (fun w => (((c w)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E))
      hc' : FiniteAdeleRing (𝓞 E) E))
  val_inv := Prod.ext (funext fun w => Units.mul_inv (a w))
    (FiniteAdeleRing.ext E fun w => Units.mul_inv (c w))
  inv_val := Prod.ext (funext fun w => Units.inv_mul (a w))
    (FiniteAdeleRing.ext E fun w => Units.inv_mul (c w))

@[simp] theorem ideleOfLocalUnits_infinite (a : ∀ w : InfinitePlace E, (w.Completion)ˣ)
    (c : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (hc hc')
    (w : InfinitePlace E) :
    ((ideleOfLocalUnits a c hc hc' : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).1 w = a w :=
  rfl

@[simp] theorem ideleOfLocalUnits_finite (a : ∀ w : InfinitePlace E, (w.Completion)ˣ)
    (c : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (hc hc')
    (w : HeightOneSpectrum (𝓞 E)) :
    ((ideleOfLocalUnits a c hc hc' : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).2 w = c w :=
  rfl

/-- Transport of a local unit at a finite place along an equality of places. -/
def finiteUnitTransport {w w' : HeightOneSpectrum (𝓞 E)} (h : w = w')
    (x : (w.adicCompletion E)ˣ) : (w'.adicCompletion E)ˣ :=
  h ▸ x

theorem finiteUnitTransport_inv {w w' : HeightOneSpectrum (𝓞 E)} (h : w = w')
    (x : (w.adicCompletion E)ˣ) :
    (finiteUnitTransport h x)⁻¹ = finiteUnitTransport h x⁻¹ := by
  subst h
  rfl

theorem finiteUnitTransport_mem_iff {w w' : HeightOneSpectrum (𝓞 E)} (h : w = w')
    (x : (w.adicCompletion E)ˣ) :
    ((finiteUnitTransport h x : (w'.adicCompletion E)ˣ) : w'.adicCompletion E) ∈
        w'.adicCompletionIntegers E ↔
      (x : w.adicCompletion E) ∈ w.adicCompletionIntegers E := by
  subst h
  rfl

/-- Transport of a local unit at an infinite place along an equality of places. -/
def infiniteUnitTransport {w w' : InfinitePlace E} (h : w = w') (x : (w.Completion)ˣ) :
    (w'.Completion)ˣ :=
  h ▸ x

end Construction

section Lifting

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

open scoped Classical in
/-- The finite coordinates of the lift: the unit `c p` at the chosen place `wf p` above each
finite place `p`, and `1` at every other place. -/
def liftFiniteCoordinates (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (c : ∀ p : HeightOneSpectrum (𝓞 K), ((wf p).1.adicCompletion L)ˣ)
    (q : HeightOneSpectrum (𝓞 L)) : (q.adicCompletion L)ˣ :=
  if h : (wf (q.under (𝓞 K))).1 = q then finiteUnitTransport h (c (q.under (𝓞 K))) else 1

open scoped Classical in
/-- The infinite coordinates of the lift: the unit `d v` at the chosen place `wi v` above each
infinite place `v`, and `1` at every other place. -/
def liftInfiniteCoordinates (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v)
    (d : ∀ v : InfinitePlace K, ((wi v).1.Completion)ˣ)
    (w : InfinitePlace L) : (w.Completion)ˣ :=
  if h : (wi (w.comap (algebraMap K L))).1 = w then
    infiniteUnitTransport h (d (w.comap (algebraMap K L)))
  else 1

omit [NumberField K] in
theorem liftFiniteCoordinates_self (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (c : ∀ p : HeightOneSpectrum (𝓞 K), ((wf p).1.adicCompletion L)ˣ)
    (p : HeightOneSpectrum (𝓞 K)) :
    liftFiniteCoordinates wf c (wf p).1 = c p := by
  have key : ∀ (p' : HeightOneSpectrum (𝓞 K)) (hp : p' = p) (h : (wf p').1 = (wf p).1),
      finiteUnitTransport h (c p') = c p := by
    intro p' hp h
    subst hp
    rfl
  have h : (wf ((wf p).1.under (𝓞 K))).1 = (wf p).1 := by
    rw [finitePlacesAbove_under p (wf p)]
  unfold liftFiniteCoordinates
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact key _ (finitePlacesAbove_under p (wf p)) h

omit [NumberField K] in
theorem liftFiniteCoordinates_of_ne
    (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (c : ∀ p : HeightOneSpectrum (𝓞 K), ((wf p).1.adicCompletion L)ˣ)
    (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p) (hq : q ≠ wf p) :
    liftFiniteCoordinates wf c q.1 = 1 := by
  have h : ¬ (wf (q.1.under (𝓞 K))).1 = q.1 := by
    rw [finitePlacesAbove_under p q]
    exact fun h => hq (Subtype.ext h).symm
  unfold liftFiniteCoordinates
  rw [dite_eq_right_of_eq_false (eq_false h)]

omit [NumberField K] in
theorem liftInfiniteCoordinates_self (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v)
    (d : ∀ v : InfinitePlace K, ((wi v).1.Completion)ˣ) (v : InfinitePlace K) :
    liftInfiniteCoordinates wi d (wi v).1 = d v := by
  have key : ∀ (v' : InfinitePlace K) (hv : v' = v) (h : (wi v').1 = (wi v).1),
      infiniteUnitTransport h (d v') = d v := by
    intro v' hv h
    subst hv
    rfl
  have hv : (wi v).1.comap (algebraMap K L) = v := InfinitePlace.LiesOver.comap_eq (wi v).1 v
  have h : (wi ((wi v).1.comap (algebraMap K L))).1 = (wi v).1 := by rw [hv]
  unfold liftInfiniteCoordinates
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact key _ hv h

omit [NumberField K] in
theorem liftInfiniteCoordinates_of_ne (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v)
    (d : ∀ v : InfinitePlace K, ((wi v).1.Completion)ˣ) (v : InfinitePlace K)
    (q : InfinitePlacesAbove L v) (hq : q ≠ wi v) :
    liftInfiniteCoordinates wi d q.1 = 1 := by
  have h : ¬ (wi (q.1.comap (algebraMap K L))).1 = q.1 := by
    rw [InfinitePlace.LiesOver.comap_eq q.1 v]
    exact fun h => hq (Subtype.ext h).symm
  unfold liftInfiniteCoordinates
  rw [dite_eq_right_of_eq_false (eq_false h)]

theorem liftFiniteCoordinates_eventually
    (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (c : ∀ p : HeightOneSpectrum (𝓞 K), ((wf p).1.adicCompletion L)ˣ)
    (hc : ∀ᶠ p in cofinite,
      (c p : (wf p).1.adicCompletion L) ∈ (wf p).1.adicCompletionIntegers L ∧
        (((c p)⁻¹ : ((wf p).1.adicCompletion L)ˣ) : (wf p).1.adicCompletion L) ∈
          (wf p).1.adicCompletionIntegers L) :
    ∀ᶠ q in cofinite,
      (liftFiniteCoordinates wf c q : q.adicCompletion L) ∈ q.adicCompletionIntegers L ∧
        (((liftFiniteCoordinates wf c q)⁻¹ : (q.adicCompletion L)ˣ) : q.adicCompletion L) ∈
          q.adicCompletionIntegers L := by
  filter_upwards [(tendsto_under_cofinite (K := K) (L := L)).eventually hc] with q hq
  by_cases h : (wf (q.under (𝓞 K))).1 = q
  · have hq' : liftFiniteCoordinates wf c q = finiteUnitTransport h (c (q.under (𝓞 K))) := by
      unfold liftFiniteCoordinates
      rw [dite_eq_left_of_eq_true (eq_true h)]
    rw [hq', finiteUnitTransport_inv, finiteUnitTransport_mem_iff, finiteUnitTransport_mem_iff]
    exact hq
  · have hq' : liftFiniteCoordinates wf c q = 1 := by
      unfold liftFiniteCoordinates
      rw [dite_eq_right_of_eq_false (eq_false h)]
    rw [hq', inv_one, Units.val_one]
    exact ⟨one_mem _, one_mem _⟩

/-- **Lifting criterion.** An idele of `K` is a norm from `L` as soon as each of its
coordinates is the local norm of a unit at one chosen place above it, provided the chosen
finite units are integral units at almost all places. -/
theorem mem_range_ideleNorm_of_local
    (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v)
    (a : IdeleGroup (𝓞 K) K)
    (c : ∀ p : HeightOneSpectrum (𝓞 K), ((wf p).1.adicCompletion L)ˣ)
    (hc : ∀ᶠ p in cofinite,
      (c p : (wf p).1.adicCompletion L) ∈ (wf p).1.adicCompletionIntegers L ∧
        (((c p)⁻¹ : ((wf p).1.adicCompletion L)ˣ) : (wf p).1.adicCompletion L) ∈
          (wf p).1.adicCompletionIntegers L)
    (hcn : ∀ p, FiniteExtension.localNorm p (wf p).1 (c p : (wf p).1.adicCompletion L) =
      (a : AdeleRing (𝓞 K) K).2 p)
    (d : ∀ v : InfinitePlace K, ((wi v).1.Completion)ˣ)
    (hdn : ∀ v, InfiniteExtension.localNorm v (wi v).1 (d v : (wi v).1.Completion) =
      (a : AdeleRing (𝓞 K) K).1 v) :
    a ∈ (ideleNorm (K := K) (L := L)).toMonoidHom.range := by
  have hb := liftFiniteCoordinates_eventually wf c hc
  refine ⟨ideleOfLocalUnits (liftInfiniteCoordinates wi d) (liftFiniteCoordinates wf c)
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2), ?_⟩
  apply Units.ext
  apply Prod.ext
  · funext v
    change ∏ q : InfinitePlacesAbove L v, InfiniteExtension.localNorm v q.1
        (liftInfiniteCoordinates wi d q.1 : q.1.Completion) = _
    rw [Finset.prod_eq_single (wi v)]
    · rw [liftInfiniteCoordinates_self, hdn]
    · intro q _ hq
      rw [liftInfiniteCoordinates_of_ne wi d v q hq, Units.val_one, map_one]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · apply FiniteAdeleRing.ext
    intro p
    change ∏ q : FinitePlacesAbove L p, FiniteExtension.localNorm p q.1
        (liftFiniteCoordinates wf c q.1 : q.1.adicCompletion L) = _
    rw [Finset.prod_eq_single (wf p)]
    · rw [liftFiniteCoordinates_self, hcn]
    · intro q _ hq
      rw [liftFiniteCoordinates_of_ne wf c p q hq, Units.val_one, map_one]
    · intro h
      exact absurd (Finset.mem_univ _) h

end Lifting

end Langlands.Global.AdelicFunctoriality
