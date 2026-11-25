/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-!
# Degreewise subobjects of cochain complexes

Let `C` be a Grothendieck abelian category and `K` a cochain complex in `C`. A subobject of `K`
is in particular a degreewise family of subobjects of the objects `K.X n`, and we develop the
dictionary between the two points of view.

## Main definitions

- `HomologicalComplex.subobjectEval`: the map `Subobject K → Subobject (K.X n)` induced by the
  evaluation functor in degree `n`.
- `HomologicalComplex.subcomplexOfDegreewise`: the subobject of `K` attached to a degreewise
  family of subobjects which is stable under the differentials.
- `HomologicalComplex.subcomplexClosure`: the smallest subcomplex of `K` containing a given
  degreewise family of subobjects.

## Main results

- `HomologicalComplex.le_iff_forall_subobjectEval_le`: a subobject of `K` is determined by its
  degreewise evaluations, and the order is tested degreewise.
- `HomologicalComplex.subobjectEval_inf`, `HomologicalComplex.subobjectEval_sup`,
  `HomologicalComplex.subobjectEval_iSup`, `HomologicalComplex.subobjectEval_exists` and
  `HomologicalComplex.subobjectEval_pullback`: evaluation commutes with the lattice operations,
  and with image pushforward and pullback along a morphism of complexes.
- `HomologicalComplex.exactAt_subobject_iff`: a lattice-theoretic criterion for a subcomplex
  of `K` to be exact in a given degree.
-/

universe w v u

@[expose] public section

namespace HomologicalComplex

open CategoryTheory Limits Subobject

variable {C : Type u} [Category.{v} C] [Abelian C]

section Eval

variable (K : CochainComplex C ℤ) (n : ℤ)

/-- The evaluation functor in degree `n`, as a functor between categories of monomorphisms. -/
noncomputable def monoOverEval : MonoOver K ⥤ MonoOver (K.X n) :=
  MonoOver.lift (Over.post (HomologicalComplex.eval C (ComplexShape.up ℤ) n))
    (fun f => by
      have := f.property
      exact inferInstanceAs (Mono (f.obj.hom.f n)))

/-- The degreewise evaluation of subobjects of a cochain complex, as a functor. -/
noncomputable def subobjectEvalFunctor : Subobject K ⥤ Subobject (K.X n) :=
  Subobject.lower (monoOverEval K n)

/-- The evaluation in degree `n` of a subobject of a cochain complex. -/
noncomputable def subobjectEval : Subobject K → Subobject (K.X n) :=
  (subobjectEvalFunctor K n).obj

@[simp]
lemma subobjectEval_mk {L : CochainComplex C ℤ} (i : L ⟶ K) [Mono i] :
    subobjectEval K n (Subobject.mk i) = Subobject.mk (i.f n) :=
  rfl

lemma subobjectEval_eq_mk (S : Subobject K) :
    subobjectEval K n S = Subobject.mk (S.arrow.f n) := by
  simpa using subobjectEval_mk K n S.arrow

lemma monotone_subobjectEval : Monotone (subobjectEval K n) :=
  (subobjectEvalFunctor K n).monotone

variable {K n}

/-- The underlying object of `subobjectEval K n S` is the degree `n` part of `S`. -/
noncomputable def subobjectEvalUnderlyingIso (S : Subobject K) :
    ((subobjectEval K n S : C)) ≅ (S : CochainComplex C ℤ).X n :=
  eqToIso (congrArg (fun T : Subobject (K.X n) => (T : C)) (subobjectEval_eq_mk K n S)) ≪≫
    Subobject.underlyingIso _

@[reassoc (attr := simp)]
lemma subobjectEvalUnderlyingIso_hom_comp_arrow (S : Subobject K) :
    (subobjectEvalUnderlyingIso S).hom ≫ S.arrow.f n = (subobjectEval K n S).arrow := by
  rw [subobjectEvalUnderlyingIso, Iso.trans_hom, Category.assoc,
    underlyingIso_hom_comp_eq_mk, eqToIso.hom]
  exact Subobject.arrow_congr _ _ (subobjectEval_eq_mk K n S)

/-- Degreewise evaluation is jointly order-reflecting. -/
lemma le_iff_forall_subobjectEval_le (S T : Subobject K) :
    S ≤ T ↔ ∀ n, subobjectEval K n S ≤ subobjectEval K n T := by
  refine ⟨fun h n => monotone_subobjectEval K n h, fun h => ?_⟩
  have key : ∀ n, ∃ g : (S : CochainComplex C ℤ).X n ⟶ (T : CochainComplex C ℤ).X n,
      g ≫ T.arrow.f n = S.arrow.f n := fun n => by
    have hfac : (Subobject.mk (T.arrow.f n)).Factors (S.arrow.f n) := by
      rw [← mk_le_iff_factors, ← subobjectEval_eq_mk, ← subobjectEval_eq_mk]
      exact h n
    exact ⟨(Subobject.mk (T.arrow.f n)).factorThru _ hfac ≫ (underlyingIso (T.arrow.f n)).hom,
      by simp⟩
  choose g hg using key
  refine Subobject.le_of_comm { f := g, comm' := fun i j _ => ?_ } (by ext n; exact hg n)
  rw [← cancel_mono (T.arrow.f j), Category.assoc, ← (T.arrow).comm i j, ← Category.assoc,
    hg i, (S.arrow).comm i j, Category.assoc, hg j]

/-- A subobject of a cochain complex is determined by its degreewise evaluations. -/
lemma subobjectEval_injective :
    Function.Injective (fun (S : Subobject K) (n : ℤ) => subobjectEval K n S) := by
  intro S T h
  exact le_antisymm ((le_iff_forall_subobjectEval_le S T).2 (fun n => (congrFun h n).le))
    ((le_iff_forall_subobjectEval_le T S).2 (fun n => (congrFun h n).ge))

/-- A subobject of a cochain complex is stable under the differentials. -/
lemma exists_subobjectEval_le (S : Subobject K) (i j : ℤ) :
    (Subobject.«exists» (K.d i j)).obj (subobjectEval K i S) ≤ subobjectEval K j S := by
  rw [exists_le_iff, subobjectEval_eq_mk, subobjectEval_eq_mk, ← underlyingIso_hom_comp_eq_mk,
    Category.assoc, (S.arrow).comm i j, ← Category.assoc]
  exact factors_of_factors_right _ (mk_factors_self _)

end Eval

section OfDegreewise

variable (K : CochainComplex C ℤ) (W : ∀ n : ℤ, Subobject (K.X n))
  (hW : ∀ i j, (Subobject.«exists» (K.d i j)).obj (W i) ≤ W j)

/-- The subcomplex of `K` whose degree `n` part is `W n`, for a degreewise family `W` of
subobjects which is stable under the differentials. -/
@[simps]
noncomputable def ofDegreewiseSubobjects : CochainComplex C ℤ where
  X n := (W n : C)
  d i j := (W j).factorThru ((W i).arrow ≫ K.d i j) ((exists_le_iff _ _ _).1 (hW i j))
  shape i j h := by
    rw [← cancel_mono (W j).arrow, factorThru_arrow, zero_comp, K.shape i j h, comp_zero]
  d_comp_d' i j k _ _ := by
    rw [← cancel_mono (W k).arrow, Category.assoc, factorThru_arrow, ← Category.assoc,
      factorThru_arrow, Category.assoc, K.d_comp_d, comp_zero, zero_comp]

/-- The inclusion of `ofDegreewiseSubobjects K W hW` into `K`. -/
noncomputable def ofDegreewiseSubobjectsι : ofDegreewiseSubobjects K W hW ⟶ K where
  f n := (W n).arrow
  comm' _ _ _ := by simp

@[simp]
lemma ofDegreewiseSubobjectsι_f (n : ℤ) : (ofDegreewiseSubobjectsι K W hW).f n = (W n).arrow := rfl

instance : Mono (ofDegreewiseSubobjectsι K W hW) :=
  mono_of_mono_f _ (fun n => inferInstanceAs (Mono (W n).arrow))

/-- The subobject of `K` attached to a degreewise family `W` of subobjects which is stable
under the differentials. -/
noncomputable def subcomplexOfDegreewise : Subobject K :=
  Subobject.mk (ofDegreewiseSubobjectsι K W hW)

@[simp]
lemma subobjectEval_subcomplexOfDegreewise (n : ℤ) :
    subobjectEval K n (subcomplexOfDegreewise K W hW) = W n := by
  rw [subcomplexOfDegreewise, subobjectEval_mk]
  exact Subobject.mk_arrow (W n)

/-- The subcomplex attached to `W` is below `S` exactly when `W` is degreewise below `S`. -/
lemma subcomplexOfDegreewise_le_iff (S : Subobject K) :
    subcomplexOfDegreewise K W hW ≤ S ↔ ∀ n, W n ≤ subobjectEval K n S := by
  rw [le_iff_forall_subobjectEval_le]
  simp

/-- `S` is below the subcomplex attached to `W` exactly when `S` is degreewise below `W`. -/
lemma le_subcomplexOfDegreewise_iff (S : Subobject K) :
    S ≤ subcomplexOfDegreewise K W hW ↔ ∀ n, subobjectEval K n S ≤ W n := by
  rw [le_iff_forall_subobjectEval_le]
  simp

end OfDegreewise

section Lattice

variable (K : CochainComplex C ℤ)

/-- Degreewise evaluation commutes with binary intersections. -/
lemma subobjectEval_inf (S T : Subobject K) (n : ℤ) :
    subobjectEval K n (S ⊓ T) = subobjectEval K n S ⊓ subobjectEval K n T := by
  have hW : ∀ i j, (Subobject.«exists» (K.d i j)).obj
      (subobjectEval K i S ⊓ subobjectEval K i T) ≤
      subobjectEval K j S ⊓ subobjectEval K j T := fun i j =>
    le_inf ((exists_obj_mono _ inf_le_left).trans (exists_subobjectEval_le S i j))
      ((exists_obj_mono _ inf_le_right).trans (exists_subobjectEval_le T i j))
  have h : subcomplexOfDegreewise K _ hW = S ⊓ T :=
    le_antisymm (le_inf ((subcomplexOfDegreewise_le_iff K _ hW S).2 (fun _ => inf_le_left))
        ((subcomplexOfDegreewise_le_iff K _ hW T).2 (fun _ => inf_le_right)))
      ((le_subcomplexOfDegreewise_iff K _ hW (S ⊓ T)).2 (fun m =>
        le_inf (monotone_subobjectEval K m inf_le_left)
          (monotone_subobjectEval K m inf_le_right)))
  rw [← h, subobjectEval_subcomplexOfDegreewise]


/-- Degreewise evaluation commutes with binary unions. -/
lemma subobjectEval_sup (S T : Subobject K) (n : ℤ) :
    subobjectEval K n (S ⊔ T) = subobjectEval K n S ⊔ subobjectEval K n T := by
  have hW : ∀ i j, (Subobject.«exists» (K.d i j)).obj
      (subobjectEval K i S ⊔ subobjectEval K i T) ≤
      subobjectEval K j S ⊔ subobjectEval K j T := fun i j => by
    rw [exists_obj_sup]
    exact sup_le_sup (exists_subobjectEval_le S i j) (exists_subobjectEval_le T i j)
  have h : subcomplexOfDegreewise K _ hW = S ⊔ T :=
    le_antisymm ((subcomplexOfDegreewise_le_iff K _ hW (S ⊔ T)).2 (fun m =>
        sup_le (monotone_subobjectEval K m le_sup_left)
          (monotone_subobjectEval K m le_sup_right)))
      (sup_le ((le_subcomplexOfDegreewise_iff K _ hW S).2 (fun _ => le_sup_left))
        ((le_subcomplexOfDegreewise_iff K _ hW T).2 (fun _ => le_sup_right)))
  rw [← h, subobjectEval_subcomplexOfDegreewise]

variable [IsGrothendieckAbelian.{w} C]

/-- Degreewise evaluation commutes with arbitrary suprema. -/
lemma subobjectEval_iSup {ι : Type*} (S : ι → Subobject K) (n : ℤ) :
    subobjectEval K n (⨆ a, S a) = ⨆ a, subobjectEval K n (S a) := by
  have hW : ∀ i j, (Subobject.«exists» (K.d i j)).obj (⨆ a, subobjectEval K i (S a)) ≤
      ⨆ a, subobjectEval K j (S a) := fun i j => by
    rw [exists_obj_iSup]
    exact iSup_le (fun a =>
      (exists_subobjectEval_le (S a) i j).trans (le_iSup (fun b => subobjectEval K j (S b)) a))
  have h : subcomplexOfDegreewise K _ hW = ⨆ a, S a :=
    le_antisymm ((subcomplexOfDegreewise_le_iff K _ hW _).2 (fun m =>
        iSup_le (fun a => monotone_subobjectEval K m (le_iSup S a))))
      (iSup_le (fun a => (le_subcomplexOfDegreewise_iff K _ hW (S a)).2
        (fun m => le_iSup (fun b => subobjectEval K m (S b)) a)))
  rw [← h, subobjectEval_subcomplexOfDegreewise]

end Lattice

section Functoriality

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- Degreewise evaluation commutes with pullback along a morphism of complexes. -/
lemma subobjectEval_pullback (T : Subobject L) (n : ℤ) :
    subobjectEval K n ((Subobject.pullback φ).obj T) =
      (Subobject.pullback (φ.f n)).obj (subobjectEval L n T) := by
  rw [subobjectEval_eq_mk, subobjectEval_eq_mk]
  exact (Subobject.pullback_obj_mk
    ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_isPullback
      (Subobject.isPullback φ T))).symm


/-- Degreewise evaluation commutes with images. -/
lemma subobjectEval_imageSubobject (n : ℤ) :
    subobjectEval L n (imageSubobject φ) = imageSubobject (φ.f n) := by
  have := strongEpi_of_epi ((factorThruImage φ).f n)
  rw [show φ.f n = (factorThruImage φ).f n ≫ (image.ι φ).f n by
    rw [← HomologicalComplex.comp_f, image.fac], imageSubobject_eq_mk]
  exact subobjectEval_mk L n (image.ι φ)

/-- Degreewise evaluation commutes with image pushforward along a morphism of complexes. -/
lemma subobjectEval_exists (S : Subobject K) (n : ℤ) :
    subobjectEval L n ((Subobject.«exists» φ).obj S) =
      (Subobject.«exists» (φ.f n)).obj (subobjectEval K n S) := by
  rw [exists_obj_eq_imageSubobject, exists_obj_eq_imageSubobject, subobjectEval_imageSubobject,
    HomologicalComplex.comp_f]
  conv_rhs => rw [← subobjectEvalUnderlyingIso_hom_comp_arrow S, Category.assoc,
    imageSubobject_iso_comp]

end Functoriality

section Closure

variable (K : CochainComplex C ℤ) (W : ∀ n : ℤ, Subobject (K.X n))

/-- The family `n ↦ W n ⊔ (image of W (n - 1))` is stable under the differentials. -/
lemma exists_sup_exists_le (i j : ℤ) :
    (Subobject.«exists» (K.d i j)).obj
        (W i ⊔ (Subobject.«exists» (K.d (i - 1) i)).obj (W (i - 1))) ≤
      W j ⊔ (Subobject.«exists» (K.d (j - 1) j)).obj (W (j - 1)) := by
  rw [exists_obj_sup]
  refine sup_le ?_ ?_
  · by_cases h : i + 1 = j
    · refine le_trans (le_of_eq ?_) le_sup_right
      obtain rfl : j - 1 = i := by omega
      rfl
    · have hd : K.d i j = 0 := K.shape i j (by simpa using h)
      exact (exists_le_iff _ _ _).2 (by rw [hd, comp_zero]; exact factors_zero)
  · rw [exists_obj_comp]
    exact (exists_le_iff _ _ _).2 (by rw [K.d_comp_d, comp_zero]; exact factors_zero)

/-- The smallest subcomplex of `K` whose degree `n` part contains `W n` for every `n`. -/
noncomputable def subcomplexClosure : Subobject K :=
  subcomplexOfDegreewise K
    (fun n => W n ⊔ (Subobject.«exists» (K.d (n - 1) n)).obj (W (n - 1)))
    (exists_sup_exists_le K W)

@[simp]
lemma subobjectEval_subcomplexClosure (n : ℤ) :
    subobjectEval K n (subcomplexClosure K W) =
      W n ⊔ (Subobject.«exists» (K.d (n - 1) n)).obj (W (n - 1)) :=
  subobjectEval_subcomplexOfDegreewise K _ (exists_sup_exists_le K W) n

/-- The subcomplex closure of `W` contains `W`. -/
lemma le_subcomplexClosure (n : ℤ) : W n ≤ subobjectEval K n (subcomplexClosure K W) := by
  rw [subobjectEval_subcomplexClosure]
  exact le_sup_left

/-- The subcomplex closure of `W` is the smallest subcomplex containing `W`. -/
lemma subcomplexClosure_le {S : Subobject K} (h : ∀ n, W n ≤ subobjectEval K n S) :
    subcomplexClosure K W ≤ S :=
  (subcomplexOfDegreewise_le_iff K _ (exists_sup_exists_le K W) S).2 (fun n =>
    sup_le (h n) ((exists_obj_mono _ (h (n - 1))).trans (exists_subobjectEval_le S (n - 1) n)))


end Closure

section ExactAt

variable (K : CochainComplex C ℤ) (S : Subobject K) (n : ℤ)

/-- The cycles of a subcomplex `S` in degree `n` are the intersection of `S` in degree `n` with
the ambient cycles. -/
lemma map_kernelSubobject_eq_inf :
    (Subobject.map (S.arrow.f n)).obj
        (kernelSubobject ((S : CochainComplex C ℤ).d n (n + 1))) =
      subobjectEval K n S ⊓ kernelSubobject (K.d n (n + 1)) := by
  rw [map_obj_eq_mk, subobjectEval_eq_mk]
  refine le_antisymm (le_inf (mk_le_mk_of_comm _ rfl) ((mk_le_iff_factors _ _).2 ?_)) ?_
  · refine kernelSubobject_factors _ _ ?_
    rw [Category.assoc, (S.arrow).comm n (n + 1), ← Category.assoc,
      kernelSubobject_arrow_comp, zero_comp]
  · obtain ⟨v, hv⟩ : ∃ v : ((Subobject.mk (S.arrow.f n) ⊓ kernelSubobject (K.d n (n + 1)) :
        Subobject (K.X n)) : C) ⟶ (S : CochainComplex C ℤ).X n, v ≫ S.arrow.f n =
          (Subobject.mk (S.arrow.f n) ⊓ kernelSubobject (K.d n (n + 1))).arrow :=
      ⟨(Subobject.mk (S.arrow.f n)).factorThru _ (inf_arrow_factors_left _ _) ≫
        (underlyingIso (S.arrow.f n)).hom, by
          rw [Category.assoc, underlyingIso_hom_comp_eq_mk, factorThru_arrow]⟩
    have h₂ : (Subobject.mk (S.arrow.f n) ⊓ kernelSubobject (K.d n (n + 1))).arrow ≫
        K.d n (n + 1) = 0 := by
      rw [← factorThru_arrow _ _ (inf_arrow_factors_right (Subobject.mk (S.arrow.f n))
        (kernelSubobject (K.d n (n + 1)))), Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    have h₃ : v ≫ (S : CochainComplex C ℤ).d n (n + 1) = 0 := by
      rw [← cancel_mono (S.arrow.f (n + 1)), Category.assoc, ← (S.arrow).comm n (n + 1),
        ← Category.assoc, hv, h₂, zero_comp]
    exact Subobject.le_mk_of_comm (factorThruKernelSubobject _ v h₃)
      (by rw [← Category.assoc, factorThruKernelSubobject_comp_arrow, hv])

/-- The boundaries of a subcomplex `S` in degree `n` are the image under the ambient differential
of `S` in degree `n - 1`. -/
lemma map_imageSubobject_eq_exists :
    (Subobject.map (S.arrow.f n)).obj
        (imageSubobject ((S : CochainComplex C ℤ).d (n - 1) n)) =
      (Subobject.«exists» (K.d (n - 1) n)).obj (subobjectEval K (n - 1) S) := by
  rw [← exists_iso_map (S.arrow.f n), ← exists_obj_top ((S : CochainComplex C ℤ).d (n - 1) n),
    exists_obj_comp, ← (S.arrow).comm (n - 1) n, ← exists_obj_comp,
    exists_iso_map (S.arrow.f (n - 1)), Subobject.map_top, subobjectEval_eq_mk]

/-- A subcomplex `S` of `K` is exact in degree `n` exactly when the cycles of `S` in degree `n`
are contained in the image under `K.d (n-1) n` of `S` in degree `n - 1`. -/
lemma exactAt_subobject_iff :
    (S : CochainComplex C ℤ).ExactAt n ↔
      subobjectEval K n S ⊓ kernelSubobject (K.d n (n + 1)) ≤
        (Subobject.«exists» (K.d (n - 1) n)).obj (subobjectEval K (n - 1) S) := by
  rw [exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
    ShortComplex.exact_iff_image_eq_kernel]
  simp only [shortComplexFunctor'_obj_f, shortComplexFunctor'_obj_g]
  rw [eq_comm, le_antisymm_iff, and_iff_left
    (image_le_kernel _ _ ((S : CochainComplex C ℤ).d_comp_d _ _ _)),
    ← map_obj_le_map_obj_iff (S.arrow.f n), map_kernelSubobject_eq_inf,
    map_imageSubobject_eq_exists]

/-- The `Acyclic` form of `HomologicalComplex.exactAt_subobject_iff`. -/
lemma acyclic_subobject_iff :
    (S : CochainComplex C ℤ).Acyclic ↔ ∀ n : ℤ,
      subobjectEval K n S ⊓ kernelSubobject (K.d n (n + 1)) ≤
        (Subobject.«exists» (K.d (n - 1) n)).obj (subobjectEval K (n - 1) S) :=
  forall_congr' (fun n => exactAt_subobject_iff K S n)

end ExactAt

end HomologicalComplex
