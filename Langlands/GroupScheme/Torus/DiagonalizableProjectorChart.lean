import Langlands.GroupScheme.Torus.DiagonalizableProjectorWeights
import Langlands.GroupScheme.Torus.OrderedProjectorSubgroup
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Local charts of a diagonalizable representation with positive weight support -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Classical

namespace Langlands.GroupScheme.DiagonalizableProjectorWeights

open OrderedProjectorScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation (Diagonalizable.groupScheme R Λ).toGrp n)

private def supportIdempotent (m : Λ) : R :=
  (exists_entryIdeal_generator (projector ρ m) (by rw [projector_mul, ite_eq_left rfl])).choose

private theorem supportIdempotent_spec (m : Λ) :
    IsIdempotentElem (supportIdempotent ρ m) ∧
      entryIdeal (projector ρ m) = Ideal.span {supportIdempotent ρ m} :=
  (exists_entryIdeal_generator (projector ρ m) (by rw [projector_mul, ite_eq_left rfl])).choose_spec

variable (x : Spec R)

private def indicator (m : Λ) : R :=
  if supportIdempotent ρ m ∈ x.asIdeal then 1 - supportIdempotent ρ m else supportIdempotent ρ m

/-- The product of the idempotents selecting the weight support at `x`. -/
def awayElement : R := ∏ m ∈ support ρ, indicator ρ x m

/-- The selected basic open contains `x`. -/
theorem awayElement_notMem : awayElement ρ x ∉ x.asIdeal := by
  intro h
  let : x.asIdeal.IsPrime := x.isPrime
  obtain ⟨m, hm, hmem⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  unfold indicator at hmem
  split_ifs at hmem with h
  · apply x.isPrime.ne_top
    apply (Ideal.eq_top_iff_one _).mpr
    simpa only [sub_add_cancel] using x.asIdeal.add_mem hmem h
  · exact h hmem

/-- The ring of the basic open on which all weight projector supports are fixed. -/
abbrev chartRing : CommRingCat.{u} := CommRingCat.of (Localization.Away (awayElement ρ x))

/-- The indicated basic open in the affine base of the original representation. -/
abbrev chartOpen : Spec (chartRing ρ x) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (chartRing ρ x)))

instance chartOpen_isOpenImmersion : IsOpenImmersion (chartOpen ρ x) :=
  IsOpenImmersion.of_isLocalization (awayElement ρ x)

/-- The weights that are nonzero at the chosen point. -/
def selectedSupport : Finset Λ := (support ρ).filter fun m => supportIdempotent ρ m ∉ x.asIdeal

/-- Index the selected weights by a finite type in the lowest universe. -/
def labels : Fin (selectedSupport ρ x).card → Λ := fun i => (selectedSupport ρ x).equivFin.symm i

theorem labels_injective : Function.Injective (labels ρ x) :=
  Subtype.val_injective.comp (selectedSupport ρ x).equivFin.symm.injective

private abbrev φ : R →+* chartRing ρ x := algebraMap R (chartRing ρ x)

private theorem indicator_specialized (m : Λ) (hm : m ∈ support ρ) :
    φ ρ x (indicator ρ x m) = 1 := by
  have hunit : IsUnit (φ ρ x (indicator ρ x m)) :=
    isUnit_of_dvd_unit (map_dvd (φ ρ x) (Finset.dvd_prod_of_mem _ hm))
      (IsLocalization.Away.algebraMap_isUnit (awayElement ρ x))
  have hidem : IsIdempotentElem (indicator ρ x m) := by
    unfold indicator
    split_ifs
    · exact (supportIdempotent_spec ρ m).1.one_sub
    · exact (supportIdempotent_spec ρ m).1
  exact (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp (hidem.map (φ ρ x))

private theorem specialization_selected (m : Λ) (hm : m ∈ selectedSupport ρ x) :
    φ ρ x (supportIdempotent ρ m) = 1 := by
  have hm' := Finset.mem_filter.mp hm
  simpa only [indicator, ite_eq_right hm'.2] using indicator_specialized ρ x m hm'.1

/-- The projectors at unselected weights vanish throughout the chosen open. -/
theorem specialized_projector_eq_zero {m : Λ} (hm : m ∈ support ρ) (h : m ∉ selectedSupport ρ x) :
    (φ ρ x).mapMatrix (projector ρ m) = 0 := by
  have hn : supportIdempotent ρ m ∈ x.asIdeal := by
    by_contra hk
    exact h (Finset.mem_filter.mpr ⟨hm, hk⟩)
  have hi := indicator_specialized ρ x m hm
  rw [indicator, ite_eq_left hn, map_sub, map_one, sub_eq_self] at hi
  apply (entryIdeal_eq_bot _).mp
  rw [entryIdeal_map, (supportIdempotent_spec ρ m).2, Ideal.map_span, Set.image_singleton, hi,
    Ideal.span_singleton_zero]

/-- The projector family on the open where the selected supports are all positive. -/
def localFamily : Family (Fin (selectedSupport ρ x).card) n (chartRing ρ x) where
  matrix i := (φ ρ x).mapMatrix (projector ρ (labels ρ x i))
  mul_eq i j := by
    rw [← map_mul (φ ρ x).mapMatrix, projector_mul]
    by_cases h : i = j
    · subst j
      simp only [ite_true]
    · rw [ite_eq_right h, ite_eq_right (fun he => h (labels_injective ρ x he)), map_zero]
  sum_eq := by
    let e := (selectedSupport ρ x).equivFin.symm
    let f (m : Λ) := (φ ρ x).mapMatrix (projector ρ m)
    change (∑ i, f (e i)) = 1
    rw [Equiv.sum_comp e (fun m => f m), Finset.sum_coe_sort (selectedSupport ρ x) f]
    have hs : selectedSupport ρ x ⊆ support ρ := Finset.filter_subset _ _
    rw [Finset.sum_subset (f := f) hs
      (fun m hm hn => specialized_projector_eq_zero ρ x hm hn)]
    change (∑ m ∈ support ρ, (φ ρ x).mapMatrix (projector ρ m)) = 1
    rw [← map_sum (φ ρ x).mapMatrix, sum_projector, map_one]
  entryIdeal_eq_top i := by
    have hi : labels ρ x i ∈ selectedSupport ρ x := ((selectedSupport ρ x).equivFin.symm i).2
    rw [entryIdeal_map, (supportIdempotent_spec ρ (labels ρ x i)).2, Ideal.map_span,
      Set.image_singleton, specialization_selected ρ x _ hi, Ideal.span_singleton_one]

/-- The projectors as global functions on their affine chart. -/
def localGlobalFamily : Family (Fin (selectedSupport ρ x).card) n Γ(Spec (chartRing ρ x), ⊤) :=
  (localFamily ρ x).map (Scheme.ΓSpecIso (chartRing ρ x)).inv.hom

private theorem scalarMap_chartOpen (U : Over (Spec (chartRing ρ x))) (r : R) :
    scalarMap ((Over.map (chartOpen ρ x)).obj U) r =
      U.hom.appTop ((Scheme.ΓSpecIso (chartRing ρ x)).inv (φ ρ x r)) := by
  change ((Scheme.ΓSpecIso R).inv ≫ (U.hom ≫ chartOpen ρ x).appTop).hom r = _
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The local ordered projector family reconstructs the actual pulled-back representation. -/
theorem baseChange_eq_subgroupHom :
    (baseChange (chartOpen ρ x)).map ρ =
      subgroupHom (labels ρ x) (Over.mk (chartOpen ρ x)) (localGlobalFamily ρ x) := by
  refine hom_ext_points fun U t => (targetPoints (Over.mk (chartOpen ρ x)) n U).injective ?_
  rw [targetPoints_subgroupHom]
  change GeneralLinear.pointsEquiv n R ((Over.map (chartOpen ρ x)).obj U)
    (baseChangePointsEquiv (chartOpen ρ x) (GeneralLinear.groupScheme n R) U
      (t ≫ ((baseChange (chartOpen ρ x)).map ρ).hom.hom)) = _
  rw [baseChangePointsEquiv_comp]
  let T := (Over.map (chartOpen ρ x)).obj U
  let z := baseChangePointsEquiv (chartOpen ρ x) (Diagonalizable.groupScheme R Λ).toGrp U t
  let χ : Multiplicative Λ →* Γ(U.left, ⊤)ˣ := Diagonalizable.characterPointsEquiv R Λ T z
  change ρ.pointMatrix T z = weightedUnit ((localGlobalFamily ρ x).map U.hom.appTop.hom)
    (fun i => χ (.ofAdd (labels ρ x i)))
  apply Units.ext
  ext a b
  change ρ.pointMatrix T z a b = weightedMatrix ((localGlobalFamily ρ x).map U.hom.appTop.hom)
    (fun i => (χ (.ofAdd (labels ρ x i)) : Γ(U.left, ⊤))) a b
  rw [pointMatrix_entry, weightedMatrix, Matrix.sum_apply]
  let f (m : Λ) : Γ(U.left, ⊤) :=
    (show Γ(U.left, ⊤) from scalarMap T (projector ρ m a b)) * (χ (.ofAdd m) : Γ(U.left, ⊤))
  change (∑ m ∈ support ρ, f m) = _
  have hs : selectedSupport ρ x ⊆ support ρ := Finset.filter_subset _ _
  rw [← Finset.sum_subset (f := f) hs]
  · have hsum : (∑ i, f (labels ρ x i)) = ∑ m ∈ selectedSupport ρ x, f m :=
      (Equiv.sum_comp (selectedSupport ρ x).equivFin.symm (fun m => f m)).trans
        (Finset.sum_coe_sort (selectedSupport ρ x) f)
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
    change _ * (χ (.ofAdd (labels ρ x i)) : Γ(U.left, ⊤)) =
      (χ (.ofAdd (labels ρ x i)) : Γ(U.left, ⊤)) *
        U.hom.appTop ((Scheme.ΓSpecIso (chartRing ρ x)).inv (φ ρ x (projector ρ (labels ρ x i) a b)))
    rw [scalarMap_chartOpen, mul_comm]
  · intro m hm hn
    dsimp only [f]
    rw [scalarMap_chartOpen]
    have h0 := congrFun (congrFun (specialized_projector_eq_zero ρ x hm hn) a) b
    change φ ρ x (projector ρ m a b) = 0 at h0
    rw [h0, map_zero, map_zero, zero_mul]

end Langlands.GroupScheme.DiagonalizableProjectorWeights
