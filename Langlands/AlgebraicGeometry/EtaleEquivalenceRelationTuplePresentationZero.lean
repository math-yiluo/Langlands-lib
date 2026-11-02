import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTuplePresentationReindex

/-! # The original relation as the zero component of the finite tuple family -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R]

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossZeroIso_inv_t :
    E.tupleSymmetricCrossZeroIso.inv ≫ E.tupleSymmetricCrossLeft 0 0 =
      E.t ≫ E.tupleSymmetricZeroIso.inv := by
  apply (cancel_mono E.tupleSymmetricZeroIso.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← E.tupleSymmetricCrossZeroProjection_t, ← Category.assoc]
  exact E.tupleSymmetricCrossZeroIso.inv_hom_id_assoc E.t

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossZeroIso_inv_s :
    E.tupleSymmetricCrossZeroIso.inv ≫ E.tupleSymmetricCrossRight 0 0 =
      E.s ≫ E.tupleSymmetricZeroIso.inv := by
  apply (cancel_mono E.tupleSymmetricZeroIso.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← E.tupleSymmetricCrossZeroProjection_s, ← Category.assoc]
  exact E.tupleSymmetricCrossZeroIso.inv_hom_id_assoc E.s

variable [IsClosedImmersion (prod.lift E.t E.s)]

local instance : Unique (PUnit.{1} × PUnit.{1}) where
  default := (PUnit.unit, PUnit.unit)
  uniq _ := Subsingleton.elim _ _

/-- The original objects, viewed as the coproduct with just the zero chart. -/
def tupleZeroSingletonObjectIso :
    E.U ≅ (E.tupleChartPresentation (fun _ : PUnit.{1} => 0)).U :=
  E.tupleSymmetricZeroIso.symm ≪≫
    (coproductUniqueIso (fun _ : PUnit.{1} => E.tupleSymmetricScheme 0)).symm

/-- The original arrows, viewed as the single zero cross-correspondence. -/
def tupleZeroSingletonRelationIso :
    E.R ≅ (E.tupleChartPresentation (fun _ : PUnit.{1} => 0)).R :=
  E.tupleSymmetricCrossZeroIso.symm ≪≫
    (coproductUniqueIso (fun _ : PUnit.{1} × PUnit.{1} => E.tupleSymmetricCrossScheme 0 0)).symm

@[reassoc (attr := simp)]
theorem tupleZeroSingletonRelationIso_hom_t :
    E.tupleZeroSingletonRelationIso.hom ≫
      (E.tupleChartPresentation (fun _ : PUnit.{1} => 0)).t =
        E.t ≫ E.tupleZeroSingletonObjectIso.hom := by
  change (E.tupleSymmetricCrossZeroIso.inv ≫
    E.tupleChartRelationι (fun _ : PUnit.{1} => 0) PUnit.unit PUnit.unit) ≫ _ =
      E.t ≫ E.tupleSymmetricZeroIso.inv ≫
        E.tupleChartObjectι (fun _ : PUnit.{1} => 0) PUnit.unit
  simp

@[reassoc (attr := simp)]
theorem tupleZeroSingletonRelationIso_hom_s :
    E.tupleZeroSingletonRelationIso.hom ≫
      (E.tupleChartPresentation (fun _ : PUnit.{1} => 0)).s =
        E.s ≫ E.tupleZeroSingletonObjectIso.hom := by
  change (E.tupleSymmetricCrossZeroIso.inv ≫
    E.tupleChartRelationι (fun _ : PUnit.{1} => 0) PUnit.unit PUnit.unit) ≫ _ =
      E.s ≫ E.tupleSymmetricZeroIso.inv ≫
        E.tupleChartObjectι (fun _ : PUnit.{1} => 0) PUnit.unit
  simp

/-- The original object scheme embeds as the zero component of the tuple family. -/
def tupleFiniteZeroObjectMap (N : ℕ) :
    E.U ⟶ (E.tupleFinitePresentation N).U :=
  E.tupleSymmetricZeroIso.inv ≫
    E.tupleChartObjectι (fun i : Fin (N + 1) => i.val) 0

/-- The original arrow scheme embeds as the zero-zero cross-correspondence. -/
def tupleFiniteZeroRelationMap (N : ℕ) :
    E.R ⟶ (E.tupleFinitePresentation N).R :=
  E.tupleSymmetricCrossZeroIso.inv ≫
    E.tupleChartRelationι (fun i : Fin (N + 1) => i.val) 0 0

@[reassoc (attr := simp)]
theorem tupleZeroSingletonObjectIso_reindex (N : ℕ) :
    E.tupleZeroSingletonObjectIso.hom ≫
      E.tupleChartReindexObjectMap (fun i : Fin (N + 1) => i.val)
        (fun _ : PUnit.{1} => (0 : Fin (N + 1))) =
      E.tupleFiniteZeroObjectMap N := by
  change (E.tupleSymmetricZeroIso.inv ≫
    E.tupleChartObjectι (fun _ : PUnit.{1} => 0) PUnit.unit) ≫ _ = _
  rw [Category.assoc]
  exact congrArg (E.tupleSymmetricZeroIso.inv ≫ ·)
    (E.tupleChartObjectι_reindexObjectMap (fun i : Fin (N + 1) => i.val)
      (fun _ : PUnit.{1} => (0 : Fin (N + 1))) PUnit.unit)

@[reassoc (attr := simp)]
theorem tupleZeroSingletonRelationIso_reindex (N : ℕ) :
    E.tupleZeroSingletonRelationIso.hom ≫
      E.tupleChartReindexRelationMap (fun i : Fin (N + 1) => i.val)
        (fun _ : PUnit.{1} => (0 : Fin (N + 1))) =
      E.tupleFiniteZeroRelationMap N := by
  change (E.tupleSymmetricCrossZeroIso.inv ≫
    E.tupleChartRelationι (fun _ : PUnit.{1} => 0) PUnit.unit PUnit.unit) ≫ _ = _
  rw [Category.assoc]
  exact congrArg (E.tupleSymmetricCrossZeroIso.inv ≫ ·)
    (E.tupleChartRelationι_reindexRelationMap (fun i : Fin (N + 1) => i.val)
      (fun _ : PUnit.{1} => (0 : Fin (N + 1))) PUnit.unit PUnit.unit)

instance tupleFiniteZeroObjectMap_isOpenImmersion (N : ℕ) :
    IsOpenImmersion (E.tupleFiniteZeroObjectMap N) := by
  rw [← E.tupleZeroSingletonObjectIso_reindex N]
  refine @IsOpenImmersion.comp _ _ _ _ _ (by infer_instance) ?_
  exact E.tupleChartReindexObjectMap_isOpenImmersion
    (fun i : Fin (N + 1) => i.val) (fun _ : PUnit.{1} => (0 : Fin (N + 1)))
    (fun _ _ _ => Subsingleton.elim _ _)

instance tupleFiniteZeroObjectMap_isClosedImmersion (N : ℕ) :
    IsClosedImmersion (E.tupleFiniteZeroObjectMap N) := by
  rw [← E.tupleZeroSingletonObjectIso_reindex N]
  refine @IsClosedImmersion.comp _ _ _ _ _ (by infer_instance) ?_
  exact E.tupleChartReindexObjectMap_isClosedImmersion
    (fun i : Fin (N + 1) => i.val) (fun _ : PUnit.{1} => (0 : Fin (N + 1)))
    (fun _ _ _ => Subsingleton.elim _ _)

instance tupleFiniteZeroRelationMap_isOpenImmersion (N : ℕ) :
    IsOpenImmersion (E.tupleFiniteZeroRelationMap N) := by
  rw [← E.tupleZeroSingletonRelationIso_reindex N]
  refine @IsOpenImmersion.comp _ _ _ _ _ (by infer_instance) ?_
  exact E.tupleChartReindexRelationMap_isOpenImmersion
    (fun i : Fin (N + 1) => i.val) (fun _ : PUnit.{1} => (0 : Fin (N + 1)))
    (fun _ _ _ => Subsingleton.elim _ _)

instance tupleFiniteZeroRelationMap_isClosedImmersion (N : ℕ) :
    IsClosedImmersion (E.tupleFiniteZeroRelationMap N) := by
  rw [← E.tupleZeroSingletonRelationIso_reindex N]
  refine @IsClosedImmersion.comp _ _ _ _ _ (by infer_instance) ?_
  exact E.tupleChartReindexRelationMap_isClosedImmersion
    (fun i : Fin (N + 1) => i.val) (fun _ : PUnit.{1} => (0 : Fin (N + 1)))
    (fun _ _ _ => Subsingleton.elim _ _)

@[reassoc (attr := simp)]
theorem tupleFiniteZeroRelationMap_t (N : ℕ) :
    E.tupleFiniteZeroRelationMap N ≫ (E.tupleFinitePresentation N).t =
      E.t ≫ E.tupleFiniteZeroObjectMap N := by
  let length := fun i : Fin (N + 1) => i.val
  let i : Fin (N + 1) := 0
  calc
    _ = (E.tupleSymmetricCrossZeroIso.inv ≫ E.tupleChartRelationι length i i) ≫
        (E.tupleChartPresentation length).t := rfl
    _ = E.tupleSymmetricCrossZeroIso.inv ≫
        (E.tupleChartRelationι length i i ≫ (E.tupleChartPresentation length).t) :=
      Category.assoc _ _ _
    _ = E.tupleSymmetricCrossZeroIso.inv ≫
        (E.tupleSymmetricCrossLeft 0 0 ≫ E.tupleChartObjectι length i) :=
      congrArg (E.tupleSymmetricCrossZeroIso.inv ≫ ·) (E.tupleChartRelationι_t length i i)
    _ = (E.tupleSymmetricCrossZeroIso.inv ≫ E.tupleSymmetricCrossLeft 0 0) ≫
        E.tupleChartObjectι length i := (Category.assoc _ _ _).symm
    _ = (E.t ≫ E.tupleSymmetricZeroIso.inv) ≫ E.tupleChartObjectι length i :=
      congrArg (· ≫ E.tupleChartObjectι length i) E.tupleSymmetricCrossZeroIso_inv_t
    _ = E.t ≫ E.tupleFiniteZeroObjectMap N := Category.assoc _ _ _

@[reassoc (attr := simp)]
theorem tupleFiniteZeroRelationMap_s (N : ℕ) :
    E.tupleFiniteZeroRelationMap N ≫ (E.tupleFinitePresentation N).s =
      E.s ≫ E.tupleFiniteZeroObjectMap N := by
  let length := fun i : Fin (N + 1) => i.val
  let i : Fin (N + 1) := 0
  calc
    _ = (E.tupleSymmetricCrossZeroIso.inv ≫ E.tupleChartRelationι length i i) ≫
        (E.tupleChartPresentation length).s := rfl
    _ = E.tupleSymmetricCrossZeroIso.inv ≫
        (E.tupleChartRelationι length i i ≫ (E.tupleChartPresentation length).s) :=
      Category.assoc _ _ _
    _ = E.tupleSymmetricCrossZeroIso.inv ≫
        (E.tupleSymmetricCrossRight 0 0 ≫ E.tupleChartObjectι length i) :=
      congrArg (E.tupleSymmetricCrossZeroIso.inv ≫ ·) (E.tupleChartRelationι_s length i i)
    _ = (E.tupleSymmetricCrossZeroIso.inv ≫ E.tupleSymmetricCrossRight 0 0) ≫
        E.tupleChartObjectι length i := (Category.assoc _ _ _).symm
    _ = (E.s ≫ E.tupleSymmetricZeroIso.inv) ≫ E.tupleChartObjectι length i :=
      congrArg (· ≫ E.tupleChartObjectι length i) E.tupleSymmetricCrossZeroIso_inv_s
    _ = E.s ≫ E.tupleFiniteZeroObjectMap N := Category.assoc _ _ _

/-- Both original endpoints give the full induced chart of the tuple family. -/
theorem tupleFiniteZero_isPullback_pair (N : ℕ) :
    IsPullback (E.tupleFiniteZeroRelationMap N) (prod.lift E.t E.s)
      (prod.lift (E.tupleFinitePresentation N).t (E.tupleFinitePresentation N).s)
      (prod.map (E.tupleFiniteZeroObjectMap N) (E.tupleFiniteZeroObjectMap N)) := by
  have h0 : IsPullback E.tupleZeroSingletonRelationIso.hom (prod.lift E.t E.s)
      (prod.lift (E.tupleChartPresentation (fun _ : PUnit.{1} => 0)).t
        (E.tupleChartPresentation (fun _ : PUnit.{1} => 0)).s)
      (prod.map E.tupleZeroSingletonObjectIso.hom E.tupleZeroSingletonObjectIso.hom) :=
    IsPullback.of_horiz_isIso ⟨by ext <;> simp⟩
  have hk : Function.Injective (fun _ : PUnit.{1} => (0 : Fin (N + 1))) :=
    fun _ _ _ => Subsingleton.elim _ _
  have h := h0.paste_horiz ((E.tupleChartRelation
    (fun i : Fin (N + 1) => i.val)).reindex_isPullback_pair
      (fun _ : PUnit.{1} => (0 : Fin (N + 1))) hk)
  change IsPullback (E.tupleZeroSingletonRelationIso.hom ≫
      E.tupleChartReindexRelationMap (fun i : Fin (N + 1) => i.val)
        (fun _ : PUnit.{1} => (0 : Fin (N + 1))))
    (prod.lift E.t E.s)
    (prod.lift (E.tupleFinitePresentation N).t (E.tupleFinitePresentation N).s)
    (prod.map E.tupleZeroSingletonObjectIso.hom E.tupleZeroSingletonObjectIso.hom ≫
      prod.map (E.tupleChartReindexObjectMap (fun i : Fin (N + 1) => i.val)
        (fun _ : PUnit.{1} => (0 : Fin (N + 1))))
        (E.tupleChartReindexObjectMap (fun i : Fin (N + 1) => i.val)
          (fun _ : PUnit.{1} => (0 : Fin (N + 1))))) at h
  simpa only [prod.map_map, E.tupleZeroSingletonObjectIso_reindex,
    E.tupleZeroSingletonRelationIso_reindex] using h

/-- Map each original arrow to the actual relation on the zero chart. -/
def tupleFiniteZeroChartMap (N : ℕ) :
    E.R ⟶ Chart.arrows (E.tupleFinitePresentation N) (E.tupleFiniteZeroObjectMap N) :=
  Chart.lift (E.tupleFinitePresentation N) (E.tupleFiniteZeroObjectMap N)
    E.t E.s (E.tupleFiniteZeroRelationMap N)
    (E.tupleFiniteZeroRelationMap_t N) (E.tupleFiniteZeroRelationMap_s N)

@[reassoc (attr := simp)]
theorem tupleFiniteZeroChartMap_t (N : ℕ) :
    E.tupleFiniteZeroChartMap N ≫
      Chart.t (E.tupleFinitePresentation N) (E.tupleFiniteZeroObjectMap N) = E.t := by
  exact Chart.lift_t _ _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem tupleFiniteZeroChartMap_s (N : ℕ) :
    E.tupleFiniteZeroChartMap N ≫
      Chart.s (E.tupleFinitePresentation N) (E.tupleFiniteZeroObjectMap N) = E.s := by
  exact Chart.lift_s _ _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem tupleFiniteZeroChartMap_map (N : ℕ) :
    E.tupleFiniteZeroChartMap N ≫
      Chart.map (E.tupleFinitePresentation N) (E.tupleFiniteZeroObjectMap N) =
        E.tupleFiniteZeroRelationMap N := by
  exact Chart.lift_map _ _ _ _ _ _ _

/-- The original relation scheme is the actual induced zero-chart relation. -/
def tupleFiniteZeroChartIso (N : ℕ) :
    E.R ≅ Chart.arrows (E.tupleFinitePresentation N) (E.tupleFiniteZeroObjectMap N) :=
  (E.tupleFiniteZero_isPullback_pair N).isoIsPullback _ _
    (Chart.isPullback_pair (E.tupleFinitePresentation N) (E.tupleFiniteZeroObjectMap N))

@[simp]
theorem tupleFiniteZeroChartIso_hom (N : ℕ) :
    (E.tupleFiniteZeroChartIso N).hom = E.tupleFiniteZeroChartMap N := by
  have h := (E.tupleFiniteZero_isPullback_pair N).isoIsPullback_hom_snd _ _
    (Chart.isPullback_pair (E.tupleFinitePresentation N) (E.tupleFiniteZeroObjectMap N))
  apply Chart.hom_ext
  · simpa [tupleFiniteZeroChartIso] using congrArg (· ≫ prod.fst) h
  · simpa [tupleFiniteZeroChartIso] using congrArg (· ≫ prod.snd) h

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
