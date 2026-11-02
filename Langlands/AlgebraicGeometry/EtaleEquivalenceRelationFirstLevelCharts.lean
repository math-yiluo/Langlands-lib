import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationFiniteTypeSystem
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationEtaleObjectDescent
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationChartComparison

/-! # Affine finite type first levels of affine étale charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

namespace AffineFiniteTypeFirstLevel

variable {E : EtaleEquivalenceRelation.{u}} [IsAffine E.U]

/-- An affine étale chart of a relation with a finite type first level has a
finite type first level. The chart need not be invariant. -/
lemma nonempty_chart (M : AffineFiniteTypeFirstLevel E)
    {V : Scheme.{u}} [IsAffine V] (a : V ⟶ E.U) [Etale a] :
    Nonempty (AffineFiniteTypeFirstLevel (E.chart a)) := by
  let h := M.comparison.isCartesian
  let : IsNoetherianRing Γ(M.relation.U, ⊤) := inferInstance
  obtain ⟨i, W, b, k, hW, hb, H⟩ := h.exists_stable_etale_object_model a
  let := hW
  let := hb
  let : LocallyOfFiniteType (terminal.from (h.stableDiagram.obj i).U) :=
    h.stableDiagram_locallyOfFiniteType i
  let F := (h.stableDiagram.obj i).chart b
  have hF : IsAffine F.R := Chart.isAffine_arrows (h.stableDiagram.obj i) b
  have hft : LocallyOfFiniteType (terminal.from W) := by
    rw [show terminal.from W = b ≫ terminal.from (h.stableDiagram.obj i).U from
      terminal.hom_ext _ _]
    infer_instance
  let c : E.chart a ⟶ F :=
    { objMap := k
      relMap := Chart.hom a b k (h.stableCone.π.app i).isCartesian.1
        (h.stableCone.π.app i).isCartesian.2.w H.flip.w
      isCartesian := Chart.isCartesianHom (h.stableCone.π.app i).isCartesian H.flip }
  exact ⟨⟨F, c, hW, hft, hF⟩⟩

/-- A chosen affine finite type first level of an actual affine étale chart. -/
def chart (M : AffineFiniteTypeFirstLevel E)
    {V : Scheme.{u}} [IsAffine V] (a : V ⟶ E.U) [Etale a] :
    AffineFiniteTypeFirstLevel (E.chart a) :=
  (M.nonempty_chart a).some

end AffineFiniteTypeFirstLevel

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]

/-- A selected finite tuple family inherits a first level from the full
family by descent of its actual affine open chart. -/
lemma nonempty_affineFiniteTypeFirstLevel_tupleChart_reindex
    {I J : Type} [Finite I] [Finite J] (length : I → ℕ)
    (k : J → I) (hk : Function.Injective k)
    (M : AffineFiniteTypeFirstLevel (E.tupleChartPresentation length)) :
    Nonempty (AffineFiniteTypeFirstLevel
      (E.tupleChartPresentation (fun j => length (k j)))) := by
  let a := E.tupleChartReindexObjectMap length k
  let : IsOpenImmersion a := E.tupleChartReindexObjectMap_isOpenImmersion length k hk
  obtain ⟨L⟩ := M.nonempty_chart a
  let c : E.tupleChartPresentation (fun j => length (k j)) ⟶
      (E.tupleChartPresentation length).chart a :=
    { objMap := 𝟙 _
      relMap := (E.tupleChartReindexChartIso length k hk).hom
      isCartesian :=
        ⟨by
          simpa only [chart, Category.comp_id, tupleChartReindexChartIso_hom] using
            E.tupleChartReindexChartMap_t length k,
          IsPullback.of_horiz_isIso ⟨by
            simpa only [chart, Category.comp_id, tupleChartReindexChartIso_hom] using
              E.tupleChartReindexChartMap_s length k⟩⟩ }
  exact ⟨AffineFiniteTypeFirstLevel.ofCartesian c L⟩

/-- A first level of the full finite tuple family gives a first level of the
original relation through its actual zero chart. -/
lemma nonempty_affineFiniteTypeFirstLevel_of_tupleFinite (N : ℕ)
    (M : AffineFiniteTypeFirstLevel (E.tupleFinitePresentation N)) :
    Nonempty (AffineFiniteTypeFirstLevel E) := by
  obtain ⟨L⟩ := M.nonempty_chart (E.tupleFiniteZeroObjectMap N)
  let c : E ⟶ (E.tupleFinitePresentation N).chart (E.tupleFiniteZeroObjectMap N) :=
    { objMap := 𝟙 _
      relMap := (E.tupleFiniteZeroChartIso N).hom
      isCartesian :=
        ⟨by
          simpa only [chart, Category.comp_id, tupleFiniteZeroChartIso_hom] using
            E.tupleFiniteZeroChartMap_t N,
          IsPullback.of_horiz_isIso ⟨by
            simpa only [chart, Category.comp_id, tupleFiniteZeroChartIso_hom] using
              E.tupleFiniteZeroChartMap_s N⟩⟩ }
  exact ⟨AffineFiniteTypeFirstLevel.ofCartesian c L⟩

/-- The zero tail contains the original relation as its length-zero chart,
so its first level suffices for the original relation. -/
lemma nonempty_affineFiniteTypeFirstLevel_of_tupleTail_zero (N : ℕ)
    (M : AffineFiniteTypeFirstLevel (E.tupleTailPresentation N 0)) :
    Nonempty (AffineFiniteTypeFirstLevel E) := by
  let k : PUnit.{1} → {i : Fin (N + 1) // 0 ≤ i.val} := fun _ => ⟨0, Nat.zero_le _⟩
  have hk : Function.Injective k := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨L⟩ := E.nonempty_affineFiniteTypeFirstLevel_tupleChart_reindex
    (fun i : {i : Fin (N + 1) // 0 ≤ i.val} => i.val.val) k hk M
  let c : E ⟶ E.tupleChartPresentation (fun _ : PUnit.{1} => 0) :=
    { objMap := E.tupleZeroSingletonObjectIso.hom
      relMap := E.tupleZeroSingletonRelationIso.hom
      isCartesian := ⟨by simp, IsPullback.of_horiz_isIso ⟨by simp⟩⟩ }
  exact ⟨AffineFiniteTypeFirstLevel.ofCartesian c L⟩

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
