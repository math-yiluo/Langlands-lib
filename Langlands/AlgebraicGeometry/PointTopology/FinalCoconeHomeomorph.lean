import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointTopology
import Mathlib.CategoryTheory.Limits.Final

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.AlgebraicGeometry.PointTopology

variable {I J : Type u} [SmallCategory I] [SmallCategory J]
  (F : I ⥤ Type u) (G : J ⥤ Type u) (H : I ⥤ J) [H.Final]
  (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
  (e : F ≅ H ⋙ G)

/-- The comparison of actual colimit points induced by a final family of stage equivalences. -/
def finalCoconeIso : c.pt ≅ d.pt :=
  hc.coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv e (d.whisker H)).symm
      ((Functor.Final.isColimitWhiskerEquiv H d).symm hd))

/-- On every original stage the colimit comparison is the supplied stage equivalence. -/
@[simp]
theorem finalCoconeIso_ι (i : I) (x : F.obj i) :
    (finalCoconeIso F G H c d hc hd e).hom (c.ι.app i x) =
      d.ι.app (H.obj i) (e.hom.app i x) := by
  exact ConcreteCategory.congr_hom
    (IsColimit.comp_coconePointUniqueUpToIso_hom hc
      ((IsColimit.precomposeHomEquiv e (d.whisker H)).symm
        ((Functor.Final.isColimitWhiskerEquiv H d).symm hd)) i) x

/-- The inverse comparison restricts to the inverse stage equivalence. -/
@[simp]
theorem finalCoconeIso_inv_ι (i : I) (x : G.obj (H.obj i)) :
    (finalCoconeIso F G H c d hc hd e).inv (d.ι.app (H.obj i) x) =
      c.ι.app i (e.inv.app i x) := by
  apply (finalCoconeIso F G H c d hc hd e).toEquiv.injective
  change (finalCoconeIso F G H c d hc hd e).hom
    ((finalCoconeIso F G H c d hc hd e).inv _) =
      (finalCoconeIso F G H c d hc hd e).hom (c.ι.app i (e.inv.app i x))
  rw [Iso.inv_hom_id_apply, finalCoconeIso_ι]
  congr 1
  exact (ConcreteCategory.congr_hom (e.inv_hom_id_app i) x).symm

variable (τ : ∀ i, TopologicalSpace (F.obj i))
  (σ : ∀ j, TopologicalSpace (G.obj j))

/-- The independently specified final topology from the original stage maps. -/
@[instance_reducible]
def typeCoconeTopology : TopologicalSpace c.pt :=
  ⨆ i, @TopologicalSpace.coinduced _ _ (c.ι.app i) (τ i)

/-- A map out of a final stage topology is continuous exactly on all original stages. -/
theorem typeCoconeTopology_continuous_iff {Z : Type v} [TopologicalSpace Z]
    (f : c.pt → Z) :
    Continuous[typeCoconeTopology F c τ, inferInstance] f ↔
      ∀ i, Continuous[τ i, inferInstance] (f ∘ c.ι.app i) := by
  unfold typeCoconeTopology
  rw [continuous_iSup_dom]
  exact forall_congr' fun _ => continuous_coinduced_dom

/-- Every original stage map into its final topology is continuous. -/
theorem typeCoconeTopology_continuous_ι (i : I) :
    Continuous[τ i, typeCoconeTopology F c τ] (c.ι.app i) :=
  continuous_iSup_rng (i := i) continuous_coinduced_rng

variable (hσ : ∀ {j j'} (f : j ⟶ j'), Continuous[σ j, σ j'] (G.map f))

include hσ in
/-- Continuity out of the upper colimit is detected on any final family of its original stages. -/
theorem typeCoconeTopology_continuous_iff_final {Z : Type v} [TopologicalSpace Z]
    (f : d.pt → Z) :
    Continuous[typeCoconeTopology G d σ, inferInstance] f ↔
      ∀ i, Continuous[σ (H.obj i), inferInstance] (f ∘ d.ι.app (H.obj i)) := by
  rw [typeCoconeTopology_continuous_iff]
  constructor
  · intro h i
    exact h _
  · intro h j
    let a : StructuredArrow j H := Classical.choice inferInstance
    have hh := (h a.right).comp (hσ a.hom)
    convert hh using 1
    funext x
    exact congrArg f (ConcreteCategory.congr_hom (d.w a.hom) x).symm

variable (he : ∀ i, @IsHomeomorph _ _ (τ i) (σ (H.obj i)) (e.hom.app i))

/-- A final natural family of stage homeomorphisms gives a homeomorphism
between the two independently defined final topologies on actual colimit points. -/
def finalCoconeHomeomorph :
    @Homeomorph c.pt d.pt (typeCoconeTopology F c τ) (typeCoconeTopology G d σ) := by
  letI := typeCoconeTopology F c τ
  letI := typeCoconeTopology G d σ
  let E := (finalCoconeIso F G H c d hc hd e).toEquiv
  refine { E with continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (typeCoconeTopology_continuous_iff F c τ E).mpr
    intro i
    have hh := (typeCoconeTopology_continuous_ι G d σ (H.obj i)).comp (he i).continuous
    convert hh using 1
    funext x
    exact finalCoconeIso_ι F G H c d hc hd e i x
  · apply (typeCoconeTopology_continuous_iff_final G H d σ hσ E.symm).mpr
    intro i
    have hi : Continuous[σ (H.obj i), τ i] (e.inv.app i) := by
      let : TopologicalSpace (F.obj i) := τ i
      let : TopologicalSpace ((H ⋙ G).obj i) := σ (H.obj i)
      exact (e.app i).toEquiv.continuous_symm_iff.mpr (he i).isOpenMap
    have hh := (typeCoconeTopology_continuous_ι F c τ i).comp hi
    convert hh using 1
    funext x
    exact finalCoconeIso_inv_ι F G H c d hc hd e i x

/-- The assembled homeomorphism is the original stage homeomorphism on every stage. -/
@[simp]
theorem finalCoconeHomeomorph_ι (i : I) (x : F.obj i) :
    finalCoconeHomeomorph F G H c d hc hd e τ σ hσ he (c.ι.app i x) =
      d.ι.app (H.obj i) (e.hom.app i x) :=
  finalCoconeIso_ι F G H c d hc hd e i x

end Langlands.AlgebraicGeometry.PointTopology
