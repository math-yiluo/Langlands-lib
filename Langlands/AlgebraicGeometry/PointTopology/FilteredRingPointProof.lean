import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointStatement

/-!
# Filtered-colimit comparison for actual relative scheme points
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F) (hc : IsColimit c)
variable (X : Over (Spec (CommRingCat.of R)))

include hc in
private theorem pointColimit_injective [LocallyOfFiniteType X.hom] :
    Function.Injective (ringPointColimitMap R F X c) := by
  let D := F.op ⋙ algSpec (CommRingCat.of R)
  let D₀ := D ⋙ Over.forget (Spec (CommRingCat.of R))
  let t : D₀ ⟶ (Functor.const Jᵒᵖ).obj (Spec (CommRingCat.of R)) :=
    NatTrans.mk (fun i => (D.obj i).hom) (by
      intro i j f
      change (D.map f).left ≫ (D.obj j).hom = (D.obj i).hom ≫ 𝟙 _
      rw [Category.comp_id]
      exact Over.w (D.map f))
  have (i : Jᵒᵖ) : CompactSpace (D₀.obj i) := by
    change CompactSpace (Spec (CommRingCat.of (F.obj i.unop)))
    infer_instance
  have {i j : Jᵒᵖ} (f : i ⟶ j) : IsAffineHom (D₀.map f) := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom (F.map f.unop).hom.toRingHom))
    infer_instance
  apply (Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered'
    ((F ⋙ ringPointFunctor R X).coconeTypesEquiv.symm (ringPointCocone R F X c))).mpr
  intro i p q hpq
  obtain ⟨k, f, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    D₀ t X.hom ((Over.forget _).mapCone (ringTestCone R F c))
    (isLimitOfPreserves (Over.forget _) (ringTestConeIsLimit R F c hc))
    p.left q.left (Over.w p).symm (Over.w q).symm congr($(hpq).left)
  refine ⟨k.unop, f.unop, ?_⟩
  apply Over.OverMorphism.ext
  exact heq

include hc in
private theorem exists_point_stage [LocallyOfFinitePresentation X.hom]
    (p : RingPoint R X c.pt) :
    ∃ (i : J) (q : RingPoint R X (F.obj i)), q.changeRing (c.ι.app i).hom = p := by
  let D := F.op ⋙ algSpec (CommRingCat.of R)
  let D₀ := D ⋙ Over.forget (Spec (CommRingCat.of R))
  let t : D₀ ⟶ (Functor.const Jᵒᵖ).obj (Spec (CommRingCat.of R)) :=
    NatTrans.mk (fun i => (D.obj i).hom) (by
      intro i j f
      change (D.map f).left ≫ (D.obj j).hom = (D.obj i).hom ≫ 𝟙 _
      rw [Category.comp_id]
      exact Over.w (D.map f))
  have (i : Jᵒᵖ) : CompactSpace (D₀.obj i) := by
    change CompactSpace (Spec (CommRingCat.of (F.obj i.unop)))
    infer_instance
  have (i : Jᵒᵖ) : QuasiSeparatedSpace (D₀.obj i) := by
    change QuasiSeparatedSpace (Spec (CommRingCat.of (F.obj i.unop)))
    infer_instance
  have {i j : Jᵒᵖ} (f : i ⟶ j) : IsAffineHom (D₀.map f) := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom (F.map f.unop).hom.toRingHom))
    infer_instance
  obtain ⟨i, g, hg, hg'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    D₀ t X.hom ((Over.forget _).mapCone (ringTestCone R F c))
    (isLimitOfPreserves (Over.forget _) (ringTestConeIsLimit R F c hc))
    p.left (by
      ext i
      exact (Over.w ((ringTestCone R F c).π.app i)).trans (Over.w p).symm)
  exact ⟨i.unop, Over.homMk g hg', by apply Over.OverMorphism.ext; exact hg⟩

/-- The exact fixed-model filtered-point comparison, including both equality
criteria and the locally finitely presented factorization. -/
theorem filteredRingPointComparison : FilteredRingPointComparison.{u} := by
  intro R _ J _ _ F c hc X
  constructor
  · intro h
    let := h
    have hinj := pointColimit_injective R F c hc X
    refine ⟨hinj, ?_, ?_⟩
    · intro i j p q
      change (ringPointColimitMap R F X c (ringPointColimitι R F X i p) =
        ringPointColimitMap R F X c (ringPointColimitι R F X j q)) ↔ _
      rw [hinj.eq_iff]
      exact (F ⋙ ringPointFunctor R X).ιColimitType_eq_iff_of_isFiltered p q
    · intro i p q
      change (ringPointColimitMap R F X c (ringPointColimitι R F X i p) =
        ringPointColimitMap R F X c (ringPointColimitι R F X i q)) ↔ _
      rw [hinj.eq_iff]
      exact (F ⋙ ringPointFunctor R X).ιColimitType_eq_iff_of_isFiltered' p q
  · intro h
    let := h
    have hstage := exists_point_stage R F c hc X
    have hsurj : Function.Surjective (ringPointColimitMap R F X c) := by
      intro p
      obtain ⟨i, q, hq⟩ := hstage p
      exact ⟨ringPointColimitι R F X i q, hq⟩
    exact ⟨hstage, hsurj, pointColimit_injective R F c hc X, hsurj⟩

end Langlands.AlgebraicGeometry.PointTopology
