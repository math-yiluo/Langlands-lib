import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasPointTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.PointTopologyIso

/-! # Ordinary points after composition of bases -/

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition

open OriginalBaseTransport

variable {S T : Scheme.{u}} (g : S ⟶ T)

/-- A field point retains its field, original section and composed structure map. -/
def fieldPoint {F : Presheaf S} (p : FieldPoint F) : FieldPoint (presheaf g F) :=
  ⟨p.field, p.base ≫ g, liftSection g F (Over.mk p.base) p.val⟩

/-- A composed field point contains its original structure map and original section. -/
def originalFieldPoint {F : Presheaf S} (p : FieldPoint (presheaf g F)) : FieldPoint F :=
  ⟨p.field, p.val.val.1, p.val.val.2⟩

@[simp]
theorem originalFieldPoint_fieldPoint {F : Presheaf S} (p : FieldPoint F) :
    originalFieldPoint g (fieldPoint g p) = p := rfl

@[simp]
theorem fieldPoint_originalFieldPoint {F : Presheaf S} (p : FieldPoint (presheaf g F)) :
    fieldPoint g (originalFieldPoint g p) = p := by
  rcases p with ⟨K, t, ⟨⟨s, x⟩, hs⟩⟩
  change Spec (CommRingCat.of K) ⟶ S at s
  have hst : s ≫ g = t := congrArg ULift.down hs
  subst t
  rfl

/-- Common-field equivalence of original sections survives composition of bases. -/
theorem fieldPoint_rel {F : Presheaf S} {p q : FieldPoint F} (hpq : FieldPoint.Rel F p q) :
    FieldPoint.Rel (presheaf g F) (fieldPoint g p) (fieldPoint g q) := by
  obtain ⟨Ω, hΩ, i, j, hb, he⟩ := hpq
  let : Field Ω := hΩ
  refine ⟨Ω, inferInstance, i, j, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom j) ≫ (q.base ≫ g) =
      Spec.map (CommRingCat.ofHom i) ≫ (p.base ≫ g)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ g) hb).trans (Category.assoc _ _ _))
  · apply Subtype.ext
    have hp := congrArg Subtype.val ((totalFiberIso F).hom.naturality_apply
      (p.extendMap i).op p.val)
    have hq := congrArg Subtype.val ((totalFiberIso F).hom.naturality_apply
      (Over.homMk (Spec.map (CommRingCat.ofHom j)) hb : p.extendTest i ⟶ Over.mk q.base).op q.val)
    have hh := congrArg (fun v => ((totalFiberIso F).hom.app (op (p.extendTest i)) v).val) he
    exact hp.symm.trans (hh.trans hq)

/-- Common-field equivalence of composed sections identifies the original structure maps. -/
theorem originalFieldPoint_rel {F : Presheaf S} {p q : FieldPoint (presheaf g F)}
    (hpq : FieldPoint.Rel (presheaf g F) p q) :
    FieldPoint.Rel F (originalFieldPoint g p) (originalFieldPoint g q) := by
  obtain ⟨Ω, hΩ, i, j, hb, he⟩ := hpq
  let : Field Ω := hΩ
  have hh : (totalPresheaf F).map (Spec.map (CommRingCat.ofHom i)).op p.val.val =
      (totalPresheaf F).map (Spec.map (CommRingCat.ofHom j)).op q.val.val :=
    congrArg Subtype.val he
  have hb' : Spec.map (CommRingCat.ofHom j) ≫ (originalFieldPoint g q).base =
      Spec.map (CommRingCat.ofHom i) ≫ (originalFieldPoint g p).base :=
    (congrArg Sigma.fst hh).symm
  refine ⟨Ω, inferInstance, i, j, hb', ?_⟩
  apply (toTotalFiber_bijective F ((originalFieldPoint g p).extendTest i)).injective
  apply Subtype.ext
  have hp := congrArg Subtype.val ((totalFiberIso F).hom.naturality_apply
    ((originalFieldPoint g p).extendMap i).op (originalFieldPoint g p).val)
  have hq := congrArg Subtype.val ((totalFiberIso F).hom.naturality_apply
    (Over.homMk (Spec.map (CommRingCat.ofHom j)) hb' :
      (originalFieldPoint g p).extendTest i ⟶ Over.mk (originalFieldPoint g q).base).op
      (originalFieldPoint g q).val)
  exact hp.trans (hh.trans hq.symm)

/-- Ordinary point sets are unchanged by composition of bases. -/
def pointsEquiv (F : Presheaf S) : Points F ≃ Points (presheaf g F) where
  toFun := Quot.map (fieldPoint g) (fun _ _ h => fieldPoint_rel g h)
  invFun := Quot.map (originalFieldPoint g) (fun _ _ h => originalFieldPoint_rel g h)
  left_inv x := by
    induction x using Quot.ind
    rfl
  right_inv x := by
    induction x using Quot.ind with
    | _ p => exact congrArg (Quot.mk _) (fieldPoint_originalFieldPoint g p)

/-- The ordinary-point identification is natural in the original presheaf. -/
theorem pointsEquiv_naturality {F G : Presheaf S} (f : F ⟶ G) (p : Points F) :
    pointsEquiv g G (Points.map f p) = Points.map (map g f) (pointsEquiv g F p) := by
  induction p using Quot.ind
  rfl

/-- Point-surjectivity of a morphism of spaces survives composition of bases. -/
theorem surjective_spaceMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsSurjectiveMorphism f) : IsSurjectiveMorphism (spaceMap g f) := by
  intro y
  obtain ⟨x, hx⟩ := hf ((pointsEquiv g Y.presheaf).symm y)
  refine ⟨pointsEquiv g X.presheaf x, ?_⟩
  exact (pointsEquiv_naturality g (hom f) x).symm.trans
    ((congrArg (pointsEquiv g Y.presheaf) hx).trans
      ((pointsEquiv g Y.presheaf).apply_symm_apply y))

/-- The represented-scheme comparison fixes its underlying ordinary scheme points. -/
theorem schemeComparison_points (U : Over S) (u : U.left) :
    Points.map (schemeComparison g U)
      (pointsEquiv g ((schemeYoneda S).obj U) (schemePoint U u)) =
        schemePoint ((Over.map g).obj U) u := by
  apply (schemePointsEquiv ((Over.map g).obj U)).injective
  change schemePointsTo ((Over.map g).obj U)
      (Points.map (schemeComparison g U)
        (pointsEquiv g ((schemeYoneda S).obj U) (schemePoint U u))) =
    schemePointsTo ((Over.map g).obj U) (schemePoint ((Over.map g).obj U) u)
  rw [schemePointsTo_schemePoint]
  exact Scheme.fromSpecResidueField_apply _ _

/-- The inverse represented-scheme comparison agrees with the ordinary-point identification. -/
theorem schemeIso_points (U : Over S) (u : U.left) :
    pointsEquiv g ((schemeYoneda S).obj U) (schemePoint U u) =
      Points.map (schemeIso g U).hom (schemePoint ((Over.map g).obj U) u) := by
  apply (Points.isoEquiv (schemeIso g U)).symm.injective
  exact (schemeComparison_points g U u).trans
    ((Points.isoEquiv (schemeIso g U)).symm_apply_apply
      (schemePoint ((Over.map g).obj U) u)).symm

/-- Actual atlas point maps agree under the ordinary-point identification. -/
theorem pointsEquiv_chartPointMap {F : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (u : U.left) :
    pointsEquiv g F (chartPointMap a u) = chartPointMap (fromScheme g a) u := by
  exact (pointsEquiv_naturality g a (schemePoint U u)).trans
    ((congrArg (Points.map (map g a)) (schemeIso_points g U u)).trans
      (Points.map_comp (schemeIso g U).hom (map g a)
        (schemePoint ((Over.map g).obj U) u)).symm)

/-- A supplied etale surjective atlas gives the topology comparison on all ordinary points. -/
def pointsHomeomorphOfAtlas {F : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a) (hs : IsSurjective a) :
    letI := pointTopology F
    letI := pointTopology (presheaf g F)
    Points F ≃ₜ Points (presheaf g F) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  letI := pointTopology F
  letI := pointTopology (presheaf g F)
  have ha' : IsEtale (fromScheme g a) := relative_fromScheme g _ ha
  have hs' : IsSurjective (fromScheme g a) := relative_fromScheme g _ hs
  refine { toEquiv := pointsEquiv g F, continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (isQuotientMap_chartPointMap a ha hs).continuous_iff.mpr
    exact (continuous_schemePoint_chart (fromScheme g a) ha').congr
      (fun u => (pointsEquiv_chartPointMap g a u).symm)
  · apply (isQuotientMap_chartPointMap (fromScheme g a) ha' hs').continuous_iff.mpr
    have he : (pointsEquiv g F).symm ∘ chartPointMap (fromScheme g a) = chartPointMap a := by
      funext u
      exact (congrArg (pointsEquiv g F).symm (pointsEquiv_chartPointMap g a u)).symm.trans
        ((pointsEquiv g F).symm_apply_apply (chartPointMap a u))
    exact (continuous_schemePoint_chart a ha).congr (fun u => (congrFun he u).symm)

/-- Composition of bases does not change the ordinary topological space of an algebraic space. -/
def pointsHomeomorph (X : AlgebraicSpace S) :
    letI := pointTopology X.presheaf
    letI := pointTopology (space g X).presheaf
    Points X.presheaf ≃ₜ Points (space g X).presheaf := by
  letI := pointTopology X.presheaf
  letI := pointTopology (space g X).presheaf
  letI := pointTopology (presheaf g X.presheaf)
  refine { toEquiv := pointsEquiv g X.presheaf, continuous_toFun := ?_, continuous_invFun := ?_ }
  · obtain ⟨U, a, ha, hs⟩ := X.property.2
    exact (pointsHomeomorphOfAtlas g a ha hs).continuous_toFun
  · obtain ⟨U, a, ha, hs⟩ := X.property.2
    exact (pointsHomeomorphOfAtlas g a ha hs).continuous_invFun

end Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition
