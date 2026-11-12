import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelativePointDimension
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubspaceGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.LFTAffineOpen

/-! # Actual open subspaces cut out by smooth relative dimensions -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open TopologicalSpace Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace PointOpenSubspace

/-- The sections whose entire ordinary point image lies in a specified subset. -/
def subfunctor (F : Presheaf S) (O : Set (Points F)) : Subfunctor F where
  obj T := {x | ∀ t : T.unop.left, chartPointMap (uliftYonedaEquiv.symm x) t ∈ O}
  map g x hx t := by
    rw [uliftYonedaEquiv_symm_map, chartPointMap_comp]
    exact hx (g.unop.left t)

/-- Ordinary point images of arbitrary scheme tests into a space are continuous. -/
theorem continuous_chart (Y : AlgebraicSpace S) {T : Over S}
    (a : (schemeYoneda S).obj T ⟶ Y.presheaf) :
    Continuous[_, pointTopology Y.presheaf] (chartPointMap a) := by
  let := pointTopology ((schemeYoneda S).obj T)
  let := pointTopology Y.presheaf
  obtain ⟨V, b, hb, hs⟩ := Y.property.2
  exact (Points.continuous_map_of_atlas a b hb hs).comp (continuous_schemePoint T)

/-- The actual open in a scheme test selected by the point subset. -/
def chartOpen (Y : AlgebraicSpace S) (O : Set (Points Y.presheaf))
    (hO : IsOpen[pointTopology Y.presheaf] O) {T : Over S}
    (a : (schemeYoneda S).obj T ⟶ Y.presheaf) : T.left.Opens := by
  let := pointTopology Y.presheaf
  exact ⟨chartPointMap a ⁻¹' O, hO.preimage (continuous_chart Y a)⟩

def chartScheme (Y : AlgebraicSpace S) (O : Set (Points Y.presheaf))
    (hO : IsOpen[pointTopology Y.presheaf] O) {T : Over S}
    (a : (schemeYoneda S).obj T ⟶ Y.presheaf) : Over S :=
  Over.mk ((chartOpen Y O hO a).ι ≫ T.hom)

def chartInclusion (Y : AlgebraicSpace S) (O : Set (Points Y.presheaf))
    (hO : IsOpen[pointTopology Y.presheaf] O) {T : Over S}
    (a : (schemeYoneda S).obj T ⟶ Y.presheaf) : chartScheme Y O hO a ⟶ T :=
  Over.homMk (chartOpen Y O hO a).ι

instance chartInclusion_isOpenImmersion (Y : AlgebraicSpace S)
    (O : Set (Points Y.presheaf)) (hO : IsOpen[pointTopology Y.presheaf] O)
    {T : Over S} (a : (schemeYoneda S).obj T ⟶ Y.presheaf) :
    _root_.AlgebraicGeometry.IsOpenImmersion (chartInclusion Y O hO a).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (chartOpen Y O hO a).ι)

/-- The scheme open represents exactly the preimage subfunctor in each test. -/
theorem range_chartInclusion (Y : AlgebraicSpace S)
    (O : Set (Points Y.presheaf)) (hO : IsOpen[pointTopology Y.presheaf] O)
    {T : Over S} (a : (schemeYoneda S).obj T ⟶ Y.presheaf) :
    Subfunctor.range ((schemeYoneda S).map (chartInclusion Y O hO a)) =
      (subfunctor Y.presheaf O).preimage a := by
  ext U ⟨g⟩
  have he : uliftYonedaEquiv.symm (a.app U (ULift.up g)) =
      (schemeYoneda S).map g ≫ a := by
    apply uliftYonedaEquiv.injective
    simp only [Equiv.apply_symm_apply, uliftYonedaEquiv_comp,
      uliftYonedaEquiv_uliftYoneda_map]
  have hm : a.app U (ULift.up g) ∈ (subfunctor Y.presheaf O).obj U ↔
      Set.range g.left ⊆ Set.range (chartInclusion Y O hO a).left := by
    change (∀ x : U.unop.left,
      chartPointMap (uliftYonedaEquiv.symm (a.app U (ULift.up g))) x ∈ O) ↔
      Set.range g.left ⊆ Set.range (chartOpen Y O hO a).ι
    rw [he, Scheme.Opens.range_ι]
    simp only [chartPointMap_comp]
    constructor
    · intro h y hy
      obtain ⟨x, hx⟩ := hy
      rw [← hx]
      exact h x
    · intro h x
      exact h ⟨x, rfl⟩
  change (∃ b : ULift (U.unop ⟶ chartScheme Y O hO a),
    ULift.up (b.down ≫ chartInclusion Y O hO a) = ULift.up g) ↔
      a.app U (ULift.up g) ∈ (subfunctor Y.presheaf O).obj U
  rw [hm, ← OpenSubfunctorLifting.factors_through_open_iff
    (chartInclusion Y O hO a) g]
  exact ⟨fun ⟨⟨b⟩, h⟩ => ⟨b, ULift.up_injective h⟩,
    fun ⟨b, h⟩ => ⟨ULift.up b, congrArg ULift.up h⟩⟩

/-- Every open subset of the actual point space defines a representable open. -/
theorem isOpenImmersion_subfunctor (Y : AlgebraicSpace S)
    (O : Set (Points Y.presheaf)) (hO : IsOpen[pointTopology Y.presheaf] O) :
    IsOpenImmersion (subfunctor Y.presheaf O).ι := by
  apply MorphismProperty.relative.of_exists
  intro T a
  let j := chartInclusion Y O hO a
  have hr := range_chartInclusion Y O hO a
  have hle : Subfunctor.range ((schemeYoneda S).map j ≫ a) ≤
      subfunctor Y.presheaf O := by
    rw [Subfunctor.range_comp, Subfunctor.image_le_iff, hr]
  let b := Subfunctor.lift ((schemeYoneda S).map j ≫ a) hle
  let : _root_.AlgebraicGeometry.IsOpenImmersion j.left :=
    chartInclusion_isOpenImmersion Y O hO a
  let : Mono j := Over.mono_of_mono_left j
  refine ⟨chartScheme Y O hO a, b, j, ?_, ?_⟩
  · exact OpenSubfunctorLifting.isPullback_subfunctor_of_range
      (subfunctor Y.presheaf O) b ((schemeYoneda S).map j) a
      (Subfunctor.lift_ι _ hle) hr
  · exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion j.left)

/-- The image on actual quotient points is precisely the selected point subset. -/
theorem range_points (F : Presheaf S) (O : Set (Points F)) :
    Set.range (Points.map (subfunctor F O).ι) = O := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quot.ind with
    | _ q =>
      have h := q.val.property (IsLocalRing.closedPoint q.field)
      have he := chartPointMap_fieldPoint (FieldPoint.map (subfunctor F O).ι q)
      change (Quot.mk _ (FieldPoint.map (subfunctor F O).ι q) : Points F) ∈ O
      exact (congrArg (fun z : Points F => z ∈ O) he).mp h
  · intro hp
    obtain ⟨q, rfl⟩ := Quot.exists_rep p
    have hq : q.val ∈ (subfunctor F O).obj (op (Over.mk q.base)) := by
      intro t
      have ht : t = IsLocalRing.closedPoint q.field :=
        Subsingleton.elim (α := PrimeSpectrum q.field) _ _
      subst t
      exact (chartPointMap_fieldPoint q).symm ▸ hp
    exact ⟨Quot.mk _ (⟨q.field, q.base, ⟨q.val, hq⟩⟩ :
      FieldPoint (subfunctor F O).toFunctor), rfl⟩

/-- Formation of the point-selected subfunctor commutes with preimages. -/
theorem preimage {F G : Presheaf S} (f : F ⟶ G) (O : Set (Points G)) :
    (subfunctor G O).preimage f = subfunctor F (Points.map f ⁻¹' O) := by
  ext T x
  change (∀ t : T.unop.left,
    chartPointMap (uliftYonedaEquiv.symm (f.app T x)) t ∈ O) ↔
      ∀ t : T.unop.left,
        Points.map f (chartPointMap (uliftYonedaEquiv.symm x) t) ∈ O
  rw [← uliftYonedaEquiv_symm_comp]
  simp only [chartPointMap, Function.comp_apply, Points.map_comp]

/-- The algebraic space attached to the point open. -/
def space (Y : AlgebraicSpace S) (O : Set (Points Y.presheaf))
    (hO : IsOpen[pointTopology Y.presheaf] O) : AlgebraicSpace S :=
  OpenSubspaceGeometry.openSubspace Y (subfunctor Y.presheaf O)
    (isOpenImmersion_subfunctor Y O hO)

def inclusion (Y : AlgebraicSpace S) (O : Set (Points Y.presheaf))
    (hO : IsOpen[pointTopology Y.presheaf] O) : space Y O hO ⟶ Y :=
  homMk (subfunctor Y.presheaf O).ι

end PointOpenSubspace

namespace SmoothTargetPointDimensions

variable {X Y : AlgebraicSpace S} {f : X ⟶ Y} (d : SmoothTargetPointDimensions f)

/-- The actual finite index of dimensions which occur on the target. -/
def Index := Set.range d.dimension

instance finiteIndex : Finite d.Index := d.finite_range.to_subtype

def targetSubset (n : ℕ) : Set (Points Y.presheaf) := d.dimension ⁻¹' {n}

theorem targetSubset_isOpen (n : ℕ) :
    IsOpen[pointTopology Y.presheaf] (d.targetSubset n) :=
  d.locallyConstant {n}

theorem targetSubset_isClosed (n : ℕ) :
    IsClosed[pointTopology Y.presheaf] (d.targetSubset n) := by
  let := pointTopology Y.presheaf
  rw [← isOpen_compl_iff]
  exact d.locallyConstant {n}ᶜ

/-- The actual open target subspace of one relative dimension. -/
def targetSpace (n : ℕ) : AlgebraicSpace S :=
  PointOpenSubspace.space Y (d.targetSubset n) (d.targetSubset_isOpen n)

def targetInclusion (n : ℕ) : d.targetSpace n ⟶ Y :=
  PointOpenSubspace.inclusion Y (d.targetSubset n) (d.targetSubset_isOpen n)

theorem targetInclusion_isOpenImmersion (n : ℕ) :
    IsOpenImmersion (hom (d.targetInclusion n)) :=
  PointOpenSubspace.isOpenImmersion_subfunctor Y _ (d.targetSubset_isOpen n)

theorem range_targetInclusion (n : ℕ) :
    Set.range (Points.map (hom (d.targetInclusion n))) = d.targetSubset n :=
  PointOpenSubspace.range_points Y.presheaf _

/-- The finite dimension-indexed family covers all actual target points. -/
theorem target_cover (y : Points Y.presheaf) :
    ∃ n : d.Index, y ∈ Set.range (Points.map (hom (d.targetInclusion n.val))) := by
  refine ⟨⟨d.dimension y, ⟨y, rfl⟩⟩, ?_⟩
  rw [d.range_targetInclusion]
  rfl

theorem target_disjoint {n m : ℕ} (h : n ≠ m) :
    Disjoint (Set.range (Points.map (hom (d.targetInclusion n))))
      (Set.range (Points.map (hom (d.targetInclusion m)))) := by
  rw [d.range_targetInclusion, d.range_targetInclusion]
  apply Set.disjoint_left.mpr
  intro y hn hm
  exact h (hn.symm.trans hm)

end SmoothTargetPointDimensions

end Langlands.AlgebraicGeometry.AlgebraicSpace
