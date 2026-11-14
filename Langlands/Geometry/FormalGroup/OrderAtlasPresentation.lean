import Langlands.Geometry.FormalGroup.AtlasOrderComparisonEquivalence
import Langlands.Geometry.FormalGroup.AtlasPresentation

/-! # Classes of actual finite-dimensional formal atlases with an order action -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

namespace BasicAtlas.OrderAction.Comparison

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {X : BasicAtlas O R σ}

/-- An actual refinement compares with its original through direct/successive restriction. -/
def ofRefinement (E : OrderAction D X) (q : CoverRefinement X) :
    Comparison E (q.orderAction E) where
  left := q.comp (CoverRefinement.refl q.atlas)
  right := CoverRefinement.refl q.atlas
  sameCover := rfl
  coordinateIso := q.orderCompIso E (CoverRefinement.refl q.atlas)

/-- The formal comparison with a refinement realizes the original full-family restriction. -/
theorem onPoints_ofRefinement (E : OrderAction D X) (q : CoverRefinement X)
    (A : CommAlgCat.{v} R) (x : E.Point A) :
    (ofRefinement E q).onPoints A x = q.orderPointEquiv E A x := by
  apply ((CoverRefinement.refl q.atlas).orderPointEquiv (q.orderAction E) A).injective
  exact ((ofRefinement E q).onPoints_restrict A x).trans
    (q.orderComp_onPoints E (CoverRefinement.refl q.atlas) A x)

end BasicAtlas.OrderAction.Comparison

/-- An actual finite-dimensional formal atlas with an action of the full O-algebra D. -/
structure OrderAtlasPresentation (O : Type u) [CommRing O] (D : Type w) [Ring D]
    [Algebra O D] (R : Type v) [CommRing R] [Algebra O R]
    extends AtlasPresentation O R where
  order : BasicAtlas.OrderAction D atlas

namespace OrderAtlasPresentation

variable {O : Type u} [CommRing O]
variable {D : Type w} [Ring D] [Algebra O D]
variable {R : Type v} [CommRing R] [Algebra O R]

/-- Equivalence means existence of an actual refined formal comparison commuting with D. -/
def Equivalent (X Y : OrderAtlasPresentation O D R) : Prop :=
  Nonempty (BasicAtlas.OrderAction.Comparison X.order Y.order)

theorem equivalent_refl (X : OrderAtlasPresentation O D R) : Equivalent X X :=
  ⟨BasicAtlas.OrderAction.Comparison.refl X.order⟩

theorem equivalent_symm {X Y : OrderAtlasPresentation O D R} (h : Equivalent X Y) :
    Equivalent Y X :=
  h.map BasicAtlas.OrderAction.Comparison.symm

theorem equivalent_trans {X Y Z : OrderAtlasPresentation O D R}
    (h : Equivalent X Y) (k : Equivalent Y Z) : Equivalent X Z := by
  obtain ⟨f⟩ := h
  obtain ⟨g⟩ := k
  exact ⟨f.trans g⟩

/-- The constructed formal comparison operations establish the setoid laws. -/
def comparisonSetoid : Setoid (OrderAtlasPresentation O D R) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- Classes of actual order-linear presentations modulo formal comparison after refinement. -/
def IsoClass (O : Type u) [CommRing O] (D : Type w) [Ring D] [Algebra O D]
    (R : Type v) [CommRing R] [Algebra O R] :=
  Quotient (comparisonSetoid (O := O) (D := D) (R := R))

/-- Send a supplied actual presentation to its class. -/
def classOf (X : OrderAtlasPresentation O D R) : IsoClass O D R :=
  Quotient.mk _ X

/-- Class equality is precisely existence of an actual refined order-linear formal comparison. -/
theorem classOf_eq_iff (X Y : OrderAtlasPresentation O D R) :
    classOf X = classOf Y ↔ Equivalent X Y :=
  Quotient.eq

/-- A specified formal order-linear comparison identifies the presentation classes. -/
theorem classOf_eq_of_comparison {X Y : OrderAtlasPresentation O D R}
    (f : BasicAtlas.OrderAction.Comparison X.order Y.order) : classOf X = classOf Y :=
  (classOf_eq_iff X Y).mpr ⟨f⟩

/-- Forgetting D-commutation retains an actual refined O-linear formal comparison. -/
theorem equivalent_forgetOrder {X Y : OrderAtlasPresentation O D R} (h : Equivalent X Y) :
    AtlasPresentation.Equivalent X.toAtlasPresentation Y.toAtlasPresentation :=
  h.map BasicAtlas.OrderAction.Comparison.toBasicComparison

/-- Restrict both actual charts and their full order action to a finer principal cover. -/
def refine (X : OrderAtlasPresentation O D R) (q : BasicAtlas.CoverRefinement X.atlas) :
    OrderAtlasPresentation O D R where
  dimension := X.dimension
  atlas := q.atlas
  order := q.orderAction X.order

/-- An actual refinement has the same order-linear presentation class. -/
theorem classOf_refine (X : OrderAtlasPresentation O D R)
    (q : BasicAtlas.CoverRefinement X.atlas) : classOf (X.refine q) = classOf X :=
  (classOf_eq_of_comparison (BasicAtlas.OrderAction.Comparison.ofRefinement X.order q)).symm

namespace IsoClass

/-- Forget the order action on classes, using the same actual underlying formal comparisons. -/
def forgetOrder : IsoClass O D R → AtlasPresentation.IsoClass O R :=
  Quotient.map OrderAtlasPresentation.toAtlasPresentation
    (fun _ _ h => equivalent_forgetOrder h)

@[simp]
theorem forgetOrder_classOf (X : OrderAtlasPresentation O D R) :
    forgetOrder (classOf X) = AtlasPresentation.classOf X.toAtlasPresentation := rfl

/-- Choose an actual order-linear presentation of the class. -/
def representative (q : IsoClass O D R) : OrderAtlasPresentation O D R :=
  Quotient.out q

@[simp]
theorem classOf_representative (q : IsoClass O D R) : classOf q.representative = q :=
  Quotient.out_eq q

/-- Evaluate the chosen representative's actual D-module point functor. -/
def pointFunctor (q : IsoClass O D R) :
    CommAlgCat.{v} R ⥤ ModuleCat.{v + 1} D :=
  q.representative.order.pointFunctor

/-- Restrict the same chosen representative's point functor to actual Nilp algebras. -/
def nilpPointFunctor (q : IsoClass O D R) (π : R) :
    Nilp R π ⥤ ModuleCat.{v + 1} D :=
  q.representative.order.nilpPointFunctor π

end IsoClass

/-- Choose an actual order-linear formal comparison with the chosen class representative. -/
def comparisonToRepresentative (X : OrderAtlasPresentation O D R) :
    BasicAtlas.OrderAction.Comparison X.order (classOf X).representative.order :=
  Classical.choice ((classOf_eq_iff X (classOf X).representative).mp
    (IsoClass.classOf_representative (classOf X)).symm)

/-- The specified choice of actual comparison yields a natural D-module isomorphism. -/
def pointFunctorIsoToRepresentative (X : OrderAtlasPresentation O D R) :
    X.order.pointFunctor ≅ (classOf X).pointFunctor :=
  X.comparisonToRepresentative.pointFunctorIso

/-- Restrict that same choice of comparison to the actual Nilp category. -/
def nilpPointFunctorIsoToRepresentative (X : OrderAtlasPresentation O D R) (π : R) :
    X.order.nilpPointFunctor π ≅ (classOf X).nilpPointFunctor π :=
  X.comparisonToRepresentative.nilpPointFunctorIso π

/-- Class equality gives an actual formal comparison after making an explicit choice. -/
def comparisonOfClassEq {X Y : OrderAtlasPresentation O D R} (h : classOf X = classOf Y) :
    BasicAtlas.OrderAction.Comparison X.order Y.order :=
  Classical.choice ((classOf_eq_iff X Y).mp h)

end OrderAtlasPresentation

end Langlands.FormalGroup.ModuleLaw
