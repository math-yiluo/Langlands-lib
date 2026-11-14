import Langlands.Geometry.FormalGroup.OrderAtlasPresentation
import Langlands.Geometry.FormalGroup.SpecialAtlasRefinement

/-! # Classes of actual special formal division-order atlases -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]

/-- Retain the actual dimension-d atlas and its full division-order action. -/
def toOrderPresentation (X : SpecialAtlas K D ι R) :
    OrderAtlasPresentation 𝒪[K] (IntegerRing K D) R where
  dimension := CentralSimple.reducedDegree K D
  atlas := X.atlas
  order := X.order

/-- Comparisons are actual order-linear formal isomorphisms after principal refinement. -/
abbrev Comparison (X Y : SpecialAtlas K D ι R) :=
  BasicAtlas.OrderAction.Comparison X.order Y.order

/-- Equivalence records existence of such an actual formal comparison. -/
def Equivalent (X Y : SpecialAtlas K D ι R) : Prop :=
  Nonempty (Comparison X Y)

theorem equivalent_refl (X : SpecialAtlas K D ι R) : Equivalent X X :=
  ⟨BasicAtlas.OrderAction.Comparison.refl X.order⟩

theorem equivalent_symm {X Y : SpecialAtlas K D ι R} (h : Equivalent X Y) :
    Equivalent Y X :=
  h.map BasicAtlas.OrderAction.Comparison.symm

theorem equivalent_trans {X Y Z : SpecialAtlas K D ι R}
    (h : Equivalent X Y) (k : Equivalent Y Z) : Equivalent X Z := by
  obtain ⟨f⟩ := h
  obtain ⟨g⟩ := k
  exact ⟨f.trans g⟩

/-- The actual comparison constructors establish the three setoid laws. -/
def comparisonSetoid : Setoid (SpecialAtlas K D ι R) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- Special-atlas classes use actual refined division-order-linear formal comparison. -/
def IsoClass :=
  Quotient (comparisonSetoid (K := K) (D := D) (ι := ι) (R := R))

/-- Send an actual special atlas to its comparison class. -/
def classOf (X : SpecialAtlas K D ι R) : IsoClass (K := K) (D := D) (ι := ι) (R := R) :=
  Quotient.mk _ X

/-- Equality of special-atlas classes means existence of an actual formal comparison. -/
theorem classOf_eq_iff (X Y : SpecialAtlas K D ι R) :
    classOf X = classOf Y ↔ Equivalent X Y :=
  Quotient.eq

theorem classOf_eq_of_comparison {X Y : SpecialAtlas K D ι R}
    (f : Comparison X Y) : classOf X = classOf Y :=
  (classOf_eq_iff X Y).mpr ⟨f⟩

/-- Forgetting the special certificates retains exactly the same formal comparison. -/
theorem equivalent_toOrderPresentation {X Y : SpecialAtlas K D ι R}
    (h : Equivalent X Y) :
    OrderAtlasPresentation.Equivalent X.toOrderPresentation Y.toOrderPresentation :=
  h

/-- A special atlas compares with its actual refinement by the constructed formal maps. -/
def comparisonOfRefinement (X : SpecialAtlas K D ι R)
    (q : BasicAtlas.CoverRefinement X.atlas) : Comparison X (X.refine q) :=
  BasicAtlas.OrderAction.Comparison.ofRefinement X.order q

/-- This specified formal comparison evaluates to the actual complete-family restriction. -/
theorem comparisonOfRefinement_onPoints (X : SpecialAtlas K D ι R)
    (q : BasicAtlas.CoverRefinement X.atlas) (A : CommAlgCat.{v} R) (x : X.Point A) :
    (X.comparisonOfRefinement q).onPoints A x = X.refinementPointEquiv q A x :=
  BasicAtlas.OrderAction.Comparison.onPoints_ofRefinement X.order q A x

/-- Actual special refinement preserves the special-atlas comparison class. -/
theorem classOf_refine (X : SpecialAtlas K D ι R)
    (q : BasicAtlas.CoverRefinement X.atlas) : classOf (X.refine q) = classOf X :=
  (classOf_eq_of_comparison (X.comparisonOfRefinement q)).symm

namespace IsoClass

/-- Descend the actual underlying order presentation, keeping the same comparison witness. -/
def forgetSpecial : IsoClass (K := K) (D := D) (ι := ι) (R := R) →
    OrderAtlasPresentation.IsoClass 𝒪[K] (IntegerRing K D) R :=
  Quotient.map toOrderPresentation (fun _ _ h => equivalent_toOrderPresentation h)

@[simp]
theorem forgetSpecial_classOf (X : SpecialAtlas K D ι R) :
    forgetSpecial (classOf X) = OrderAtlasPresentation.classOf X.toOrderPresentation := rfl

/-- Choose an actual special atlas of the class, retaining its special certificates. -/
def representative (q : IsoClass (K := K) (D := D) (ι := ι) (R := R)) :
    SpecialAtlas K D ι R :=
  Quotient.out q

@[simp]
theorem classOf_representative (q : IsoClass (K := K) (D := D) (ι := ι) (R := R)) :
    classOf q.representative = q :=
  Quotient.out_eq q

/-- Evaluate the chosen special representative's actual division-order point functor. -/
def pointFunctor (q : IsoClass (K := K) (D := D) (ι := ι) (R := R)) :
    CommAlgCat.{v} R ⥤ ModuleCat.{v + 1} (IntegerRing K D) :=
  q.representative.pointFunctor

/-- Restrict that same chosen point functor to actual algebras with nilpotent pi. -/
def nilpPointFunctor (q : IsoClass (K := K) (D := D) (ι := ι) (R := R)) (π : R) :
    Nilp R π ⥤ ModuleCat.{v + 1} (IntegerRing K D) :=
  q.representative.nilpPointFunctor π

end IsoClass

/-- Choose an actual formal comparison from X to the chosen special representative. -/
def comparisonToRepresentative (X : SpecialAtlas K D ι R) :
    Comparison X (classOf X).representative :=
  Classical.choice ((classOf_eq_iff X (classOf X).representative).mp
    (IsoClass.classOf_representative (classOf X)).symm)

/-- This choice of actual formal comparison realizes a natural division-order isomorphism. -/
def pointFunctorIsoToRepresentative (X : SpecialAtlas K D ι R) :
    X.pointFunctor ≅ (classOf X).pointFunctor :=
  X.comparisonToRepresentative.pointFunctorIso

/-- Use the same chosen formal comparison on the actual Nilp subcategory. -/
def nilpPointFunctorIsoToRepresentative (X : SpecialAtlas K D ι R) (π : R) :
    X.nilpPointFunctor π ≅ (classOf X).nilpPointFunctor π :=
  X.comparisonToRepresentative.nilpPointFunctorIso π

/-- Class equality supplies an actual formal comparison after an explicit classical choice. -/
def comparisonOfClassEq {X Y : SpecialAtlas K D ι R} (h : classOf X = classOf Y) :
    Comparison X Y :=
  Classical.choice ((classOf_eq_iff X Y).mp h)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
