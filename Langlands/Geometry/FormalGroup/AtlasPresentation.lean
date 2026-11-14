import Langlands.Geometry.FormalGroup.AtlasComparisonEquivalence

/-! # Isomorphism classes of finite-dimensional formal atlas presentations -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

/-- An actual principal-cover formal module atlas with a specified finite dimension. -/
structure AtlasPresentation (O : Type u) [CommRing O] (R : Type v) [CommRing R]
    [Algebra O R] where
  dimension : ℕ
  atlas : BasicAtlas O R (Fin dimension)

namespace AtlasPresentation

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]

/-- Equivalence requires an actual formal isomorphism after actual refinements. -/
def Equivalent (X Y : AtlasPresentation O R) : Prop :=
  Nonempty (BasicAtlas.Comparison X.atlas Y.atlas)

theorem equivalent_refl (X : AtlasPresentation O R) : Equivalent X X :=
  ⟨BasicAtlas.Comparison.refl X.atlas⟩

theorem equivalent_symm {X Y : AtlasPresentation O R} (h : Equivalent X Y) :
    Equivalent Y X :=
  h.map BasicAtlas.Comparison.symm

theorem equivalent_trans {X Y Z : AtlasPresentation O R}
    (h : Equivalent X Y) (k : Equivalent Y Z) : Equivalent X Z := by
  obtain ⟨f⟩ := h
  obtain ⟨g⟩ := k
  exact ⟨f.trans g⟩

/-- The relation is a setoid by the constructed formal comparison operations. -/
def comparisonSetoid : Setoid (AtlasPresentation O R) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- Classes of presentations modulo actual formal comparison after refinement. -/
def IsoClass (O : Type u) [CommRing O] (R : Type v) [CommRing R] [Algebra O R] :=
  Quotient (comparisonSetoid (O := O) (R := R))

/-- Send an actual presentation to its class. -/
def classOf (X : AtlasPresentation O R) : IsoClass O R :=
  Quotient.mk _ X

/-- Equality of classes is exactly existence of the required formal comparison. -/
theorem classOf_eq_iff (X Y : AtlasPresentation O R) :
    classOf X = classOf Y ↔ Equivalent X Y :=
  Quotient.eq

/-- A given actual comparison identifies the two presentation classes. -/
theorem classOf_eq_of_comparison {X Y : AtlasPresentation O R}
    (f : BasicAtlas.Comparison X.atlas Y.atlas) : classOf X = classOf Y :=
  (classOf_eq_iff X Y).mpr ⟨f⟩

namespace IsoClass

/-- Choose an actual atlas presentation of a class. -/
def representative (q : IsoClass O R) : AtlasPresentation O R :=
  Quotient.out q

@[simp]
theorem classOf_representative (q : IsoClass O R) :
    classOf q.representative = q :=
  Quotient.out_eq q

/-- Evaluate the chosen representative's actual full-family point functor. -/
def pointFunctor (q : IsoClass O R) :
    CommAlgCat.{v} R ⥤ ModuleCat.{v + 1} O :=
  q.representative.atlas.pointFunctor

/-- Evaluate the chosen representative on algebras where pi is nilpotent. -/
def nilpPointFunctor (q : IsoClass O R) (π : R) :
    Nilp R π ⥤ ModuleCat.{v + 1} O :=
  q.representative.atlas.nilpPointFunctor π

end IsoClass

/-- Choose a genuine refined formal comparison with the class representative. -/
def comparisonToRepresentative (X : AtlasPresentation O R) :
    BasicAtlas.Comparison X.atlas (classOf X).representative.atlas :=
  Classical.choice ((classOf_eq_iff X (classOf X).representative).mp
    (IsoClass.classOf_representative (classOf X)).symm)

/-- The chosen comparison gives a natural isomorphism of actual point functors. -/
def pointFunctorIsoToRepresentative (X : AtlasPresentation O R) :
    X.atlas.pointFunctor ≅ (classOf X).pointFunctor :=
  X.comparisonToRepresentative.pointFunctorIso

/-- The same chosen formal comparison restricts to the actual Nilp category. -/
def nilpPointFunctorIsoToRepresentative (X : AtlasPresentation O R) (π : R) :
    X.atlas.nilpPointFunctor π ≅ (classOf X).nilpPointFunctor π :=
  X.comparisonToRepresentative.nilpPointFunctorIso π

/-- Equality of classes supplies a formal comparison, with an explicit choice. -/
def comparisonOfClassEq {X Y : AtlasPresentation O R} (h : classOf X = classOf Y) :
    BasicAtlas.Comparison X.atlas Y.atlas :=
  Classical.choice ((classOf_eq_iff X Y).mp h)

end AtlasPresentation

end Langlands.FormalGroup.ModuleLaw
