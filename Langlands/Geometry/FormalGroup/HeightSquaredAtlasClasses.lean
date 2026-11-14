import Langlands.Geometry.FormalGroup.SpecialAtlasPresentation

/-! # Comparison classes with actual height-d-squared certificates -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas.HeightSquaredAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R] {π : 𝒪[K]}

/-- Both inputs already have actual height certificates; the relation is formal comparison. -/
def Equivalent (X Y : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) : Prop :=
  SpecialAtlas.Equivalent X.val Y.val

theorem equivalent_refl (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) :
    Equivalent X X :=
  SpecialAtlas.equivalent_refl X.val

theorem equivalent_symm {X Y : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π}
    (h : Equivalent X Y) : Equivalent Y X :=
  SpecialAtlas.equivalent_symm h

theorem equivalent_trans
    {X Y Z : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π}
    (h : Equivalent X Y) (k : Equivalent Y Z) : Equivalent X Z :=
  SpecialAtlas.equivalent_trans h k

/-- Restrict the actual formal comparison setoid to the height-certified subtype. -/
def comparisonSetoid (π : 𝒪[K]) :
    Setoid (HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- Classes of actual special atlases already carrying height d² at pi. -/
def IsoClass (π : 𝒪[K]) :=
  Quotient (comparisonSetoid (K := K) (D := D) (ι := ι) (R := R) π)

/-- Send a supplied height-certified actual atlas to its comparison class. -/
def classOf (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) :
    IsoClass (K := K) (D := D) (ι := ι) (R := R) π :=
  Quotient.mk _ X

/-- The quotient equality criterion uses actual formal comparisons of certified inputs. -/
theorem classOf_eq_iff
    (X Y : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) :
    classOf X = classOf Y ↔ Equivalent X Y :=
  Quotient.eq

theorem classOf_eq_of_comparison
    {X Y : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π}
    (f : SpecialAtlas.Comparison X.val Y.val) : classOf X = classOf Y :=
  (classOf_eq_iff X Y).mpr ⟨f⟩

/-- Actual restriction preserves the supplied chart heights and global base condition. -/
def refine (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π)
    (q : BasicAtlas.CoverRefinement X.val.atlas) :
    HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π :=
  ⟨X.val.refine q, X.val.refine_height q X.property⟩

/-- The constructed formal comparison identifies the height-certified refinement's class. -/
theorem classOf_refine (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π)
    (q : BasicAtlas.CoverRefinement X.val.atlas) : classOf (refine X q) = classOf X :=
  (classOf_eq_of_comparison (X.val.comparisonOfRefinement q)).symm

namespace IsoClass

/-- Forget height certificates on classes through the same actual formal relation. -/
def forgetHeight : IsoClass (K := K) (D := D) (ι := ι) (R := R) π →
    SpecialAtlas.IsoClass (K := K) (D := D) (ι := ι) (R := R) :=
  Quotient.map Subtype.val (fun _ _ h => h)

@[simp]
theorem forgetHeight_classOf
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) :
    forgetHeight (classOf X) = SpecialAtlas.classOf X.val := rfl

/-- The restricted relation gives an injection, without transporting any height certificate. -/
theorem forgetHeight_injective :
    Function.Injective (forgetHeight (K := K) (D := D) (ι := ι) (R := R) (π := π)) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro X Y h
  exact (classOf_eq_iff X Y).mpr ((SpecialAtlas.classOf_eq_iff X.val Y.val).mp h)

/-- Choose a representative inside the already height-certified subtype. -/
def representative (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π) :
    HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π :=
  Quotient.out q

@[simp]
theorem classOf_representative (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π) :
    classOf q.representative = q :=
  Quotient.out_eq q

/-- The chosen representative retains its own original scalar-kernel height certificate. -/
theorem representative_height (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π) :
    q.representative.val.HasHeightSquared π :=
  q.representative.property

/-- In particular, pi has nilpotent actual image in the atlas base. -/
theorem base_nilpotent (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π) :
    IsNilpotent (algebraMap 𝒪[K] R π) :=
  q.representative.val.base_nilpotent q.representative_height

/-- Evaluate the chosen height-certified representative's actual point functor. -/
def pointFunctor (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π) :
    CommAlgCat.{v} R ⥤ ModuleCat.{v + 1} (IntegerRing K D) :=
  q.representative.val.pointFunctor

/-- Restrict that same chosen functor to Nilp for the actual image of pi. -/
def nilpPointFunctor (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π) :
    Nilp R (algebraMap 𝒪[K] R π) ⥤ ModuleCat.{v + 1} (IntegerRing K D) :=
  q.representative.val.nilpPointFunctor (algebraMap 𝒪[K] R π)

end IsoClass

/-- Choose actual formal maps to the chosen height-certified class representative. -/
def comparisonToRepresentative
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) :
    SpecialAtlas.Comparison X.val (classOf X).representative.val :=
  Classical.choice ((classOf_eq_iff X (classOf X).representative).mp
    (IsoClass.classOf_representative (classOf X)).symm)

/-- The chosen actual formal comparison gives a natural division-order-module isomorphism. -/
def pointFunctorIsoToRepresentative
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) :
    X.val.pointFunctor ≅ (classOf X).pointFunctor :=
  (comparisonToRepresentative X).pointFunctorIso

/-- The same chosen actual formal maps give the isomorphism on pi-nilpotent tests. -/
def nilpPointFunctorIsoToRepresentative
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) :
    X.val.nilpPointFunctor (algebraMap 𝒪[K] R π) ≅ (classOf X).nilpPointFunctor :=
  (comparisonToRepresentative X).nilpPointFunctorIso (algebraMap 𝒪[K] R π)

/-- Class equality between certified inputs supplies actual formal maps after a choice. -/
def comparisonOfClassEq
    {X Y : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π}
    (h : classOf X = classOf Y) : SpecialAtlas.Comparison X.val Y.val :=
  Classical.choice ((classOf_eq_iff X Y).mp h)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas.HeightSquaredAtlas
