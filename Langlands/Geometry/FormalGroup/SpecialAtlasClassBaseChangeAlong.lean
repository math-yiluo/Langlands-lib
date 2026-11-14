import Langlands.Geometry.FormalGroup.SpecialAtlasBaseChangeAlong
import Langlands.Geometry.FormalGroup.SpecialAtlasClassBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeSelf

/-! # Supplied-target extension and identity on special-atlas classes -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S : Type v} [CommRing R] [CommRing S]

attribute [local instance] coefficientAlgebra coefficientScalarTower

section AlgebraTransport

variable {α : Algebra 𝒪[K] R}
variable {X Y : (letI := α; SpecialAtlas K D ι R)}

/-- Retype the supplied actual refined formal comparison along equal scalars. -/
def reAlgebraComparison (f : (letI := α; Comparison X Y))
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := β; Comparison (X.reAlgebra β e) (Y.reAlgebra β e)) := by
  cases e
  exact f

/-- The retyped formal comparison realizes the entire-family transport square. -/
theorem reAlgebraComparison_onPoints (f : (letI := α; Comparison X Y))
    (β : Algebra 𝒪[K] R) (e : α = β) (A : CommAlgCat.{v} R)
    (x : (letI := α; X.Point A)) :
    (letI := β; (reAlgebraComparison f β e).onPoints A (X.reAlgebraPointEquiv β e A x)) =
      Y.reAlgebraPointEquiv β e A (letI := α; f.onPoints A x) := by
  cases e
  rfl

/-- Scalar transport preserves existence of actual refined formal comparison. -/
theorem equivalent_reAlgebra (h : (letI := α; Equivalent X Y))
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := β; Equivalent (X.reAlgebra β e) (Y.reAlgebra β e)) :=
  h.map (fun f => reAlgebraComparison f β e)

namespace IsoClass

/-- Retype the actual comparison quotient along equality of scalar structures. -/
def reAlgebra (q : (letI := α; IsoClass (K := K) (D := D) (ι := ι) (R := R)))
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := β; IsoClass (K := K) (D := D) (ι := ι) (R := R)) :=
  Quotient.map (fun X => X.reAlgebra β e) (fun _ _ h => equivalent_reAlgebra h β e) q

@[simp]
theorem reAlgebra_classOf (X : (letI := α; SpecialAtlas K D ι R))
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := α; reAlgebra (classOf X) β e) = (letI := β; classOf (X.reAlgebra β e)) := rfl

end IsoClass
end AlgebraTransport

variable [Algebra 𝒪[K] R] [Algebra 𝒪[K] S]

/-- Extend the given refined formal comparison to the supplied target scalars. -/
def baseChangeAlongComparison {X Y : SpecialAtlas K D ι R} (g : Comparison X Y)
    (f : R →ₐ[𝒪[K]] S) : Comparison (X.baseChangeAlong f) (Y.baseChangeAlong f) :=
  reAlgebraComparison (baseChangeComparison g (BasicAtlas.coefficientTest f)) _
    (BasicAtlas.coefficientAlgebraAlong_eq f)

/-- The specified extended formal comparison realizes the complete-family square. -/
theorem baseChangeAlongComparison_onPoints {X Y : SpecialAtlas K D ι R}
    (g : Comparison X Y) (f : R →ₐ[𝒪[K]] S) (A : CommAlgCat.{v} S)
    (x : X.Point (restrictCoefficientAlgebra f A)) :
    (baseChangeAlongComparison g f).onPoints A (X.baseChangeAlongPointEquiv f A x) =
      Y.baseChangeAlongPointEquiv f A (g.onPoints (restrictCoefficientAlgebra f A) x) :=
  (reAlgebraComparison_onPoints (baseChangeComparison g (BasicAtlas.coefficientTest f)) _
    (BasicAtlas.coefficientAlgebraAlong_eq f) A
      (X.order.toBaseChangePoints (BasicAtlas.coefficientTest f) A x)).trans
        (congrArg
          ((Y.baseChange (BasicAtlas.coefficientTest f)).reAlgebraPointEquiv _
            (BasicAtlas.coefficientAlgebraAlong_eq f) A)
          (g.baseChange_onPoints (BasicAtlas.coefficientTest f) A x))

/-- The inverse family comparisons realize the reverse square for that same comparison. -/
theorem baseChangeAlongComparison_fromPoints {X Y : SpecialAtlas K D ι R}
    (g : Comparison X Y) (f : R →ₐ[𝒪[K]] S) (A : CommAlgCat.{v} S)
    (y : (X.baseChangeAlong f).Point A) :
    g.onPoints (restrictCoefficientAlgebra f A) ((X.baseChangeAlongPointEquiv f A).symm y) =
      (Y.baseChangeAlongPointEquiv f A).symm ((baseChangeAlongComparison g f).onPoints A y) := by
  apply (Y.baseChangeAlongPointEquiv f A).injective
  rw [← baseChangeAlongComparison_onPoints, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- Supplied-target extension preserves the actual refined formal equivalence relation. -/
theorem equivalent_baseChangeAlong {X Y : SpecialAtlas K D ι R} (h : Equivalent X Y)
    (f : R →ₐ[𝒪[K]] S) : Equivalent (X.baseChangeAlong f) (Y.baseChangeAlong f) :=
  h.map (fun g => baseChangeAlongComparison g f)

/-- The actual identity-extension isomorphism is exactly the full-order comparison. -/
def baseIdIso (X : SpecialAtlas K D ι R) :
    (X.baseChangeAlong (AlgHom.id 𝒪[K] R)).Iso X X.atlas.baseIdOpens_eq :=
  X.order.baseIdIso

/-- Identity extension compares by actual full-order formal maps after reflexive refinement. -/
def baseIdComparison (X : SpecialAtlas K D ι R) :
    Comparison (X.baseChangeAlong (AlgHom.id 𝒪[K] R)) X where
  left := BasicAtlas.CoverRefinement.refl _
  right := (BasicAtlas.CoverRefinement.refl _).retarget _ X.atlas.baseIdOpens_eq
  sameCover := rfl
  coordinateIso := X.baseIdIso.restrict (BasicAtlas.CoverRefinement.refl _)

/-- The identity comparison identifies the actual special-atlas classes. -/
theorem classOf_baseChangeAlong_id (X : SpecialAtlas K D ι R) :
    classOf (X.baseChangeAlong (AlgHom.id 𝒪[K] R)) = classOf X :=
  classOf_eq_of_comparison X.baseIdComparison

namespace IsoClass

/-- Supplied-target coefficient extension descends through actual formal comparison. -/
def baseChangeAlong (q : IsoClass (K := K) (D := D) (ι := ι) (R := R))
    (f : R →ₐ[𝒪[K]] S) : IsoClass (K := K) (D := D) (ι := ι) (R := S) :=
  Quotient.map (fun X => X.baseChangeAlong f) (fun _ _ h => equivalent_baseChangeAlong h f) q

@[simp]
theorem baseChangeAlong_classOf (X : SpecialAtlas K D ι R) (f : R →ₐ[𝒪[K]] S) :
    (classOf X).baseChangeAlong f = classOf (X.baseChangeAlong f) := rfl

/-- Extension along the supplied algebra identity is the identity on comparison classes. -/
@[simp]
theorem baseChangeAlong_id (q : IsoClass (K := K) (D := D) (ι := ι) (R := R)) :
    q.baseChangeAlong (AlgHom.id 𝒪[K] R) = q := by
  refine Quotient.inductionOn q ?_
  exact classOf_baseChangeAlong_id

end IsoClass

namespace HeightSquaredAtlas

variable {π : 𝒪[K]}

/-- Extend the actual atlas and its own height certificates to the supplied target scalars. -/
def baseChangeAlong (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π)
    (f : R →ₐ[𝒪[K]] S) :
    HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := S) π :=
  ⟨X.val.baseChangeAlong f, X.val.baseChangeAlong_height f X.property⟩

@[simp]
theorem val_baseChangeAlong
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π)
    (f : R →ₐ[𝒪[K]] S) : (X.baseChangeAlong f).val = X.val.baseChangeAlong f := rfl

/-- Both extended inputs retain height certificates and the supplied formal comparison. -/
theorem equivalent_baseChangeAlong
    {X Y : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π}
    (h : Equivalent X Y) (f : R →ₐ[𝒪[K]] S) :
    Equivalent (X.baseChangeAlong f) (Y.baseChangeAlong f) :=
  SpecialAtlas.equivalent_baseChangeAlong h f

/-- Identity extension is certified by the same actual refined formal comparison. -/
theorem classOf_baseChangeAlong_id
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) :
    classOf (X.baseChangeAlong (AlgHom.id 𝒪[K] R)) = classOf X :=
  classOf_eq_of_comparison X.val.baseIdComparison

namespace IsoClass

/-- Descend supplied-target extension inside the already height-certified subtype. -/
def baseChangeAlong (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π)
    (f : R →ₐ[𝒪[K]] S) : IsoClass (K := K) (D := D) (ι := ι) (R := S) π :=
  Quotient.map (fun X => X.baseChangeAlong f) (fun _ _ h => equivalent_baseChangeAlong h f) q

@[simp]
theorem baseChangeAlong_classOf
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π)
    (f : R →ₐ[𝒪[K]] S) : (classOf X).baseChangeAlong f = classOf (X.baseChangeAlong f) := rfl

/-- Forgetting height commutes with extension along the supplied scalar map. -/
@[simp]
theorem forgetHeight_baseChangeAlong
    (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π) (f : R →ₐ[𝒪[K]] S) :
    (q.baseChangeAlong f).forgetHeight = q.forgetHeight.baseChangeAlong f := by
  refine Quotient.inductionOn q ?_
  intro X
  rfl

/-- Supplied identity extension is the identity on the height-certified comparison quotient. -/
@[simp]
theorem baseChangeAlong_id (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π) :
    q.baseChangeAlong (AlgHom.id 𝒪[K] R) = q := by
  refine Quotient.inductionOn q ?_
  exact classOf_baseChangeAlong_id

end IsoClass
end HeightSquaredAtlas

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
