import Langlands.Geometry.FormalGroup.SpecialAtlasInducedComparison
import Langlands.Geometry.FormalGroup.DivisionOrder

/-! # Actual integral-unit conjugation of special formal atlases -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {X : BasicAtlas O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Conjugate the actual order action on each original formal chart, retaining its actual transition maps. -/
def twist (E : OrderAction D X) (α : D ≃ₐ[O] D) : OrderAction D X where
  chart b := (E.chart b).twist α
  transition C b c hb hc d := E.transition C b c hb hc (α d)

@[simp]
theorem twist_chart (E : OrderAction D X) (α : D ≃ₐ[O] D) (b : X.opens) :
    (E.twist α).chart b = (E.chart b).twist α := rfl

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra 𝒪[K] R] [Algebra 𝒪[K] S]

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace SpecialModule

/-- Conjugate the actual order action by an integer unit and transport the special tangent certificate. -/
def twistIntegerUnit (X : SpecialModule K D ι R) (u : (IntegerRing K D)ˣ) : SpecialModule K D ι R where
  formalModule := X.formalModule
  order := LocalDivision.twist K D X.order (integerUnit K D u)
  unramified := X.unramified
  tangent := X.tangent.ofIso (LocalDivision.twistUnitIso K D X.order u)

/-- The original actual integral inverse maps identify the special module with its unit-conjugate action. -/
def twistIntegerUnitIso (X : SpecialModule K D ι R) (u : (IntegerRing K D)ˣ) :
    X.Iso (X.twistIntegerUnit u) := LocalDivision.twistUnitIso K D X.order u

/-- Unit conjugation retains the actual underlying scalar kernels and their height. -/
theorem twistIntegerUnit_height_iff (X : SpecialModule K D ι R) (u : (IntegerRing K D)ˣ) (π : 𝒪[K]) :
    (X.twistIntegerUnit u).HasHeightSquared π ↔ X.HasHeightSquared π := Iff.rfl

/-- Coefficient extension retains the same actual unit-conjugate formal module. -/
theorem twistIntegerUnit_map (X : SpecialModule K D ι R) (u : (IntegerRing K D)ˣ) (f : R →ₐ[𝒪[K]] S) :
    (X.twistIntegerUnit u).mapSameUniverse f = (X.mapSameUniverse f).twistIntegerUnit u := rfl

end SpecialModule

namespace SpecialAtlas

/-- Twist the chart order actions by the actual inverse-conjugation automorphism of an integer unit. -/
def twistIntegerUnit (X : SpecialAtlas K D ι R) (u : (IntegerRing K D)ˣ) : SpecialAtlas K D ι R where
  atlas := X.atlas
  order := X.order.twist (conjugation K D (integerUnit K D u))
  unramified := X.unramified
  tangent b := (X.tangent b).ofIso (LocalDivision.twistUnitIso K D (X.order.chart b) u)

/-- The actual inverse-unit formal endomorphisms identify the atlas with its unit-conjugate order action. -/
def twistIntegerUnitIso (X : SpecialAtlas K D ι R) (u : (IntegerRing K D)ˣ) :
    X.Iso (X.twistIntegerUnit u) rfl where
  hom := ⟨X.order.endomorphism (u⁻¹ : (IntegerRing K D)ˣ), by
    intro C b hb d
    exact (LocalDivision.twistUnitIso K D
      ((X.order.chart b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val C hb)) u).hom.property d⟩
  inv := ⟨X.order.endomorphism (u : IntegerRing K D), by
    intro C b hb d
    exact (LocalDivision.twistUnitIso K D
      ((X.order.chart b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val C hb)) u).inv.property d⟩
  inv_hom := by
    apply Subtype.ext
    apply BasicAtlas.Hom.ext
    intro C b hb
    exact congrArg Subtype.val (LocalDivision.twistUnitIso K D
      ((X.order.chart b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val C hb)) u).inv_hom
  hom_inv := by
    apply Subtype.ext
    apply BasicAtlas.Hom.ext
    intro C b hb
    exact congrArg Subtype.val (LocalDivision.twistUnitIso K D
      ((X.order.chart b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val C hb)) u).hom_inv

/-- The exact original comparison induced by the actual unit-conjugation atlas isomorphism. -/
def twistIntegerUnitComparison (X : SpecialAtlas K D ι R) (u : (IntegerRing K D)ˣ) :
    Comparison X (X.twistIntegerUnit u) :=
  BasicAtlas.OrderAction.Comparison.ofIso (X.twistIntegerUnitIso u) (BasicAtlas.CoverRefinement.refl _)

/-- Unit conjugation retains the actual scalar kernels and height certificates on every original chart. -/
theorem twistIntegerUnit_height_iff (X : SpecialAtlas K D ι R) (u : (IntegerRing K D)ˣ) (π : 𝒪[K]) :
    (X.twistIntegerUnit u).HasHeightSquared π ↔ X.HasHeightSquared π := Iff.rfl

/-- Coefficient extension retains the same actual unit-conjugate original atlas. -/
theorem twistIntegerUnit_baseChange (X : SpecialAtlas K D ι R) (u : (IntegerRing K D)ˣ)
    (B : CommAlgCat.{v} R) :
    (X.twistIntegerUnit u).baseChange B = (X.baseChange B).twistIntegerUnit u := rfl

omit [Algebra 𝒪[K] R] in
/-- Equal scalar-algebra structures retain the actual conjugated order action. -/
theorem twistIntegerUnit_reAlgebra {α : Algebra 𝒪[K] R}
    (X : (letI := α; SpecialAtlas K D ι R)) (u : (IntegerRing K D)ˣ)
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := α; (X.twistIntegerUnit u).reAlgebra β e) =
      (letI := β; (X.reAlgebra β e).twistIntegerUnit u) := by
  cases e
  rfl

/-- Supplied scalar extension retains the same actual unit-conjugate original atlas. -/
theorem twistIntegerUnit_baseChangeAlong (X : SpecialAtlas K D ι R) (u : (IntegerRing K D)ˣ)
    (f : R →ₐ[𝒪[K]] S) :
    (X.twistIntegerUnit u).baseChangeAlong f = (X.baseChangeAlong f).twistIntegerUnit u := by
  unfold baseChangeAlong
  rw [twistIntegerUnit_baseChange]
  exact twistIntegerUnit_reAlgebra _ u _ _

/-- The unit-conjugate atlas has exactly the same class, witnessed by its actual integral comparison. -/
theorem classOf_twistIntegerUnit (X : SpecialAtlas K D ι R) (u : (IntegerRing K D)ˣ) :
    classOf (X.twistIntegerUnit u) = classOf X :=
  (classOf_eq_of_comparison (X.twistIntegerUnitComparison u)).symm

namespace HeightSquaredAtlas

/-- Retain the actual height certificate with the unit-conjugate order action. -/
def twistIntegerUnit {π : 𝒪[K]} (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π)
    (u : (IntegerRing K D)ˣ) : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π :=
  ⟨X.val.twistIntegerUnit u, X.property⟩

/-- The height-certified comparison quotient retains the same class under actual unit conjugation. -/
theorem classOf_twistIntegerUnit {π : 𝒪[K]} (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π)
    (u : (IntegerRing K D)ˣ) : classOf (X.twistIntegerUnit u) = classOf X :=
  (classOf_eq_of_comparison (X.val.twistIntegerUnitComparison u)).symm

end HeightSquaredAtlas

end SpecialAtlas

end Langlands.FormalGroup.LocalDivision
