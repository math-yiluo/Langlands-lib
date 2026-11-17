import Langlands.Geometry.FormalGroup.DrinfeldFramedComparison
import Langlands.Geometry.FormalGroup.OrderScalarTransport
import Langlands.Geometry.FormalGroup.AtlasBaseChangeAlongComposition

/-! # Actual original framing squares on a restricted base-change test -/

noncomputable section

universe u v w z s

namespace Langlands.FormalGroup.ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] {α : Algebra O R}
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {M : (letI := α; ModuleLaw O R σ)} {N : (letI := α; ModuleLaw O R τ)}
variable {P : (letI := α; ModuleLaw O R υ)} {Q : (letI := α; ModuleLaw O R ω)}
variable {E : (letI := α; OrderAction D M)} {E' : (letI := α; OrderAction D N)}
variable {E'' : (letI := α; OrderAction D P)} {E''' : (letI := α; OrderAction D Q)}

/-- Retain the four actual rational maps and their proved square through scalar equality. -/
def reAlgebra (s : (letI := α; CommutingSquare (F := F) E E' E'' E'''))
    (β : Algebra O R) (e : α = β) :
    (letI := β; CommutingSquare (F := F) (E.reAlgebra β e) (E'.reAlgebra β e)
      (E''.reAlgebra β e) (E'''.reAlgebra β e)) := by
  cases e
  exact s

@[simp]
theorem reAlgebra_top (s : (letI := α; CommutingSquare (F := F) E E' E'' E'''))
    (β : Algebra O R) (e : α = β) :
    (letI := β; (s.reAlgebra β e).top) = (letI := α; s.top.reAlgebra β e) := by
  cases e
  rfl

@[simp]
theorem reAlgebra_right (s : (letI := α; CommutingSquare (F := F) E E' E'' E'''))
    (β : Algebra O R) (e : α = β) :
    (letI := β; (s.reAlgebra β e).right) = (letI := α; s.right.reAlgebra β e) := by
  cases e
  rfl

@[simp]
theorem reAlgebra_left (s : (letI := α; CommutingSquare (F := F) E E' E'' E'''))
    (β : Algebra O R) (e : α = β) :
    (letI := β; (s.reAlgebra β e).left) = (letI := α; s.left.reAlgebra β e) := by
  cases e
  rfl

@[simp]
theorem reAlgebra_bottom (s : (letI := α; CommutingSquare (F := F) E E' E'' E'''))
    (β : Algebra O R) (e : α = β) :
    (letI := β; (s.reAlgebra β e).bottom) = (letI := α; s.bottom.reAlgebra β e) := by
  cases e
  rfl

end Langlands.FormalGroup.ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas.Comparison

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := κ) π}
variable {X Y : DrinfeldFramedAtlas Φ A}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The given original framing square, evaluated on the restricted new test and
transported to the actual new scalar structure on that same ring. -/
def originalSquareOnRestrictedTest (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (SpecialAtlas.reductionComparison c.targetComparison).right.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C) b.val)) :=
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  let d := SpecialAtlas.reductionComparison c.targetComparison
  letI := coefficientAlgebra (O := 𝒪[K]) T
  let square := ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.mk
    (X.refinedChartFraming d.left T
      (BasicAtlas.sourceChart (X := d.left.atlas) (Y := d.right.atlas) d.sameCover b) hb)
    (reducedComparisonOnChart d T b hb)
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := T) (F := K)
      ((globalFrameIso c.residue_eq).map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj T)))
    (Y.refinedChartFraming d.right T b hb) (c.square T b hb)
  square.reAlgebra γ eC

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas.Comparison
