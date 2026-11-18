import Langlands.Geometry.FormalGroup.AtlasOrderInducedComparison
import Langlands.Geometry.FormalGroup.SpecialAtlasClassReduction

/-! # Supplied coefficients and reduction for comparisons induced by actual atlas maps -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra 𝒪[K] R]
variable {X Y : SpecialAtlas K D ι R} {h : X.atlas.opens = Y.atlas.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Retyping the coefficient extension keeps the complete inducing formal map. -/
theorem inducedBy_baseChangeReAlgebra (c : Comparison X Y) (f : X.Iso Y h)
    (hc : c.InducedBy f) (T : CommAlgCat.{v} R)
    (β : Algebra 𝒪[K] T) (e : coefficientAlgebra (O := 𝒪[K]) T = β) :
    (letI := β; (reAlgebraComparison (baseChangeComparison c T) β e).InducedBy
      ((f.baseChange T).reAlgebra β e)) := by
  cases e
  exact hc.baseChange T

variable [Algebra 𝒪[K] S]

/-- The supplied-target comparison is induced by extension of the same actual atlas isomorphism. -/
theorem inducedBy_baseChangeAlong (c : Comparison X Y) (f : X.Iso Y h)
    (hc : c.InducedBy f) (m : R →ₐ[𝒪[K]] S) :
    (baseChangeAlongComparison c m).InducedBy (f.baseChangeAlong m) :=
  inducedBy_baseChangeReAlgebra c f hc (BasicAtlas.coefficientTest m) _
    (BasicAtlas.coefficientAlgebraAlong_eq m)

/-- The specified original identity-base comparison is induced by the actual identity-base atlas map. -/
theorem baseIdComparison_inducedBy (X : SpecialAtlas K D ι R) :
    X.baseIdComparison.InducedBy X.baseIdIso :=
  BasicAtlas.OrderAction.Comparison.inducedBy_ofIso X.baseIdIso
    (BasicAtlas.CoverRefinement.refl _)

section Reduction

variable {r : R} {A : Nilp.{v,w} R r}
variable {U V : SpecialAtlas K D ι A.obj} {k : U.atlas.opens = V.atlas.opens}

/-- Quotient reduction retains the inducing actual isomorphism on every original test chart. -/
theorem inducedBy_reduction (c : Comparison U V) (f : U.Iso V k)
    (hc : c.InducedBy f) :
    (reductionComparison c).InducedBy f.reduction :=
  inducedBy_baseChangeAlong c f hc (Nilp.quotientO 𝒪[K] A)

/-- Retain exactly the specified reduced target comparison and its complete inducing certificate. -/
def inducedReductionComparison (c : Comparison U V) (f : U.Iso V k)
    (hc : c.InducedBy f) :
    {d : Comparison U.reduction V.reduction // d.InducedBy f.reduction} :=
  ⟨reductionComparison c, inducedBy_reduction c f hc⟩

end Reduction

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
