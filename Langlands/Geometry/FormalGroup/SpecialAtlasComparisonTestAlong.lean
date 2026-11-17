import Langlands.Geometry.FormalGroup.AtlasOrderComparisonTestBaseChange
import Langlands.Geometry.FormalGroup.SpecialAtlasClassBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlongCharts

/-! # Actual test comparisons over supplied target scalars -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra 𝒪[K] R]
variable {X Y : SpecialAtlas K D ι R}

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option backward.isDefEq.respectTransparency false in
/-- Transport the same original actual test comparison through supplied target scalar structures. -/
def baseChangeReAlgebraOriginalTestIso (c : Comparison X Y) (T : CommAlgCat.{v} R)
    (β : Algebra 𝒪[K] T) (e : coefficientAlgebra (O := 𝒪[K]) T = β)
    (C : CommAlgCat.{v} T) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (BasicAtlas.restrictTest T C) a.val))
    (x : X.atlas.baseOpens T) (y : Y.atlas.baseOpens T)
    (hx : IsUnit (algebraMap T C x.val)) (hy : IsUnit (algebraMap T C y.val)) :=
  let A := BasicAtlas.restrictTest T C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) A
  letI := β
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport T C β e
  let si := BasicAtlas.OrderAction.baseChangeReAlgebraOrderChartIso X.order T β e C x hx
  let ti := BasicAtlas.OrderAction.baseChangeReAlgebraOrderChartIso Y.order T β e C y hy
  let oi := (letI := δ;
    (c.testIso A a ha (X.atlas.baseSource T x) (Y.atlas.baseSource T y)
      (X.atlas.baseSource_unit T C x hx) (Y.atlas.baseSource_unit T C y hy)).reAlgebra γ eC)
  letI := γ
  ModuleLaw.OrderAction.Iso.trans (O := 𝒪[K]) (R := C) si
    (ModuleLaw.OrderAction.Iso.trans (O := 𝒪[K]) (R := C) oi
      (ModuleLaw.OrderAction.Iso.symm (O := 𝒪[K]) (R := C) ti))

set_option backward.isDefEq.respectTransparency false in
/-- Scalar-retyped extension retains the actual original test comparison through its coefficient charts. -/
theorem testIso_baseChangeReAlgebra (c : Comparison X Y) (T : CommAlgCat.{v} R)
    (β : Algebra 𝒪[K] T) (e : coefficientAlgebra (O := 𝒪[K]) T = β)
    (C : CommAlgCat.{v} T)
    (b : (letI := β; (reAlgebraComparison (baseChangeComparison c T) β e).right.opens))
    (hb : IsUnit (algebraMap T C b.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (BasicAtlas.restrictTest T C) a.val))
    (x : X.atlas.baseOpens T) (y : Y.atlas.baseOpens T)
    (hx : IsUnit (algebraMap T C x.val)) (hy : IsUnit (algebraMap T C y.val)) :
    (letI := β; (reAlgebraComparison (baseChangeComparison c T) β e).testIso C b hb x y hx hy) =
      baseChangeReAlgebraOriginalTestIso c T β e C a ha x y hx hy := by
  cases e
  exact c.testIso_baseChange_eq_original T C b hb a ha x y hx hy

variable [Algebra 𝒪[K] S]

/-- The actual original test comparison transported over a supplied coefficient algebra map. -/
def baseChangeAlongOriginalTestIso (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S)
    (C : CommAlgCat.{v} S) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictCoefficientAlgebra f C) a.val))
    (x : (X.baseChangeAlong f).atlas.opens) (y : (Y.baseChangeAlong f).atlas.opens)
    (hx : IsUnit (algebraMap S C x.val)) (hy : IsUnit (algebraMap S C y.val)) :=
  baseChangeReAlgebraOriginalTestIso c (BasicAtlas.coefficientTest f) _
    (BasicAtlas.coefficientAlgebraAlong_eq f) C a ha x y hx hy

/-- The supplied-target extended comparison retains any specified original finer test chart. -/
theorem testIso_baseChangeAlong (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S)
    (C : CommAlgCat.{v} S) (b : (baseChangeAlongComparison c f).right.opens)
    (hb : IsUnit (algebraMap S C b.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictCoefficientAlgebra f C) a.val))
    (x : (X.baseChangeAlong f).atlas.opens) (y : (Y.baseChangeAlong f).atlas.opens)
    (hx : IsUnit (algebraMap S C x.val)) (hy : IsUnit (algebraMap S C y.val)) :
    (baseChangeAlongComparison c f).testIso C b hb x y hx hy =
      baseChangeAlongOriginalTestIso c f C a ha x y hx hy :=
  testIso_baseChangeReAlgebra c (BasicAtlas.coefficientTest f) _
    (BasicAtlas.coefficientAlgebraAlong_eq f) C b hb a ha x y hx hy

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
