import Langlands.Geometry.FormalGroup.SpecialAtlasComparisonTestSquare

/-! # Actual image and original test charts in extended refined comparisons -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S S' T : Type v} [CommRing R] [CommRing S] [CommRing S'] [CommRing T]
variable [Algebra 𝒪[K] R]
variable {X Y : SpecialAtlas K D ι R}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Retain the selected original finer generator through scalar retyping of an extended comparison. -/
def baseChangeReAlgebraComparisonOriginalChart (c : Comparison X Y) (B : CommAlgCat.{v} R)
    (β : Algebra 𝒪[K] B) (e : coefficientAlgebra (O := 𝒪[K]) B = β)
    (b : (letI := β; (reAlgebraComparison (baseChangeComparison c B) β e).right.opens)) :
    c.right.opens := by
  cases e
  exact c.right.atlas.baseSource B b

/-- The retained actual original generator is invertible on the restricted test. -/
theorem baseChangeReAlgebraComparisonOriginalChart_unit (c : Comparison X Y)
    (B : CommAlgCat.{v} R) (β : Algebra 𝒪[K] B)
    (e : coefficientAlgebra (O := 𝒪[K]) B = β) (A : CommAlgCat.{v} B)
    (b : (letI := β; (reAlgebraComparison (baseChangeComparison c B) β e).right.opens))
    (hb : IsUnit (algebraMap B A b.val)) :
    IsUnit (algebraMap R (BasicAtlas.restrictTest B A)
      (baseChangeReAlgebraComparisonOriginalChart c B β e b).val) := by
  cases e
  exact c.right.atlas.baseSource_unit B A b hb

/-- The image of a specified original finer generator through the same supplied scalar retyping. -/
def baseChangeReAlgebraComparisonImageChart (c : Comparison X Y) (B : CommAlgCat.{v} R)
    (β : Algebra 𝒪[K] B) (e : coefficientAlgebra (O := 𝒪[K]) B = β) (a : c.right.opens) :
    (letI := β; (reAlgebraComparison (baseChangeComparison c B) β e).right.opens) := by
  cases e
  exact ⟨algebraMap R B a.val, ⟨a.val, a.property, rfl⟩⟩

/-- The complete generator value is the actual coefficient image. -/
theorem baseChangeReAlgebraComparisonImageChart_val (c : Comparison X Y) (B : CommAlgCat.{v} R)
    (β : Algebra 𝒪[K] B) (e : coefficientAlgebra (O := 𝒪[K]) B = β) (a : c.right.opens) :
    (baseChangeReAlgebraComparisonImageChart c B β e a).val = algebraMap R B a.val := by
  cases e
  rfl

/-- Unit evidence for the specified original chart gives unit evidence for its actual image chart. -/
theorem baseChangeReAlgebraComparisonImageChart_unit (c : Comparison X Y) (B : CommAlgCat.{v} R)
    (β : Algebra 𝒪[K] B) (e : coefficientAlgebra (O := 𝒪[K]) B = β) (A : CommAlgCat.{v} B)
    (a : c.right.opens) (ha : IsUnit (algebraMap R (BasicAtlas.restrictTest B A) a.val)) :
    IsUnit (algebraMap B A (baseChangeReAlgebraComparisonImageChart c B β e a).val) := by
  cases e
  exact ha

variable [Algebra 𝒪[K] S] [Algebra 𝒪[K] S'] [Algebra 𝒪[K] T]

/-- The retained original finer chart for a comparison extended along the supplied scalar map. -/
def baseChangeAlongComparisonOriginalChart (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S)
    (b : (baseChangeAlongComparison c f).right.opens) : c.right.opens :=
  baseChangeReAlgebraComparisonOriginalChart c (BasicAtlas.coefficientTest f) _
    (BasicAtlas.coefficientAlgebraAlong_eq f) b

/-- The retained original finer chart has its actual unit evidence on the restricted test. -/
theorem baseChangeAlongComparisonOriginalChart_unit (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S)
    (A : CommAlgCat.{v} S) (b : (baseChangeAlongComparison c f).right.opens)
    (hb : IsUnit (algebraMap S A b.val)) :
    IsUnit (algebraMap R (restrictCoefficientAlgebra f A)
      (baseChangeAlongComparisonOriginalChart c f b).val) :=
  baseChangeReAlgebraComparisonOriginalChart_unit c (BasicAtlas.coefficientTest f) _
    (BasicAtlas.coefficientAlgebraAlong_eq f) A b hb

/-- The actual image finer chart of a supplied original comparison generator. -/
def baseChangeAlongComparisonImageChart (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S)
    (a : c.right.opens) : (baseChangeAlongComparison c f).right.opens :=
  baseChangeReAlgebraComparisonImageChart c (BasicAtlas.coefficientTest f) _
    (BasicAtlas.coefficientAlgebraAlong_eq f) a

/-- The actual image chart has the specified supplied-map generator. -/
theorem baseChangeAlongComparisonImageChart_val (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S)
    (a : c.right.opens) : (baseChangeAlongComparisonImageChart c f a).val = f a.val :=
  baseChangeReAlgebraComparisonImageChart_val c (BasicAtlas.coefficientTest f) _
    (BasicAtlas.coefficientAlgebraAlong_eq f) a

/-- A unit original generator remains invertible in its supplied-map image chart on the same test ring. -/
theorem baseChangeAlongComparisonImageChart_unit (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S)
    (A : CommAlgCat.{v} S) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictCoefficientAlgebra f A) a.val)) :
    IsUnit (algebraMap S A (baseChangeAlongComparisonImageChart c f a).val) :=
  baseChangeReAlgebraComparisonImageChart_unit c (BasicAtlas.coefficientTest f) _
    (BasicAtlas.coefficientAlgebraAlong_eq f) A a ha

/-- The actual original finer generator selected through both coefficient extensions. -/
def baseAlongCompOriginalChart (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T)
    (b : (baseChangeAlongComparison (baseChangeAlongComparison c f) g).right.opens) : c.right.opens :=
  baseChangeAlongComparisonOriginalChart c f
    (baseChangeAlongComparisonOriginalChart (baseChangeAlongComparison c f) g b)

/-- Iterated original-chart selection supplies unit evidence over the actual composite restriction. -/
theorem baseAlongCompOriginalChart_unit (c : Comparison X Y)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T) (A : CommAlgCat.{v} T)
    (b : (baseChangeAlongComparison (baseChangeAlongComparison c f) g).right.opens)
    (hb : IsUnit (algebraMap T A b.val)) :
    IsUnit (algebraMap R (restrictCoefficientAlgebra (g.comp f) A)
      (baseAlongCompOriginalChart c f g b).val) :=
  baseChangeAlongComparisonOriginalChart_unit c f (restrictCoefficientAlgebra g A) _
    (baseChangeAlongComparisonOriginalChart_unit (baseChangeAlongComparison c f) g A b hb)

set_option backward.isDefEq.respectTransparency false in
/-- The actual coefficient-square test-comparison equation needs only its two supplied iterated finer charts. -/
theorem testIso_baseAlongSquare_onCharts (c : Comparison X Y)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T)
    (p : R →ₐ[𝒪[K]] S') (q : S' →ₐ[𝒪[K]] T) (e : g.comp f = q.comp p)
    (A : CommAlgCat.{v} T)
    (b : (baseChangeAlongComparison (baseChangeAlongComparison c f) g).right.opens)
    (hb : IsUnit (algebraMap T A b.val))
    (b' : (baseChangeAlongComparison (baseChangeAlongComparison c p) q).right.opens)
    (hb' : IsUnit (algebraMap T A b'.val))
    (x : ((X.baseChangeAlong p).baseChangeAlong q).atlas.opens)
    (y : ((Y.baseChangeAlong p).baseChangeAlong q).atlas.opens)
    (hx : IsUnit (algebraMap T A x.val)) (hy : IsUnit (algebraMap T A y.val)) :
    ((baseChangeAlongComparison (baseChangeAlongComparison c f) g).testIso A b hb
      (BasicAtlas.sourceChart (X.atlas.baseAlongSquareOpens_eq f g p q e) x)
      (BasicAtlas.sourceChart (Y.atlas.baseAlongSquareOpens_eq f g p q e) y) hx hy).trans
        ((Y.order.baseAlongSquareIso f g p q e).onChart A y hy) =
      ((X.order.baseAlongSquareIso f g p q e).onChart A x hx).trans
        ((baseChangeAlongComparison (baseChangeAlongComparison c p) q).testIso A b' hb' x y hx hy) := by
  let a := baseAlongCompOriginalChart c p q b'
  have ha := baseAlongCompOriginalChart_unit c p q A b' hb'
  have haf : IsUnit (algebraMap R (restrictCoefficientAlgebra (g.comp f) A) a.val) := by
    change IsUnit (algebraMap T A ((g.comp f) a.val))
    have hqa : IsUnit (algebraMap T A ((q.comp p) a.val)) := ha
    simpa only [e] using hqa
  let d := baseChangeAlongComparisonImageChart c (g.comp f) a
  have hd := baseChangeAlongComparisonImageChart_unit c (g.comp f) A a haf
  let d' := baseChangeAlongComparisonImageChart c (q.comp p) a
  have hd' := baseChangeAlongComparisonImageChart_unit c (q.comp p) A a ha
  exact testIso_baseAlongSquare c f g p q e A b hb b' hb' d hd d' hd' a ha x y hx hy

/-- The actual rational coefficient-square test comparison with all auxiliary charts constructed. -/
def baseAlongSquareTestSquareOnCharts (c : Comparison X Y)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T)
    (p : R →ₐ[𝒪[K]] S') (q : S' →ₐ[𝒪[K]] T) (e : g.comp f = q.comp p)
    (A : CommAlgCat.{v} T)
    (b : (baseChangeAlongComparison (baseChangeAlongComparison c f) g).right.opens)
    (hb : IsUnit (algebraMap T A b.val))
    (b' : (baseChangeAlongComparison (baseChangeAlongComparison c p) q).right.opens)
    (hb' : IsUnit (algebraMap T A b'.val))
    (x : ((X.baseChangeAlong p).baseChangeAlong q).atlas.opens)
    (y : ((Y.baseChangeAlong p).baseChangeAlong q).atlas.opens)
    (hx : IsUnit (algebraMap T A x.val)) (hy : IsUnit (algebraMap T A y.val)) :=
  ModuleLaw.OrderAction.Iso.rationalSquare (F := K)
    ((baseChangeAlongComparison (baseChangeAlongComparison c f) g).testIso A b hb
      (BasicAtlas.sourceChart (X.atlas.baseAlongSquareOpens_eq f g p q e) x)
      (BasicAtlas.sourceChart (Y.atlas.baseAlongSquareOpens_eq f g p q e) y) hx hy)
    ((Y.order.baseAlongSquareIso f g p q e).onChart A y hy)
    ((X.order.baseAlongSquareIso f g p q e).onChart A x hx)
    ((baseChangeAlongComparison (baseChangeAlongComparison c p) q).testIso A b' hb' x y hx hy)
    (testIso_baseAlongSquare_onCharts c f g p q e A b hb b' hb' x y hx hy)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
