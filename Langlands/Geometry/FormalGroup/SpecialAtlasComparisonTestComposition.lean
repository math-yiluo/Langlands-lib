import Langlands.Geometry.FormalGroup.AtlasOrderComparisonTestComposition
import Langlands.Geometry.FormalGroup.SpecialAtlasComparisonTestAlong
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlongComposition

/-! # Actual test-comparison composition over supplied scalar structures -/

noncomputable section

universe u v w z s

namespace Langlands.FormalGroup.ModuleLaw.OrderAction.Iso

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}
variable {E : OrderAction D M} {E' : OrderAction D N}
variable {E'' : OrderAction D P} {E''' : OrderAction D Q}

/-- Rationalize the four actual integral isomorphisms and their specified square. -/
def rationalSquare (f : Iso E E') (r : Iso E' E'') (l : Iso E E''') (d : Iso E''' E'')
    (h : f.trans r = l.trans d) :
    QuasiIsogeny.CommutingSquare (F := F) E E' E'' E''' :=
  QuasiIsogeny.CommutingSquare.mk (QuasiIsogeny.ofIso f) (QuasiIsogeny.ofIso r)
    (QuasiIsogeny.ofIso l) (QuasiIsogeny.ofIso d) (by
      apply QuasiIsogeny.ext
      apply RationalHom.ext
      have hh := congrArg (fun z => z.hom.val) h
      exact (ModuleLaw.RationalHom.ofHom_comp (F := F) r.hom.val f.hom.val).symm.trans
        ((congrArg (fun z => ModuleLaw.RationalHom.ofHom (F := F) z) hh).trans
          (ModuleLaw.RationalHom.ofHom_comp (F := F) d.hom.val l.hom.val)))

end Langlands.FormalGroup.ModuleLaw.OrderAction.Iso

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S T : Type v} [CommRing R] [CommRing S] [CommRing T] [Algebra 𝒪[K] R]
variable {X Y : SpecialAtlas K D ι R}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Extend the actual comparison twice while retaining the supplied intermediate and final scalars. -/
def iteratedReAlgebraComparison (c : Comparison X Y) (B : CommAlgCat.{v} R)
    (C : CommAlgCat.{v} B) (β : Algebra 𝒪[K] B)
    (e : coefficientAlgebra (O := 𝒪[K]) B = β)
    (γ : Algebra 𝒪[K] C) (d : (letI := β; coefficientAlgebra (O := 𝒪[K]) C) = γ) :=
  letI := β
  reAlgebraComparison (baseChangeComparison
    (reAlgebraComparison (baseChangeComparison c B) β e) C) γ d

/-- Direct extension of the same actual comparison with the induced final scalar equality. -/
def directReAlgebraComparison (c : Comparison X Y) (B : CommAlgCat.{v} R)
    (C : CommAlgCat.{v} B) (β : Algebra 𝒪[K] B)
    (e : coefficientAlgebra (O := 𝒪[K]) B = β)
    (γ : Algebra 𝒪[K] C) (d : (letI := β; coefficientAlgebra (O := 𝒪[K]) C) = γ) :=
  reAlgebraComparison (baseChangeComparison c (BasicAtlas.restrictTest B C)) γ
    ((BasicAtlas.coefficientAlgebra_comp_transport B C β e).trans d)

set_option backward.isDefEq.respectTransparency false in
/-- Scalar transport retains the whole actual test-comparison composition square. -/
theorem testIso_baseCompReAlgebra (c : Comparison X Y) (B : CommAlgCat.{v} R)
    (C : CommAlgCat.{v} B) (β : Algebra 𝒪[K] B)
    (e : coefficientAlgebra (O := 𝒪[K]) B = β)
    (γ : Algebra 𝒪[K] C) (d : (letI := β; coefficientAlgebra (O := 𝒪[K]) C) = γ)
    (A : CommAlgCat.{v} C)
    (b : (letI := γ; (iteratedReAlgebraComparison c B C β e γ d).right.opens))
    (hb : IsUnit (algebraMap C A b.val))
    (b' : (letI := γ; (directReAlgebraComparison c B C β e γ d).right.opens))
    (hb' : IsUnit (algebraMap C A b'.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (BasicAtlas.restrictTest (BasicAtlas.restrictTest B C) A) a.val))
    (x : X.atlas.baseOpens (BasicAtlas.restrictTest B C))
    (y : Y.atlas.baseOpens (BasicAtlas.restrictTest B C))
    (hx : IsUnit (algebraMap C A x.val)) (hy : IsUnit (algebraMap C A y.val)) :
    (letI := γ;
      ((iteratedReAlgebraComparison c B C β e γ d).testIso A b hb
        (BasicAtlas.sourceChart
          (X := (letI := β;
            ((((X.baseChange B).reAlgebra β e).baseChange C).reAlgebra γ d).atlas))
          (Y := ((X.baseChange (BasicAtlas.restrictTest B C)).reAlgebra γ
            ((BasicAtlas.coefficientAlgebra_comp_transport B C β e).trans d)).atlas)
          (X.atlas.baseCompOpens_eq B C) x)
        (BasicAtlas.sourceChart
          (X := (letI := β;
            ((((Y.baseChange B).reAlgebra β e).baseChange C).reAlgebra γ d).atlas))
          (Y := ((Y.baseChange (BasicAtlas.restrictTest B C)).reAlgebra γ
            ((BasicAtlas.coefficientAlgebra_comp_transport B C β e).trans d)).atlas)
          (Y.atlas.baseCompOpens_eq B C) y) hx hy).trans
          ((Y.order.baseCompReAlgebraIso B C β e γ d).onChart A y hy) =
        ((X.order.baseCompReAlgebraIso B C β e γ d).onChart A x hx).trans
          ((directReAlgebraComparison c B C β e γ d).testIso A b' hb' x y hx hy)) := by
  cases e
  cases d
  exact c.testIso_baseComp B C A b hb b' hb' a ha x y hx hy

variable [Algebra 𝒪[K] S] [Algebra 𝒪[K] T]

set_option backward.isDefEq.respectTransparency false in
/-- The actual supplied coefficient-composition map intertwines both specified test comparisons. -/
theorem testIso_baseAlongComp (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T)
    (A : CommAlgCat.{v} T)
    (b : (baseChangeAlongComparison (baseChangeAlongComparison c f) g).right.opens)
    (hb : IsUnit (algebraMap T A b.val))
    (b' : (baseChangeAlongComparison c (g.comp f)).right.opens)
    (hb' : IsUnit (algebraMap T A b'.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictCoefficientAlgebra (g.comp f) A) a.val))
    (x : (X.baseChangeAlong (g.comp f)).atlas.opens)
    (y : (Y.baseChangeAlong (g.comp f)).atlas.opens)
    (hx : IsUnit (algebraMap T A x.val)) (hy : IsUnit (algebraMap T A y.val)) :
    ((baseChangeAlongComparison (baseChangeAlongComparison c f) g).testIso A b hb
      (BasicAtlas.sourceChart (X.atlas.baseAlongCompOpens_eq f g) x)
      (BasicAtlas.sourceChart (Y.atlas.baseAlongCompOpens_eq f g) y) hx hy).trans
        ((Y.order.baseAlongCompIso f g).onChart A y hy) =
      ((X.order.baseAlongCompIso f g).onChart A x hx).trans
        ((baseChangeAlongComparison c (g.comp f)).testIso A b' hb' x y hx hy) :=
  testIso_baseCompReAlgebra c (BasicAtlas.coefficientTest f) (BasicAtlas.coefficientTest g) _
    (BasicAtlas.coefficientAlgebraAlong_eq f) _ (BasicAtlas.coefficientAlgebraAlong_eq g)
    A b hb b' hb' a ha x y hx hy

/-- Four specified actual rational test maps with their supplied-coefficient composition square. -/
def baseAlongCompTestSquare (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T)
    (A : CommAlgCat.{v} T)
    (b : (baseChangeAlongComparison (baseChangeAlongComparison c f) g).right.opens)
    (hb : IsUnit (algebraMap T A b.val))
    (b' : (baseChangeAlongComparison c (g.comp f)).right.opens)
    (hb' : IsUnit (algebraMap T A b'.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictCoefficientAlgebra (g.comp f) A) a.val))
    (x : (X.baseChangeAlong (g.comp f)).atlas.opens)
    (y : (Y.baseChangeAlong (g.comp f)).atlas.opens)
    (hx : IsUnit (algebraMap T A x.val)) (hy : IsUnit (algebraMap T A y.val)) :=
  ModuleLaw.OrderAction.Iso.rationalSquare (F := K)
    ((baseChangeAlongComparison (baseChangeAlongComparison c f) g).testIso A b hb
      (BasicAtlas.sourceChart (X.atlas.baseAlongCompOpens_eq f g) x)
      (BasicAtlas.sourceChart (Y.atlas.baseAlongCompOpens_eq f g) y) hx hy)
    ((Y.order.baseAlongCompIso f g).onChart A y hy)
    ((X.order.baseAlongCompIso f g).onChart A x hx)
    ((baseChangeAlongComparison c (g.comp f)).testIso A b' hb' x y hx hy)
    (testIso_baseAlongComp c f g A b hb b' hb' a ha x y hx hy)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
