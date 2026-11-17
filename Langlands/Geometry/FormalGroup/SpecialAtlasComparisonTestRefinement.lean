import Langlands.Geometry.FormalGroup.SpecialAtlasComparisonTestReduction

/-! # Actual refined-chart and scalar-test comparison squares -/

noncomputable section

universe u v w z s

namespace Langlands.FormalGroup.ModuleLaw.OrderAction.Iso

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}
variable {E : OrderAction D M} {E' : OrderAction D N}
variable {E'' : OrderAction D P} {E''' : OrderAction D Q}

/-- Compose a specified conjugated actual formal map with its target comparison. -/
theorem conjugate_square {t : Iso E E'} {a : Iso E E'''} {o : Iso E''' E''} {b : Iso E' E''}
    (h : t = a.trans (o.trans b.symm)) : t.trans b = a.trans o := by
  apply ext_hom
  have ht := congrArg Iso.hom h
  change t.hom = (b.inv.comp o.hom).comp a.hom at ht
  change b.hom.comp t.hom = o.hom.comp a.hom
  rw [ht]
  simp only [← Hom.comp_assoc, b.hom_inv, Hom.id_comp]

end Langlands.FormalGroup.ModuleLaw.OrderAction.Iso

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {X : BasicAtlas O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual integral map from a specified original test chart to a specified finer test chart. -/
def parentOrderTestIso (q : CoverRefinement X) (E : OrderAction D X)
    (A : CommAlgCat.{v} R) (x : X.opens) (hx : IsUnit (algebraMap R A x.val))
    (b : q.opens) (hb : IsUnit (algebraMap R A b.val)) :=
  (E.transitionIso A x (q.source b) hx (q.source_unit A b hb)).trans (q.orderChartIso E A b hb).symm

/-- The complete correction series is the actual original transition to the selected parent chart. -/
theorem parentOrderTestIso_hom_coordinates (q : CoverRefinement X) (E : OrderAction D X)
    (A : CommAlgCat.{v} R) (x : X.opens) (hx : IsUnit (algebraMap R A x.val))
    (b : q.opens) (hb : IsUnit (algebraMap R A b.val)) :
    (q.parentOrderTestIso E A x hx b hb).hom.val.toHom.toCoordinateMap =
      (X.transition A x (q.source b) hx (q.source_unit A b hb)).hom.toHom.toCoordinateMap := by
  change CoordinateMap.id.comp (X.transition A x (q.source b) hx _).hom.toHom.toCoordinateMap = _
  exact CoordinateMap.id_comp _

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option backward.isDefEq.respectTransparency false in
/-- The actual comparison between original test charts commutes with its original refined chart map. -/
theorem testIso_refinement (c : Comparison E E') (A : CommAlgCat.{v} R)
    (b : c.right.opens) (hb : IsUnit (algebraMap R A b.val))
    (x : X.opens) (y : Y.opens)
    (hx : IsUnit (algebraMap R A x.val)) (hy : IsUnit (algebraMap R A y.val)) :
    (c.testIso A b hb x y hx hy).trans (c.right.parentOrderTestIso E' A y hy b hb) =
      (c.left.parentOrderTestIso E A x hx
        (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b) hb).trans
          (c.coordinateIso.onChart A b hb) := by
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (c.right.parentOrderTestIso E' A y hy b hb).hom.val.toHom.toCoordinateMap.comp
      (c.testIso A b hb x y hx hy).hom.val.toHom.toCoordinateMap =
    (c.coordinateIso.hom.val.hom A b hb).toHom.toCoordinateMap.comp
      (c.left.parentOrderTestIso E A x hx _ hb).hom.val.toHom.toCoordinateMap
  rw [c.right.parentOrderTestIso_hom_coordinates E' A y hy b hb,
    c.left.parentOrderTestIso_hom_coordinates E A x hx
      (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b) hb,
    c.testIso_hom_coordinates A b hb x y hx hy]
  have hY := congrArg (fun z => z.hom.toHom.toCoordinateMap)
    (Y.transition_cocycle A (c.right.source b) y (c.right.source b)
      (c.right.source_unit A b hb) hy (c.right.source_unit A b hb))
  have hs := congrArg (fun z => z.hom.toHom.toCoordinateMap)
    (Y.transition_self A (c.right.source b) (c.right.source_unit A b hb))
  change (Y.transition A y (c.right.source b) _ _).hom.toHom.toCoordinateMap.comp
      (Y.transition A (c.right.source b) y _ _).hom.toHom.toCoordinateMap =
    (Y.transition A (c.right.source b) (c.right.source b) _ _).hom.toHom.toCoordinateMap at hY
  change (Y.transition A (c.right.source b) (c.right.source b) _ _).hom.toHom.toCoordinateMap =
    CoordinateMap.id at hs
  simp only [← CoordinateMap.comp_assoc]
  rw [hY, hs, CoordinateMap.id_comp]

variable [IsDomain O] {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]

/-- The four actual rationalized maps in the refined-chart test comparison square. -/
def refinementTestSquare (c : Comparison E E') (A : CommAlgCat.{v} R)
    (b : c.right.opens) (hb : IsUnit (algebraMap R A b.val))
    (x : X.opens) (y : Y.opens)
    (hx : IsUnit (algebraMap R A x.val)) (hy : IsUnit (algebraMap R A y.val)) :=
  ModuleLaw.OrderAction.Iso.rationalSquare (F := F)
    (c.testIso A b hb x y hx hy) (c.right.parentOrderTestIso E' A y hy b hb)
    (c.left.parentOrderTestIso E A x hx
      (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b) hb)
    (c.coordinateIso.onChart A b hb) (c.testIso_refinement A b hb x y hx hy)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra 𝒪[K] R] [Algebra 𝒪[K] S]
variable {X Y : SpecialAtlas K D ι R}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Retain the actual original integral test comparison at the new induced test scalars. -/
def originalTestIsoOnRestrictedTest (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S)
    (C : CommAlgCat.{v} S) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictCoefficientAlgebra f C) a.val))
    (x : (X.baseChangeAlong f).atlas.opens) (y : (Y.baseChangeAlong f).atlas.opens)
    (hx : IsUnit (algebraMap S C x.val)) (hy : IsUnit (algebraMap S C y.val)) :=
  let A := restrictCoefficientAlgebra f C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) A
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest f) C _
    (BasicAtlas.coefficientAlgebraAlong_eq f)
  (letI := δ;
    (c.testIso A a ha (X.atlas.baseSource (BasicAtlas.coefficientTest f) x)
      (Y.atlas.baseSource (BasicAtlas.coefficientTest f) y)
      (X.atlas.baseSource_unit (BasicAtlas.coefficientTest f) C x hx)
      (Y.atlas.baseSource_unit (BasicAtlas.coefficientTest f) C y hy)).reAlgebra γ eC)

/-- The actual supplied-target comparison test map commutes with both coefficient-chart comparisons. -/
theorem testIso_baseChangeAlong_square (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S)
    (C : CommAlgCat.{v} S) (b : (baseChangeAlongComparison c f).right.opens)
    (hb : IsUnit (algebraMap S C b.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictCoefficientAlgebra f C) a.val))
    (x : (X.baseChangeAlong f).atlas.opens) (y : (Y.baseChangeAlong f).atlas.opens)
    (hx : IsUnit (algebraMap S C x.val)) (hy : IsUnit (algebraMap S C y.val)) :
    (letI := coefficientAlgebra (O := 𝒪[K]) C;
      ((baseChangeAlongComparison c f).testIso C b hb x y hx hy).trans
          (BasicAtlas.OrderAction.baseChangeAlongOrderChartIso Y.order f C y hy) =
        (BasicAtlas.OrderAction.baseChangeAlongOrderChartIso X.order f C x hx).trans
          (originalTestIsoOnRestrictedTest c f C a ha x y hx hy)) :=
  ModuleLaw.OrderAction.Iso.conjugate_square (testIso_baseChangeAlong c f C b hb a ha x y hx hy)

/-- The four specified actual rational maps in supplied coefficient-test comparison naturality. -/
def baseChangeAlongTestSquare (c : Comparison X Y) (f : R →ₐ[𝒪[K]] S)
    (C : CommAlgCat.{v} S) (b : (baseChangeAlongComparison c f).right.opens)
    (hb : IsUnit (algebraMap S C b.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictCoefficientAlgebra f C) a.val))
    (x : (X.baseChangeAlong f).atlas.opens) (y : (Y.baseChangeAlong f).atlas.opens)
    (hx : IsUnit (algebraMap S C x.val)) (hy : IsUnit (algebraMap S C y.val)) :=
  letI := coefficientAlgebra (O := 𝒪[K]) C
  ModuleLaw.OrderAction.Iso.rationalSquare (F := K)
    ((baseChangeAlongComparison c f).testIso C b hb x y hx hy)
    (BasicAtlas.OrderAction.baseChangeAlongOrderChartIso Y.order f C y hy)
    (BasicAtlas.OrderAction.baseChangeAlongOrderChartIso X.order f C x hx)
    (originalTestIsoOnRestrictedTest c f C a ha x y hx hy)
    (testIso_baseChangeAlong_square c f C b hb a ha x y hx hy)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
