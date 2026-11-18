import Langlands.Geometry.FormalGroup.DrinfeldFramedIdentityRho
import Langlands.Geometry.FormalGroup.SpecialAtlasInducedComparison

/-! # Original framed comparison for identity Nilp-base extension -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {X Y : BasicAtlas O R σ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual map from extension by a proved identity retains complete identity chart series. -/
theorem identityAlongIso_hom_coordinates (E : OrderAction D X) {m : R →ₐ[O] R}
    (hm : m = AlgHom.id O R) (C : CommAlgCat.{v} R)
    (b : X.opens) (hb : IsUnit (algebraMap R C b.val)) :
    ((E.identityAlongIso hm).hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id := by
  cases hm
  change CoordinateMap.id.comp CoordinateMap.id = CoordinateMap.id
  exact CoordinateMap.id_comp _

/-- The actual inverse atlas map retains identity series if its specified forward chart maps do. -/
theorem Iso.symm_hom_coordinates_id (f : Iso E E' h)
    (hf : ∀ (C : CommAlgCat.{v} R) (b : Y.opens)
      (hb : IsUnit (algebraMap R C b.val)),
      (f.hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id)
    (C : CommAlgCat.{v} R) (b : X.opens) (hb : IsUnit (algebraMap R C b.val)) :
    (f.symm.hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id := by
  have hh := Iso.onChart_symm f C b hb
  exact (congrArg (fun z => z.hom.val.toHom.toCoordinateMap) hh).trans
    (ModuleLaw.OrderAction.Iso.inv_coordinates_of_hom_id _
      (hf C (sourceChart (X := Y) (Y := X) h.symm b) hb))

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}
variable {X Y : DrinfeldFramedAtlas Φ A}

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option backward.isDefEq.respectTransparency false in
/-- The specified source map for identity Nilp-base extension has complete identity formal series. -/
theorem baseChangeIdentitySourceIso_hom_coordinates (X : DrinfeldFramedAtlas Φ A)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : X.source.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C b.val)) :
    (X.baseChangeIdentitySourceIso.hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id := by
  unfold baseChangeIdentitySourceIso
  apply BasicAtlas.OrderAction.Iso.trans_chart_hom_coordinates_id
  · apply BasicAtlas.OrderAction.Iso.symm_hom_coordinates_id
    exact SpecialAtlas.quotientFrameBaseChangeIso_hom_coordinates Φ.val X.residueMap X.target.val (𝟙 A)
  · exact BasicAtlas.OrderAction.identityAlongIso_hom_coordinates _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- A whole framing tensor square with identity-series source maps gives the normalized chart square. -/
theorem chartFraming_of_global_square (e : X.residueMap = Y.residueMap)
    {h : X.target.val.reduction.atlas.opens = Y.target.val.reduction.atlas.opens}
    (t : X.target.val.reduction.Iso Y.target.val.reduction h)
    (s : BasicAtlas.OrderAction.Iso X.source.order Y.source.order h)
    (hs : ∀ (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
      (b : Y.source.atlas.opens)
      (hb : IsUnit (algebraMap
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C b.val)),
      (s.hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id)
    (hr : X.rho.trans (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) t) =
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) s).trans Y.rho)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : Y.target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C b.val)) :
    (X.chartFraming C (BasicAtlas.sourceChart h b) hb).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (t.onChart C b hb)) =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
          ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C))).trans
        (Y.chartFraming C b hb) := by
  let gx := BasicAtlas.globalOrderChartIso X.globalFrame.order b.val C hb
  let gy := BasicAtlas.globalOrderChartIso Y.globalFrame.order b.val C hb
  let fi := (globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
    ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C)
  have hfi : fi.trans gy.symm = gx.symm.trans (s.onChart C b hb) := by
    apply ModuleLaw.OrderAction.Iso.ext_hom
    apply Subtype.ext
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp fi.hom.val.toHom.toCoordinateMap =
      (s.hom.val.hom C b hb).toHom.toCoordinateMap.comp CoordinateMap.id
    rw [hs C b hb]
    have hh := globalFrameIso_map_hom_coordinates e C
    change fi.hom.val.toHom.toCoordinateMap = CoordinateMap.id at hh
    rw [hh]
  let fx := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) gx
  let fy := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) gy
  let n := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) fi
  let sq := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) (s.onChart C b hb)
  let tq := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) (t.onChart C b hb)
  let rx := X.rho.onChart C (BasicAtlas.sourceChart h b) hb
  let ry := Y.rho.onChart C b hb
  have hf : n.trans fy.symm = fx.symm.trans sq := by
    have hh := congrArg (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)) hfi
    simpa only [ModuleLaw.OrderAction.QuasiIsogeny.ofIso_trans,
      ModuleLaw.OrderAction.QuasiIsogeny.ofIso_symm] using hh
  have hh := congrArg (fun q => q.onChart C b hb) hr
  simp only [BasicAtlas.OrderAction.QuasiIsogeny.onChart_trans] at hh
  have ht : rx.trans tq = sq.trans ry := hh
  change (fx.symm.trans rx).trans tq = n.trans (fy.symm.trans ry)
  exact (ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc _ _ _).trans
    ((congrArg (fun q => fx.symm.trans q) ht).trans
      ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc _ _ _).symm.trans
        ((congrArg (fun q => q.trans ry) hf.symm).trans
          (ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc _ _ _))))

set_option backward.isDefEq.respectTransparency false in
/-- A specified inducing reduced-target comparison inherits the normalized framing square. -/
theorem ReducedFramingSquare.of_induced_global_square (e : X.residueMap = Y.residueMap)
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    {h : X.target.val.reduction.atlas.opens = Y.target.val.reduction.atlas.opens}
    (t : X.target.val.reduction.Iso Y.target.val.reduction h)
    (s : BasicAtlas.OrderAction.Iso X.source.order Y.source.order h)
    (hc : c.InducedBy t)
    (hs : ∀ (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
      (b : Y.source.atlas.opens)
      (hb : IsUnit (algebraMap
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C b.val)),
      (s.hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id)
    (hr : X.rho.trans (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) t) =
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) s).trans Y.rho) :
    ReducedFramingSquare e c := by
  intro C b hb
  let a := BasicAtlas.sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b
  let y := c.right.source b
  let hy := c.right.source_unit C b hb
  let x := BasicAtlas.sourceChart h y
  let ll := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (c.left.parentOrderTestIso X.target.val.reduction.order C x hy a hb)
  let rr := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    (c.right.parentOrderTestIso Y.target.val.reduction.order C y hy b hb)
  let tq := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) (t.onChart C y hy)
  let cc := reducedComparisonOnChart c C b hb
  let n := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C))
  let fx := X.chartFraming C x hy
  let fy := Y.chartFraming C y hy
  have hfx : fx.trans ll = X.refinedChartFraming c.left C a hb :=
    X.chartFraming_originalRefinedTargetTestIso C x hy c.left a hb
  have hfy : fy.trans rr = Y.refinedChartFraming c.right C b hb :=
    Y.chartFraming_originalRefinedTargetTestIso C y hy c.right b hb
  have hchart : fx.trans tq = n.trans fy :=
    chartFraming_of_global_square e t s hs hr C y hy
  have hi := hc C b hb x y hy hy
  change c.testIso C b hb x y hy hy =
    (X.target.val.reduction.order.transitionIso C x x hy hy).trans (t.onChart C y hy) at hi
  rw [BasicAtlas.OrderAction.transitionIso_self] at hi
  have hu : (ModuleLaw.OrderAction.Iso.refl _).trans (t.onChart C y hy) =
      t.onChart C y hy := by
    apply ModuleLaw.OrderAction.Iso.ext_hom
    exact ModuleLaw.OrderAction.Hom.comp_id _
  have hqi := congrArg (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)) (hi.trans hu)
  have htest := (c.refinementTestSquare (F := K) C b hb x y hy hy).commutes
  have ht : tq.trans rr = ll.trans cc :=
    (congrArg (fun z => z.trans rr) hqi).symm.trans htest
  change (X.refinedChartFraming c.left C a hb).trans cc =
    n.trans (Y.refinedChartFraming c.right C b hb)
  exact (congrArg (fun z => z.trans cc) hfx.symm).trans
    ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc fx ll cc).trans
      ((congrArg (fun z => fx.trans z) ht.symm).trans
        ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc fx tq rr).symm.trans
          ((congrArg (fun z => z.trans rr) hchart).trans
            ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc n fy rr).trans
              (congrArg (fun z => n.trans z) hfy))))))

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Identity Nilp extension compares in the original framed relation, retaining the specified target map. -/
def baseChangeIdentityComparison (X : DrinfeldFramedAtlas Φ A) :
    Comparison (X.baseChange (𝟙 A)) X where
  targetComparison := X.target.val.baseIdComparison
  residue_eq := X.baseChange_id_residueMap
  square := ReducedFramingSquare.of_induced_global_square X.baseChange_id_residueMap
    (SpecialAtlas.reductionComparison X.target.val.baseIdComparison)
    X.baseChangeIdentityReducedTargetIso X.baseChangeIdentitySourceIso
    (SpecialAtlas.inducedBy_reduction X.target.val.baseIdComparison X.target.val.baseIdIso
      X.target.val.baseIdComparison_inducedBy)
    X.baseChangeIdentitySourceIso_hom_coordinates X.baseChangeIdentity_rho

/-- The original identity-base target comparison is retained exactly. -/
@[simp]
theorem baseChangeIdentityComparison_targetComparison (X : DrinfeldFramedAtlas Φ A) :
    X.baseChangeIdentityComparison.targetComparison = X.target.val.baseIdComparison := rfl

/-- The actual original framed comparison proves the identity law for representative classes. -/
theorem comparisonClassOf_baseChange_id (X : DrinfeldFramedAtlas Φ A) :
    comparisonClassOf (X.baseChange (𝟙 A)) = comparisonClassOf X :=
  comparisonClassOf_eq_of_comparison X.baseChangeIdentityComparison

namespace ComparisonClass

/-- Identity Nilp-base extension is the identity on the original framed comparison quotient. -/
@[simp]
theorem baseChange_id (q : ComparisonClass Φ A) : q.baseChange (𝟙 A) = q := by
  refine Quotient.inductionOn q ?_
  exact comparisonClassOf_baseChange_id

end ComparisonClass

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
