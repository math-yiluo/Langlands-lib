import Langlands.Geometry.FormalGroup.DrinfeldFramedReducedRefinement
import Langlands.Geometry.FormalGroup.DrinfeldFramedComparisonIdentity
import Langlands.Geometry.FormalGroup.DrinfeldFramedSourceChoice

/-! # Actual composition of specified reduced framing comparisons -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := κ) π}
variable {X Y Z : DrinfeldFramedAtlas Φ A}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The residue-induced identity frame maps compose as actual rational maps. -/
theorem globalFrameQuasiIso_trans (e : X.residueMap = Y.residueMap)
    (f : Y.residueMap = Z.residueMap) :
    ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) (globalFrameIso (e.trans f)) =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (globalFrameIso e)).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (globalFrameIso f)) := by
  cases X
  cases Y
  cases Z
  cases e
  cases f
  exact (ModuleLaw.OrderAction.QuasiIsogeny.refl_trans _).symm

/-- Coefficient extension preserves the composition of the specified frame maps. -/
theorem globalFrameQuasiIso_map_trans (e : X.residueMap = Y.residueMap)
    (f : Y.residueMap = Z.residueMap)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj) :
    ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
        ((globalFrameIso (e.trans f)).map (IsScalarTower.toAlgHom 𝒪[K]
          ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B)) =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
          ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
          ((globalFrameIso f).map (IsScalarTower.toAlgHom 𝒪[K]
            ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))) := by
  have h := congrArg
    (ModuleLaw.OrderAction.QuasiIsogeny.map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
    (globalFrameQuasiIso_trans e f)
  simpa only [ModuleLaw.OrderAction.QuasiIsogeny.map_ofIso,
    ModuleLaw.OrderAction.QuasiIsogeny.map_trans] using h

/-- The joined comparison uses exactly the prescribed middle source-chart map. -/
theorem reducedComparisonOnChart_join
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (d : SpecialAtlas.Comparison Y.target.val.reduction Z.target.val.reduction)
    (h : c.right.opens = d.left.opens)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : d.right.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    reducedComparisonOnChart (c.join d h) B b hb =
      (reducedComparisonOnChart c B
        (BasicAtlas.sourceChart (X := c.right.atlas) (Y := d.left.atlas) h
          (BasicAtlas.sourceChart (X := d.left.atlas) (Y := d.right.atlas) d.sameCover b)) hb).trans
        (((BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
          (c.right.orderSourceIso Y.target.val.reduction.order d.left h)).onChart B
            (BasicAtlas.sourceChart (X := d.left.atlas) (Y := d.right.atlas) d.sameCover b) hb).trans
              (reducedComparisonOnChart d B b hb)) := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  apply ModuleLaw.OrderAction.RationalHom.ext
  let a := BasicAtlas.sourceChart (X := d.left.atlas) (Y := d.right.atlas) d.sameCover b
  let m := BasicAtlas.sourceChart (X := c.right.atlas) (Y := d.left.atlas) h a
  let fl := c.coordinateIso.hom.val.hom B m hb
  let fm := (c.right.orderSourceIso Y.target.val.reduction.order d.left h).hom.val.hom B a hb
  let fr := d.coordinateIso.hom.val.hom B b hb
  have h₁ := ModuleLaw.RationalHom.ofHom_comp (F := K) fr fm
  have h₂ := ModuleLaw.RationalHom.ofHom_comp (F := K) (fr.comp fm) fl
  exact h₂.trans (congrArg (fun k => ModuleLaw.RationalHom.comp k
    (ModuleLaw.RationalHom.ofHom (F := K) fl)) h₁)

/-- Join actual reduced framing squares through their specified middle source choice. -/
theorem ReducedFramingSquare.join
    (e : X.residueMap = Y.residueMap) (f : Y.residueMap = Z.residueMap)
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (d : SpecialAtlas.Comparison Y.target.val.reduction Z.target.val.reduction)
    (h : c.right.opens = d.left.opens)
    (hc : ReducedFramingSquare e c) (hd : ReducedFramingSquare f d) :
    ReducedFramingSquare (e.trans f) (c.join d h) := by
  intro B b hb
  let a := BasicAtlas.sourceChart (X := d.left.atlas) (Y := d.right.atlas) d.sameCover b
  let m := BasicAtlas.sourceChart (X := c.right.atlas) (Y := d.left.atlas) h a
  let x := BasicAtlas.sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover m
  let fl := X.refinedChartFraming c.left B x hb
  let fm := Y.refinedChartFraming c.right B m hb
  let fn := Y.refinedChartFraming d.left B a hb
  let fr := Z.refinedChartFraming d.right B b hb
  let cc := reducedComparisonOnChart c B m hb
  let mid := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
    (c.right.orderSourceIso Y.target.val.reduction.order d.left h)).onChart B a hb
  let dd := reducedComparisonOnChart d B b hb
  let fi := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
  let fj := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    ((globalFrameIso f).map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
  have hcc : fl.trans cc = fi.trans fm := hc B m hb
  have hm : fm.trans mid = fn :=
    Y.refinedChartFraming_sourceIso c.right d.left h B a hb
  have hdd : fn.trans dd = fj.trans fr := hd B b hb
  have hmdd : fm.trans (mid.trans dd) = fj.trans fr :=
    (ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc fm mid dd).symm.trans
      ((congrArg (fun k => k.trans dd) hm).trans hdd)
  have hp := ModuleLaw.OrderAction.QuasiIsogeny.square_paste
    fl cc fi fm (mid.trans dd) fj fr hcc hmdd
  exact (congrArg (fun k => fl.trans k)
    (reducedComparisonOnChart_join c d h B b hb)).trans
      (hp.trans (congrArg (fun k => k.trans fr)
        (globalFrameQuasiIso_map_trans e f B)).symm)

/-- Product-cover composition preserves the specified actual reduced framing square. -/
theorem ReducedFramingSquare.trans
    (e : X.residueMap = Y.residueMap) (f : Y.residueMap = Z.residueMap)
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (d : SpecialAtlas.Comparison Y.target.val.reduction Z.target.val.reduction)
    (hc : ReducedFramingSquare e c) (hd : ReducedFramingSquare f d) :
    ReducedFramingSquare (e.trans f) (c.trans d) :=
  ReducedFramingSquare.join e f
    (c.refine (BasicAtlas.commonLeft c.left.atlas d.left.atlas))
    (d.refine (BasicAtlas.commonRight c.left.atlas d.left.atlas)) rfl
    (ReducedFramingSquare.refine e c hc (BasicAtlas.commonLeft c.left.atlas d.left.atlas))
    (ReducedFramingSquare.refine f d hd (BasicAtlas.commonRight c.left.atlas d.left.atlas))

/-- The actual commuting square for the specified product-cover composite. -/
def composedReducedFramingSquare
    (e : X.residueMap = Y.residueMap) (f : Y.residueMap = Z.residueMap)
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (d : SpecialAtlas.Comparison Y.target.val.reduction Z.target.val.reduction)
    (hc : ReducedFramingSquare e c) (hd : ReducedFramingSquare f d)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : (c.trans d).right.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare (F := K)
      (X.globalFrame.order.map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
      (((c.trans d).left.orderChart X.target.val.reduction.order
        (BasicAtlas.sourceChart (X := (c.trans d).left.atlas) (Y := (c.trans d).right.atlas)
          (c.trans d).sameCover b)).map
            (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb))
      (((c.trans d).right.orderChart Z.target.val.reduction.order b).map
        (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb))
      (Z.globalFrame.order.map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B)) where
  top := X.refinedChartFraming (c.trans d).left B
    (BasicAtlas.sourceChart (X := (c.trans d).left.atlas) (Y := (c.trans d).right.atlas)
      (c.trans d).sameCover b) hb
  right := reducedComparisonOnChart (c.trans d) B b hb
  left := ModuleLaw.OrderAction.QuasiIsogeny.ofIso
    ((globalFrameIso (e.trans f)).map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
  bottom := Z.refinedChartFraming (c.trans d).right B b hb
  commutes := ReducedFramingSquare.trans e f c d hc hd B b hb

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
