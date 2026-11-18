import Langlands.Geometry.FormalGroup.DrinfeldFramedFrameAutomorphism

/-! # Original framed comparisons under integral fixed-frame automorphisms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : ModuleLaw.OrderAction D M} {E' : ModuleLaw.OrderAction D N}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Normalizing an actual restricted global map retains the original coefficient-extended formal map. -/
theorem globalOrderChartIso_natural (f : ModuleLaw.OrderAction.Iso E E')
    (t : Set R) (ht : Ideal.span t = ⊤) (C : CommAlgCat.{v} R)
    (b : t) (hb : IsUnit (algebraMap R C b.val)) :
    (globalOrderChartIso E b.val C hb).symm.trans ((ofGlobalOrderIso f t ht).onChart C b hb) =
      (f.map (IsScalarTower.toAlgHom O R C)).trans (globalOrderChartIso E' b.val C hb).symm := by
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (globalChartHom f.hom.val b.val C hb).toHom.toCoordinateMap.comp CoordinateMap.id =
    CoordinateMap.id.comp ((f.map (IsScalarTower.toAlgHom O R C)).hom.val.toHom.toCoordinateMap)
  rw [globalChartHom_coordinates, CoordinateMap.comp_id, CoordinateMap.id_comp]
  rfl

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v,u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}
variable {X Y : DrinfeldFramedAtlas Φ A}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual integral frame automorphism on a specified quotient coefficient test. -/
def frameAutomorphismTestIso (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (X : DrinfeldFramedAtlas Φ A)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj) :=
  (a.toIso.map X.residueMap).map (IsScalarTower.toAlgHom 𝒪[K]
    ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C)

/-- Inverse precomposition gives the specified whole normalized original-chart framing. -/
theorem chartFraming_frameAct (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (X : DrinfeldFramedAtlas Φ A)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : X.target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C b.val)) :
    (frameAct a X).chartFraming C b hb =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) (frameAutomorphismTestIso a X C)).symm.trans
        (X.chartFraming C b hb) := by
  let gi := BasicAtlas.globalOrderChartIso X.globalFrame.order b.val C hb
  let g := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) gi
  let ai := (X.frameAutomorphismIso a).symm.onChart C b hb
  let q := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) ai
  let n := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) (frameAutomorphismTestIso a X C)
  have hi : gi.symm.trans ai = (frameAutomorphismTestIso a X C).symm.trans gi.symm :=
    BasicAtlas.globalOrderChartIso_natural (a.toIso.map X.residueMap).symm
      X.target.val.reduction.atlas.opens X.target.val.reduction.atlas.covers C b hb
  have hq : g.symm.trans q = n.symm.trans g.symm := by
    have hh := congrArg (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)) hi
    simpa only [ModuleLaw.OrderAction.QuasiIsogeny.ofIso_trans,
      ModuleLaw.OrderAction.QuasiIsogeny.ofIso_symm] using hh
  have hr : (frameAct a X).rho.onChart C b hb = q.trans (X.rho.onChart C b hb) := by
    exact BasicAtlas.OrderAction.QuasiIsogeny.onChart_trans
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) (X.frameAutomorphismIso a)).symm X.rho C b hb
  change g.symm.trans ((frameAct a X).rho.onChart C b hb) =
    n.symm.trans (g.symm.trans (X.rho.onChart C b hb))
  exact (congrArg (fun j => g.symm.trans j) hr).trans
    ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc g.symm q _).symm.trans
      ((congrArg (fun j => j.trans (X.rho.onChart C b hb)) hq).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc _ _ _)))

/-- Inverse precomposition gives the same normalized framing equation on any original refinement. -/
theorem refinedChartFraming_frameAct (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (X : DrinfeldFramedAtlas Φ A) (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : q.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C b.val)) :
    (frameAct a X).refinedChartFraming q C b hb =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) (frameAutomorphismTestIso a X C)).symm.trans
        (X.refinedChartFraming q C b hb) := by
  rw [refinedChartFraming_eq_chartFraming, chartFraming_frameAct]
  exact ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc _ _ _

/-- The source automorphisms commute with the exact residue-forced integral frame comparison. -/
theorem frameAutomorphismTestIso_residue_square (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (e : X.residueMap = Y.residueMap)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj) :
    (frameAutomorphismTestIso a X C).symm.trans
        ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
          ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C)) =
      ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C)).trans
          (frameAutomorphismTestIso a Y C).symm := by
  cases X
  cases Y
  cases e
  apply ModuleLaw.OrderAction.Iso.ext_hom
  change ((ModuleLaw.OrderAction.Hom.id _).map _).comp ((a.toIso.map _).map _).inv =
    ((a.toIso.map _).map _).inv.comp ((ModuleLaw.OrderAction.Hom.id _).map _)
  rw [ModuleLaw.OrderAction.Hom.map_id, ModuleLaw.OrderAction.Hom.id_comp,
    ModuleLaw.OrderAction.Hom.comp_id]

/-- The specified original all-test framing square survives inverse precomposition. -/
theorem FramingSquare.frameAct (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    {e : X.residueMap = Y.residueMap} {c : SpecialAtlas.Comparison X.target.val Y.target.val}
    (hc : FramingSquare e c) : FramingSquare (X := frameAct a X) (Y := frameAct a Y) e c := by
  intro C b hb
  let d := SpecialAtlas.reductionComparison c
  let bl := BasicAtlas.sourceChart (X := d.left.atlas) (Y := d.right.atlas) d.sameCover b
  let fx := X.refinedChartFraming d.left C bl hb
  let fy := Y.refinedChartFraming d.right C b hb
  let t := reducedComparisonOnChart d C b hb
  let nx := (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) (frameAutomorphismTestIso a X C)).symm
  let ny := (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) (frameAutomorphismTestIso a Y C)).symm
  let fi := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
    ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C))
  have hx := refinedChartFraming_frameAct a X d.left C bl hb
  have hy := refinedChartFraming_frameAct a Y d.right C b hb
  have ho : fx.trans t = fi.trans fy := hc C b hb
  have hi : nx.trans fi = fi.trans ny := by
    have hh := congrArg (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K))
      (frameAutomorphismTestIso_residue_square a e C)
    simpa only [ModuleLaw.OrderAction.QuasiIsogeny.ofIso_trans,
      ModuleLaw.OrderAction.QuasiIsogeny.ofIso_symm] using hh
  change ((DrinfeldFramedAtlas.frameAct a X).refinedChartFraming d.left C bl hb).trans t =
    fi.trans ((DrinfeldFramedAtlas.frameAct a Y).refinedChartFraming d.right C b hb)
  exact (congrArg (fun j => j.trans t) hx).trans
    ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc nx fx t).trans
      ((congrArg (fun j => nx.trans j) ho).trans
        ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc nx fi fy).symm.trans
          ((congrArg (fun j => j.trans fy) hi).trans
            ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc fi ny fy).trans
              (congrArg (fun j => fi.trans j) hy.symm))))))

/-- Retain the exact original target comparison and residue equality under the frame action. -/
def Comparison.frameAct (c : Comparison X Y) (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) :
    Comparison (DrinfeldFramedAtlas.frameAct a X) (DrinfeldFramedAtlas.frameAct a Y) where
  targetComparison := c.targetComparison
  residue_eq := c.residue_eq
  square := c.square.frameAct a

@[simp]
theorem Comparison.frameAct_targetComparison (c : Comparison X Y)
    (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) :
    (c.frameAct a).targetComparison = c.targetComparison := rfl

namespace ComparisonClass

/-- Inverse precomposition descends through the same original framed comparison quotient. -/
def frameAct (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) : ComparisonClass Φ A → ComparisonClass Φ A :=
  lift (fun X => comparisonClassOf (DrinfeldFramedAtlas.frameAct a X))
    (fun c => comparisonClassOf_eq_of_comparison (c.frameAct a))

@[simp]
theorem frameAct_comparisonClassOf (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (X : DrinfeldFramedAtlas Φ A) :
    frameAct a (comparisonClassOf X) = comparisonClassOf (DrinfeldFramedAtlas.frameAct a X) := rfl

/-- The actual integral identity fixes the original framed comparison class. -/
@[simp]
theorem frameAct_one (q : ComparisonClass Φ A) : frameAct 1 q = q := by
  refine Quotient.inductionOn q ?_
  intro X
  exact congrArg comparisonClassOf (DrinfeldFramedAtlas.frameAct_one X)

/-- The original quotient retains the actual left multiplication law. -/
theorem frameAct_mul (a b : ModuleLaw.OrderAction.Automorphism Φ.val.order) (q : ComparisonClass Φ A) :
    frameAct (a * b) q = frameAct a (frameAct b q) := by
  refine Quotient.inductionOn q ?_
  intro X
  exact congrArg comparisonClassOf (DrinfeldFramedAtlas.frameAct_mul a b X)

/-- The actual integral full-order frame automorphism group acts on the same original framed quotient. -/
instance frameAutomorphismMulAction :
    MulAction (ModuleLaw.OrderAction.Automorphism Φ.val.order) (ComparisonClass Φ A) where
  smul := frameAct
  one_smul := frameAct_one
  mul_smul := frameAct_mul

@[simp]
theorem frameAct_residueMap (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) (q : ComparisonClass Φ A) :
    (frameAct a q).residueMap = q.residueMap := by
  refine Quotient.inductionOn q ?_
  intro X
  rfl

@[simp]
theorem frameAct_targetClass (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) (q : ComparisonClass Φ A) :
    (frameAct a q).targetClass = q.targetClass := by
  refine Quotient.inductionOn q ?_
  intro X
  rfl

@[simp]
theorem frameAct_reducedTargetClass (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) (q : ComparisonClass Φ A) :
    (frameAct a q).reducedTargetClass = q.reducedTargetClass := by
  refine Quotient.inductionOn q ?_
  intro X
  rfl

end ComparisonClass

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
