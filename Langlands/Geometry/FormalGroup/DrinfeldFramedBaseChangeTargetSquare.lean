import Langlands.Geometry.FormalGroup.DrinfeldFramedBaseChangeRefinedSquare
import Langlands.Geometry.FormalGroup.SpecialAtlasComparisonTestRefinement

/-! # Actual refined target square for a framed Nilp-base comparison -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type v} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M₀ M₁ M₂ M₃ M₄ : ModuleLaw O R σ}
variable {N₀ N₁ N₂ N₃ N₄ : ModuleLaw O R τ}
variable {E₀ : OrderAction D M₀} {E₁ : OrderAction D M₁}
variable {E₂ : OrderAction D M₂} {E₃ : OrderAction D M₃} {E₄ : OrderAction D M₄}
variable {G₀ : OrderAction D N₀} {G₁ : OrderAction D N₁}
variable {G₂ : OrderAction D N₂} {G₃ : OrderAction D N₃} {G₄ : OrderAction D N₄}

/-- Paste four specified actual rational squares through their three proved shared maps. -/
def pasteFour (a : CommutingSquare (F := F) E₀ G₀ G₁ E₁)
    (b : CommutingSquare (F := F) E₁ G₁ G₂ E₂)
    (c : CommutingSquare (F := F) E₂ G₂ G₃ E₃)
    (d : CommutingSquare (F := F) E₃ G₃ G₄ E₄)
    (hab : a.bottom = b.top) (hbc : b.bottom = c.top) (hcd : c.bottom = d.top) :
    CommutingSquare (F := F) E₀ G₀ G₄ E₄ :=
  ((a.paste b hab).paste c hbc).paste d hcd

end Langlands.FormalGroup.ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {X : BasicAtlas O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- At its selected parent the inverse original-to-refined correction is the actual refinement chart map. -/
theorem parentOrderTestIso_at_source (q : CoverRefinement X) (E : OrderAction D X)
    (A : CommAlgCat.{v} R) (b : q.opens) (hb : IsUnit (algebraMap R A b.val)) :
    (q.parentOrderTestIso E A (q.source b) (q.source_unit A b hb) b hb).symm =
      q.orderChartIso E A b hb := by
  apply ModuleLaw.OrderAction.Iso.ext_hom
  change (E.transitionIso A (q.source b) (q.source b) _ _).inv.comp
    (q.orderChartIso E A b hb).hom = (q.orderChartIso E A b hb).hom
  rw [BasicAtlas.OrderAction.transitionIso_self]
  exact ModuleLaw.OrderAction.Hom.id_comp _

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas.Comparison

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}
variable {X Y : DrinfeldFramedAtlas Φ A}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The specified actual target comparison extended to the new Nilp base. -/
def baseChangedTargetComparison (c : Comparison X Y) (f : A ⟶ B) :=
  SpecialAtlas.baseChangeAlongComparison c.targetComparison (Nilp.scalarMap 𝒪[K] f)

/-- The actual original reduced finer chart selected by the new comparison chart. -/
def baseChangeOriginalReducedChart (c : Comparison X Y) (f : A ⟶ B)
    (b : (SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)).right.opens) :=
  SpecialAtlas.reductionBaseChangeOriginalChart c.targetComparison f b

/-- Its generator is invertible on the restricted new quotient test. -/
theorem baseChangeOriginalReducedChart_unit (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C)
        (c.baseChangeOriginalReducedChart f b).val) :=
  SpecialAtlas.reductionBaseChangeOriginalChart_unit c.targetComparison f C b hb

/-- The four actual refined target order actions in the new and scalar-transported original tests. -/
abbrev BaseChangeTargetSquare (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :=
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) T
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  let n := SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)
  let o := SpecialAtlas.reductionComparison c.targetComparison
  let a := c.baseChangeOriginalReducedChart f b
  let ha := c.baseChangeOriginalReducedChart_unit f C b hb
  let bl := BasicAtlas.sourceChart (X := n.left.atlas) (Y := n.right.atlas) n.sameCover b
  let al := BasicAtlas.sourceChart (X := o.left.atlas) (Y := o.right.atlas) o.sameCover a
  letI := γ
  ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare (F := K)
    ((n.left.orderChart (X.baseChange f).target.val.reduction.order bl).map
      (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val C hb))
    ((n.right.orderChart (Y.baseChange f).target.val.reduction.order b).map
      (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val C hb))
    ((letI := δ; (o.right.orderChart Y.target.val.reduction.order a).map
      (BasicAtlas.coefficientLift (O := 𝒪[K]) a.val T ha)).reAlgebra γ eC)
    ((letI := δ; (o.left.orderChart X.target.val.reduction.order al).map
      (BasicAtlas.coefficientLift (O := 𝒪[K]) a.val T ha)).reAlgebra γ eC)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Paste actual refined, quotient, supplied-coefficient and transported original refined test squares. -/
def baseChangePastedTargetSquare (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    c.BaseChangeTargetSquare f C b hb :=
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) T
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  let n := SpecialAtlas.reductionComparison (c.baseChangedTargetComparison f)
  let o := SpecialAtlas.reductionComparison c.targetComparison
  let a := c.baseChangeOriginalReducedChart f b
  let ha := c.baseChangeOriginalReducedChart_unit f C b hb
  let bl := BasicAtlas.sourceChart (X := n.left.atlas) (Y := n.right.atlas) n.sameCover b
  let xn := n.left.source bl
  let yn := n.right.source b
  let hxn := n.left.source_unit C bl hb
  let hyn := n.right.source_unit C b hb
  let x := X.baseChangeExtendedChart f xn
  let y := Y.baseChangeExtendedChart f yn
  let xo := X.baseChangeOriginalChart f xn
  let yo := Y.baseChangeOriginalChart f yn
  let hxo := X.baseChangeOriginalChart_unit f C xn hxn
  let hyo := Y.baseChangeOriginalChart_unit f C yn hyn
  let bi := SpecialAtlas.reductionBaseChangeOldImageChart c.targetComparison f b
  let hbi := SpecialAtlas.reductionBaseChangeOldImageChart_unit c.targetComparison f C b hb
  letI := γ
  let sn := (n.refinementTestSquare (F := K) C b hb xn yn hxn hyn).reverse
  let sq := SpecialAtlas.reductionBaseChangeTestSquare c.targetComparison f C b hb x y hxn hyn
  let sc := SpecialAtlas.baseChangeAlongTestSquare o φ C bi hbi a ha x y hxn hyn
  let so := ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.reAlgebra (α := δ)
    (letI := δ; o.refinementTestSquare (F := K) T a ha xo yo hxo hyo) γ eC
  have htop := ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.reAlgebra_top (α := δ)
    (letI := δ; o.refinementTestSquare (F := K) T a ha xo yo hxo hyo) γ eC
  have hso :
      ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.bottom (O := 𝒪[K]) (R := C) sc =
        ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.top (O := 𝒪[K]) (R := C) so :=
    (ModuleLaw.OrderAction.QuasiIsogeny.reAlgebra_ofIso (α := δ) (F := K)
      (letI := δ; o.testIso T a ha xo yo hxo hyo) γ eC).symm.trans htop.symm
  ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.pasteFour sn sq sc so rfl rfl hso

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas.Comparison
