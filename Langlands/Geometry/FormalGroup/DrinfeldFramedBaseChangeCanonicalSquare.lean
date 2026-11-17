import Langlands.Geometry.FormalGroup.DrinfeldFramedBaseChangeFrameComparison

/-! # Chart-independent fixed-frame comparison in the actual base-change square -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.OrderAction.Iso

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]
variable {M N : ModuleLaw O R σ} {E : OrderAction D M} {E' : OrderAction D N}

/-- The actual inverse of an identity-series formal isomorphism has identity series. -/
theorem inv_coordinates_of_hom_id (f : Iso E E')
    (hf : f.hom.val.toHom.toCoordinateMap = CoordinateMap.id) :
    f.inv.val.toHom.toCoordinateMap = CoordinateMap.id := by
  have h := congrArg (fun g => g.val.toHom.toCoordinateMap) f.inv_hom
  change f.inv.val.toHom.toCoordinateMap.comp f.hom.val.toHom.toCoordinateMap = CoordinateMap.id at h
  simpa only [hf, CoordinateMap.comp_id] using h

end Langlands.FormalGroup.ModuleLaw.OrderAction.Iso

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Restricting actual coefficient composition to a cover retains complete identity series. -/
theorem ofGlobalOrderMapCompIso_hom_coordinates (E : ModuleLaw.OrderAction D M)
    {S T : Type v} [CommRing S] [CommRing T] [Algebra O S] [Algebra O T]
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) (a : Set T) (ha : Ideal.span a = ⊤)
    (C : CommAlgCat.{v} T) (b : a) (hb : IsUnit (algebraMap T C b.val)) :
    ((ofGlobalOrderIso (E.mapCompIso f g) a ha).hom.val.hom C b hb).toHom.toCoordinateMap =
      CoordinateMap.id := by
  change (globalChartHom (ModuleLaw.mapCompIso M f g).hom b.val C hb).toHom.toCoordinateMap = _
  rw [globalChartHom_coordinates]
  exact CoordinateMap.map_id _

/-- Retyping equal global covers retains the actual forward identity series on every chart. -/
theorem globalCoverOrderIsoOfCoverEq_hom_coordinates (E : ModuleLaw.OrderAction D M)
    (a b : Set R) (ha : Ideal.span a = ⊤) (hb : Ideal.span b = ⊤) (e : a = b)
    (C : CommAlgCat.{v} R) (c : b) (hc : IsUnit (algebraMap R C c.val)) :
    ((globalCoverOrderIsoOfCoverEq E a b ha hb e).hom.val.hom C c hc).toHom.toCoordinateMap =
      CoordinateMap.id := by
  cases e
  rfl

/-- Scalar retyping of actual global normalization retains complete forward identity series. -/
theorem globalOrderChartIso_reAlgebra_hom_coordinates (E : ModuleLaw.OrderAction D M)
    (a : R) (C : CommAlgCat.{v} R) (ha : IsUnit (algebraMap R C a))
    (β : Algebra O C) (e : coefficientAlgebra (O := O) C = β) :
    (letI := β; ((globalOrderChartIso E a C ha).reAlgebra β e).hom.val.toHom.toCoordinateMap) =
      CoordinateMap.id := by
  cases e
  rfl

namespace OrderAction

variable {X Y Z : BasicAtlas O R σ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Actual atlas-map composition retains chartwise complete identity series. -/
theorem Iso.trans_chart_hom_coordinates_id (f : Iso E E' h) (g : Iso E' E'' k)
    (C : CommAlgCat.{v} R) (b : Z.opens) (hb : IsUnit (algebraMap R C b.val))
    (hf : (f.hom.val.hom C (sourceChart k b) hb).toHom.toCoordinateMap = CoordinateMap.id)
    (hg : (g.hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id) :
    ((f.trans g).hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id := by
  change (g.hom.val.hom C b hb).toHom.toCoordinateMap.comp
    (f.hom.val.hom C (sourceChart k b) hb).toHom.toCoordinateMap = _
  rw [hf, hg]
  exact CoordinateMap.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- The actual scalar-retyped source coefficient-chart map retains identity series. -/
theorem baseChangeReAlgebraSourceOrderChartIso_hom_coordinates (E : OrderAction D X)
    (S : CommAlgCat.{v} R) (h : X.opens = Y.opens)
    (β : Algebra O S) (e : coefficientAlgebra (O := O) S = β)
    (C : CommAlgCat.{v} S) (b : Y.baseOpens S) (hb : IsUnit (algebraMap S C b.val)) :
    (letI := β;
      (baseChangeReAlgebraSourceOrderChartIso E S h β e C b hb).hom.val.toHom.toCoordinateMap) =
      CoordinateMap.id := by
  cases e
  rfl

end OrderAction

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace SpecialAtlas

set_option backward.isDefEq.respectTransparency false in
/-- The actual extended fixed-frame source comparison has complete forward identity series. -/
theorem quotientFrameBaseChangeIso_hom_coordinates (Φ : SpecialModule K D ι κ)
    (ψ : κ →ₐ[𝒪[K]] ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (Y : SpecialAtlas K D ι A.obj) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (Y.baseChangeAlong (Nilp.scalarMap 𝒪[K] f)).reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    ((quotientFrameBaseChangeIso Φ ψ Y f).hom.val.hom C b hb).toHom.toCoordinateMap =
      CoordinateMap.id := by
  unfold quotientFrameBaseChangeIso
  apply BasicAtlas.OrderAction.Iso.trans_chart_hom_coordinates_id
  · exact BasicAtlas.globalCoverBaseAlongIso_hom_coordinates _ _ _ _ _ _ _
  · apply BasicAtlas.OrderAction.Iso.trans_chart_hom_coordinates_id
    · exact BasicAtlas.ofGlobalOrderMapCompIso_hom_coordinates _ _ _ _ _ _ _ _
    · exact BasicAtlas.globalCoverOrderIsoOfCoverEq_hom_coordinates _ _ _ _ _ _ _ _ _

end SpecialAtlas

namespace DrinfeldFramedAtlas

variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := κ) π}

set_option backward.isDefEq.respectTransparency false in
/-- The frame comparison used by the actual base-change framing has complete identity series. -/
theorem baseChangeFrameChartIso_hom_coordinates (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    (X.baseChangeFrameChartIso f C b hb).hom.val.toHom.toCoordinateMap = CoordinateMap.id := by
  unfold baseChangeFrameChartIso
  apply ModuleLaw.OrderAction.Iso.trans_hom_coordinates_id
  · rfl
  · apply ModuleLaw.OrderAction.Iso.trans_hom_coordinates_id
    · apply ModuleLaw.OrderAction.Iso.inv_coordinates_of_hom_id
      exact SpecialAtlas.quotientFrameBaseChangeIso_hom_coordinates _ _ _ _ _ _ _
    · apply ModuleLaw.OrderAction.Iso.trans_hom_coordinates_id
      · exact BasicAtlas.OrderAction.baseChangeReAlgebraSourceOrderChartIso_hom_coordinates _ _ _ _ _ _ _ _
      · exact BasicAtlas.globalOrderChartIso_reAlgebra_hom_coordinates X.globalFrame.order
          (X.baseChangeOriginalChart f b).val
          (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C)
          (X.baseChangeOriginalChart_unit f C b hb) (coefficientAlgebra (O := 𝒪[K]) C)
          (BasicAtlas.coefficientAlgebra_comp_transport
            (BasicAtlas.coefficientTest (Nilp.reducedScalarMap 𝒪[K] f)) C _
            (BasicAtlas.coefficientAlgebraAlong_eq (Nilp.reducedScalarMap 𝒪[K] f)))

set_option backward.isDefEq.respectTransparency false in
/-- The chart-dependent actual comparison is exactly the direct coefficient-map comparison. -/
theorem baseChangeFrameChartIso_eq_global (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    X.baseChangeFrameChartIso f C b hb = X.baseChangeGlobalFrameTestIso f C := by
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  exact (X.baseChangeFrameChartIso_hom_coordinates f C b hb).trans
    (X.baseChangeGlobalFrameTestIso_hom_coordinates f C).symm

/-- The normalized framing square uses the fixed-frame comparison with no chart parameter. -/
theorem chartFraming_baseChange_canonical (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    ((X.baseChange f).chartFraming C b hb).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (X.baseChangeTargetChartIso f C b hb)) =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (X.baseChangeGlobalFrameTestIso f C)).trans
        (X.baseChangeOriginalChartFraming f C b hb) := by
  let _ := coefficientAlgebra (O := 𝒪[K]) C
  have hi := congrArg (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K))
    (X.baseChangeFrameChartIso_eq_global f C b hb)
  exact (X.chartFraming_baseChange f C b hb).trans
    (congrArg (fun q => q.trans (X.baseChangeOriginalChartFraming f C b hb)) hi)

/-- Four actual full-order rational maps with their chart-independent fixed-frame square. -/
def baseChangeCanonicalFramingSquare (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :=
  letI := coefficientAlgebra (O := 𝒪[K]) C
  ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.mk
    ((X.baseChange f).chartFraming C b hb)
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (X.baseChangeTargetChartIso f C b hb))
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (X.baseChangeGlobalFrameTestIso f C))
    (X.baseChangeOriginalChartFraming f C b hb) (X.chartFraming_baseChange_canonical f C b hb)

end DrinfeldFramedAtlas

end Langlands.FormalGroup.LocalDivision
