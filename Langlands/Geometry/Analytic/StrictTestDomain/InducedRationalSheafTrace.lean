import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalDirectImage
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCoveringTrace
import Langlands.Sheaf.Equivariant.CoveringTrace

/-! # Full coefficient sheaf trace on actual induced rational spectra -/

noncomputable section

universe u v r w t

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory TopologicalSpace Opposite Topology
open Langlands.Sheaf.Equivariant Langlands.LocallyConstantCovering
open scoped BigOperators

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

namespace OpenSubgroupTransport.SheafVariation

section Congruence

variable {G : Type v} [Group G]
  {S T : Type t} [TopologicalSpace S] [TopologicalSpace T]
  [MulAction G S] [MulAction G T]
  [ContinuousConstSMul G S] [ContinuousConstSMul G T]
  {p q : C(S, T)}
  (hp : ∀ (g : G) (x : S), p (g • x) = g • p x)
  (hq : ∀ (g : G) (x : S), q (g • x) = g • q x)
  {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

omit [ContinuousConstSMul G S] [ContinuousConstSMul G T] in
/-- Equality of spatial maps gives the actual full direct-image comparison. -/
private theorem traceDirectImage_congr (h : p = q) :
    DirectImage.sheaf p hp (ModuleCat.{max t w} R) =
      DirectImage.sheaf q hq (ModuleCat.{max t w} R) := by
  subst q
  rfl

/-- Trace is unchanged by equality of the original continuous maps. -/
private theorem trace_congr [∀ y, Finite (p ⁻¹' {y})] [∀ y, Finite (q ⁻¹' {y})]
    (h : p = q) (hpc : IsCoveringMap p) (hqc : IsCoveringMap q)
    (τ : Representation R G M) :
    DirectImage.coefficientTrace p hp hpc τ =
      (eqToIso (traceDirectImage_congr (R := R) hp hq h)).hom.app
          (LocallyConstantSheaf.sheaf (X := S) τ) ≫
        DirectImage.coefficientTrace q hq hqc τ := by
  subst q
  simp

end Congruence

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {X Y Z : ρ.OpenSubgroupTransport}
  {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- Unnormalized trace along the original rational transport map on every open. -/
def coefficientTrace (f : X ⟶ Y) [∀ y, Finite (f.inducedMap ⁻¹' {y})]
    (hf : IsCoveringMap f.inducedMap) (τ : Representation R G M) :
    (directImage (ModuleCat.{max (max u v) w} R) f).obj
        (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) ⟶
      LocallyConstantSheaf.sheaf (X := Y.InducedSpectrum) τ :=
  DirectImage.coefficientTrace f.inducedMap f.inducedMap_smul hf τ

/-- Each original inverse-image-open section is traced by its actual fiber sum. -/
@[simp]
theorem coefficientTrace_apply (f : X ⟶ Y) [∀ y, Finite (f.inducedMap ⁻¹' {y})]
    (hf : IsCoveringMap f.inducedMap) (τ : Representation R G M)
    (U : ActionOpens G Y.InducedSpectrum)
    (s : LocallyConstant ((preimage f).obj U).openSet M) (y : U.openSet) :
    LocallyConstant.toFun (((coefficientTrace f hf τ).hom.app (op U)).hom s) y =
      fiberSum (DirectImage.pointMap f.inducedMap f.inducedMap_smul U) s y := rfl

/-- The sum contains every original quotient point in the entire original fiber. -/
theorem coefficientTrace_apply_sum (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})]
    (hf : IsCoveringMap f.inducedMap) (τ : Representation R G M)
    (U : ActionOpens G Y.InducedSpectrum)
    (s : LocallyConstant ((preimage f).obj U).openSet M)
    (y : U.openSet) [Fintype (f.inducedMap ⁻¹' {y.val})] :
    LocallyConstant.toFun (((coefficientTrace f hf τ).hom.app (op U)).hom s) y =
      ∑ x : f.inducedMap ⁻¹' {y.val}, s ⟨x.val, by
        change f.inducedMap x.val ∈ U.openSet
        rw [show f.inducedMap x.val = y.val from x.property]
        exact y.property⟩ :=
  DirectImage.coefficientTrace_apply_sum f.inducedMap f.inducedMap_smul hf τ U s y

/-- Pullback followed by trace has the cardinality of the original rational fiber. -/
theorem coefficientTrace_pullback_apply (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})]
    (hf : IsCoveringMap f.inducedMap) (τ : Representation R G M)
    (U : ActionOpens G Y.InducedSpectrum)
    (s : LocallyConstant U.openSet M) (y : U.openSet) :
    LocallyConstant.toFun
        (((coefficientMap f τ ≫ coefficientTrace f hf τ).hom.app (op U)).hom s) y =
      Nat.card (f.inducedMap ⁻¹' {y.val}) • s y :=
  DirectImage.coefficientTrace_pullback_apply f.inducedMap f.inducedMap_smul hf τ U s y

/-- The degree formula evaluates at the actual inverse-label rational image. -/
theorem coefficientTrace_pullback_mk_apply (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})]
    (hf : IsCoveringMap f.inducedMap) (τ : Representation R G M)
    (U : ActionOpens G Y.InducedSpectrum) (s : LocallyConstant U.openSet M)
    (a : G) (x : X.LocalSpectrum)
    (hy : Y.inducedMk (a * f.label⁻¹) (f.localSpectrumMap x) ∈ U.openSet) :
    LocallyConstant.toFun
        (((coefficientMap f τ ≫ coefficientTrace f hf τ).hom.app (op U)).hom s)
        ⟨Y.inducedMk (a * f.label⁻¹) (f.localSpectrumMap x), hy⟩ =
      Nat.card (f.inducedMap ⁻¹'
        {Y.inducedMk (a * f.label⁻¹) (f.localSpectrumMap x)}) •
          s ⟨Y.inducedMk (a * f.label⁻¹) (f.localSpectrumMap x), hy⟩ :=
  coefficientTrace_pullback_apply f hf τ U s _

/-- Trace retains all original representations and all coefficient intertwiners. -/
def coefficientTraceNatTrans (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] (hf : IsCoveringMap f.inducedMap) :
    coefficientFunctor X R ⋙
        directImage (ModuleCat.{max (max u v) w} R) f ⟶
      coefficientFunctor Y R :=
  DirectImage.coefficientTraceNatTrans f.inducedMap f.inducedMap_smul hf

@[simp]
theorem coefficientTraceNatTrans_app (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] (hf : IsCoveringMap f.inducedMap)
    (N : Rep.{w} R G) :
    (coefficientTraceNatTrans (R := R) f hf).app N = coefficientTrace f hf N.ρ := rfl

/-- The naturality square uses the original pointwise coefficient maps. -/
@[reassoc]
theorem coefficientTrace_naturality (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] (hf : IsCoveringMap f.inducedMap)
    {N N' : Rep.{w} R G} (a : N ⟶ N') :
    (directImage (ModuleCat.{max (max u v) w} R) f).map
        ((coefficientFunctor X R).map a) ≫ coefficientTrace f hf N'.ρ =
      coefficientTrace f hf N.ρ ≫ (coefficientFunctor Y R).map a :=
  (coefficientTraceNatTrans f hf).naturality a

section Identity

local instance finite_identityFiber :
    ∀ x : X.InducedSpectrum, Finite ((𝟙 X : X ⟶ X).inducedMap ⁻¹' {x}) :=
  Hom.finite_inducedMap_id_fiber X

/-- Identity trace is exactly the existing rational direct-image comparison. -/
@[simp]
theorem coefficientTrace_id (τ : Representation R G M) :
    coefficientTrace (𝟙 X) (Hom.isCoveringMap_inducedMap_id X) τ =
      (directImageIdIso (ModuleCat.{max (max u v) w} R) X).hom.app
        (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) := by
  let : ∀ x : X.InducedSpectrum, Finite ((ContinuousMap.id X.InducedSpectrum) ⁻¹' {x}) :=
    finite_id_fiber
  exact (trace_congr (Hom.inducedMap_smul (𝟙 X))
    (fun (_ : G) (_ : X.InducedSpectrum) => rfl) (inducedMap_id_eq X)
    (Hom.isCoveringMap_inducedMap_id X) isCoveringMap_id τ).trans
      ((congrArg (fun k =>
        (directImageIdIso (ModuleCat.{max (max u v) w} R) X).hom.app
          (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) ≫ k)
        (DirectImage.coefficientTrace_id τ)).trans (Category.comp_id _))

/-- The identity comparison retains the entire original coefficient category. -/
@[simp]
theorem coefficientTraceNatTrans_id :
    coefficientTraceNatTrans (R := R) (𝟙 X)
        (Hom.isCoveringMap_inducedMap_id X) =
      Functor.whiskerLeft (coefficientFunctor X R)
        (directImageIdIso (ModuleCat.{max (max u v) w} R) X).hom := by
  apply NatTrans.ext
  funext N
  exact coefficientTrace_id N.ρ

end Identity

set_option maxHeartbeats 800000 in
/-- Trace composition uses the actual full rational direct-image comparison. -/
theorem coefficientTrace_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] [∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [∀ z, Finite ((f ≫ g).inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hfg : IsCoveringMap (f ≫ g).inducedMap) (τ : Representation R G M) :
    coefficientTrace (f ≫ g) hfg τ =
      (directImageCompIso (ModuleCat.{max (max u v) w} R) f g).hom.app
          (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) ≫
        (directImage (ModuleCat.{max (max u v) w} R) g).map (coefficientTrace f hf τ) ≫
          coefficientTrace g hg τ := by
  let : ∀ z, Finite ((g.inducedMap.comp f.inducedMap) ⁻¹' {z}) :=
    finite_comp_fiber f.inducedMap g.inducedMap
  have hc : IsCoveringMap (g.inducedMap.comp f.inducedMap) := by
    rw [← inducedMap_comp_eq f g]
    exact hfg
  exact (trace_congr (Hom.inducedMap_smul (f ≫ g))
    (fun k x => by
      change g.inducedMap (f.inducedMap (k • x)) = k • g.inducedMap (f.inducedMap x)
      rw [f.inducedMap_smul, g.inducedMap_smul])
    (inducedMap_comp_eq f g) hfg hc τ).trans
      (congrArg (fun k =>
        (directImageCompIso (ModuleCat.{max (max u v) w} R) f g).hom.app
          (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) ≫ k)
        (DirectImage.coefficientTrace_comp f.inducedMap f.inducedMap_smul
          g.inducedMap g.inducedMap_smul hf hg hc τ))

/-- Composite traces are natural in every original rational coefficient. -/
theorem coefficientTraceNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] [∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [∀ z, Finite ((f ≫ g).inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hfg : IsCoveringMap (f ≫ g).inducedMap) :
    coefficientTraceNatTrans (R := R) (f ≫ g) hfg =
      Functor.whiskerLeft (coefficientFunctor X R)
          (directImageCompIso (ModuleCat.{max (max u v) w} R) f g).hom ≫
        Functor.whiskerRight (coefficientTraceNatTrans f hf)
          (directImage (ModuleCat.{max (max u v) w} R) g) ≫
            coefficientTraceNatTrans g hg := by
  apply NatTrans.ext
  funext N
  exact coefficientTrace_comp f g hf hg hfg N.ρ

end OpenSubgroupTransport.SheafVariation

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
