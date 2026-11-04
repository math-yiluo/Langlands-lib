import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSheafTrace
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothSpatialSheaves
import Langlands.Sheaf.Equivariant.SmoothDirectImage.CoveringTrace

/-! # Smooth coefficient sheaf trace on actual induced rational spectra -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory TopologicalSpace Opposite Topology
open Langlands.Sheaf.Equivariant Langlands.LocallyConstantCovering
open scoped BigOperators

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

namespace OpenSubgroupTransport.SmoothSheafVariation

section Congruence

variable {R G S T : Type u} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace S] [TopologicalSpace T] [MulAction G S] [MulAction G T]
  [ContinuousConstSMul G S] [ContinuousConstSMul G T]
  [HasStableNeighbourhoods G S] [HasStableNeighbourhoods G T]
  {p q : C(S, T)}
  (hp : ∀ (g : G) (x : S), p (g • x) = g • p x)
  (hq : ∀ (g : G) (x : S), q (g • x) = g • q x)

omit [ContinuousConstSMul G S] [HasStableNeighbourhoods G S] in
/-- Equality of actual continuous maps identifies their smooth direct images. -/
private theorem directImage_congr (h : p = q) :
    SmoothDirectImage.functor (R := R) p hp = SmoothDirectImage.functor q hq := by
  subst q
  rfl

/-- Transport smooth identity pullback by equality of the actual identity map. -/
private theorem coefficientMap_id_congr {q : C(S, S)}
    (hq : ∀ (k : G) (x : S), q (k • x) = k • q x)
    (h : q = ContinuousMap.id S)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    SmoothDirectImage.coefficientMap q hq M =
      (SmoothDirectImage.idIso ≪≫
        (eqToIso (directImage_congr (R := R) hq
          (fun (_ : G) (_ : S) => rfl) h)).symm).hom.app
            ((LocallyConstantSheaf.smoothFunctor R G S).obj M) := by
  subst q
  simpa using SmoothDirectImage.coefficientMap_id M

/-- Smooth trace respects equality of the original continuous maps. -/
private theorem trace_congr [∀ y, Finite (p ⁻¹' {y})] [∀ y, Finite (q ⁻¹' {y})]
    (h : p = q) (hpc : IsCoveringMap p) (hqc : IsCoveringMap q)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    SmoothDirectImage.coefficientTrace p hp hpc M =
      (eqToIso (directImage_congr (R := R) hp hq h)).hom.app
          ((LocallyConstantSheaf.smoothFunctor R G S).obj M) ≫
        SmoothDirectImage.coefficientTrace q hq hqc M := by
  subst q
  simp

/-- Transport smooth pullback composition by equality of the actual composite map. -/
private theorem coefficientMap_comp_congr {W : Type u} [TopologicalSpace W]
    [MulAction G W] [ContinuousConstSMul G W] [HasStableNeighbourhoods G W]
    (f : C(S, T)) (hf : ∀ (k : G) (x : S), f (k • x) = k • f x)
    (g : C(T, W)) (hg : ∀ (k : G) (y : T), g (k • y) = k • g y)
    {q : C(S, W)} (hq : ∀ (k : G) (x : S), q (k • x) = k • q x)
    (h : q = g.comp f) (M : Langlands.SmoothRep.{u, u, u} R G) :
    SmoothDirectImage.coefficientMap q hq M =
      SmoothDirectImage.coefficientMap g hg M ≫
        (SmoothDirectImage.functor g hg).map (SmoothDirectImage.coefficientMap f hf M) ≫
          (SmoothDirectImage.compMap f hf g hg ≫
            (eqToIso (directImage_congr (R := R) hq
              (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) h)).inv).app
                ((LocallyConstantSheaf.smoothFunctor R G S).obj M) := by
  subst q
  simpa using SmoothDirectImage.coefficientMap_comp f hf g hg M

/-- Transport the generic lax trace law by equality of the actual composite map. -/
private theorem trace_comp_congr {W : Type u} [TopologicalSpace W]
    [MulAction G W] [ContinuousConstSMul G W] [HasStableNeighbourhoods G W]
    (f : C(S, T)) (hf : ∀ (k : G) (x : S), f (k • x) = k • f x)
    (g : C(T, W)) (hg : ∀ (k : G) (y : T), g (k • y) = k • g y)
    {q : C(S, W)} (hq : ∀ (k : G) (x : S), q (k • x) = k • q x)
    [∀ y, Finite (f ⁻¹' {y})] [∀ z, Finite (g ⁻¹' {z})]
    [∀ z, Finite (q ⁻¹' {z})]
    (h : q = g.comp f) (hfc : IsCoveringMap f) (hgc : IsCoveringMap g)
    (hqc : IsCoveringMap q) (M : Langlands.SmoothRep.{u, u, u} R G) :
    (SmoothDirectImage.compMap f hf g hg ≫
        (eqToIso (directImage_congr (R := R) hq
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) h)).inv).app
          ((LocallyConstantSheaf.smoothFunctor R G S).obj M) ≫
        SmoothDirectImage.coefficientTrace q hq hqc M =
      (SmoothDirectImage.functor g hg).map (SmoothDirectImage.coefficientTrace f hf hfc M) ≫
        SmoothDirectImage.coefficientTrace g hg hgc M := by
  subst q
  simpa using SmoothDirectImage.coefficientTrace_comp f hf g hg hfc hgc hqc M

end Congruence

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  (R : Type u) [CommRing R]

local instance inducedStable (X : ρ.OpenSubgroupTransport)
    [HasStableNeighbourhoods X.subgroup.toSubgroup X.LocalSpectrum] :
    HasStableNeighbourhoods G X.InducedSpectrum :=
  SpatialSheaves.hasStableNeighbourhoods_induced X

variable {X Y Z : ρ.OpenSubgroupTransport}
  [HasStableNeighbourhoods X.subgroup.toSubgroup X.LocalSpectrum]
  [HasStableNeighbourhoods Y.subgroup.toSubgroup Y.LocalSpectrum]
  [HasStableNeighbourhoods Z.subgroup.toSubgroup Z.LocalSpectrum]

/-- The existing full smooth coefficient functor, on the actual rational spectrum. -/
def coefficientFunctor (X : ρ.OpenSubgroupTransport)
    [HasStableNeighbourhoods X.subgroup.toSubgroup X.LocalSpectrum] :
    Langlands.SmoothRep.{u, u, u} R G ⥤
      SmoothTopologicalSheaf R G X.InducedSpectrum :=
  SpatialSheaves.smoothInducedCoefficientFunctor X R

/-- Smooth direct image is the actual coreflection of the full rational direct image. -/
def directImage (f : X ⟶ Y) :
    SmoothTopologicalSheaf R G X.InducedSpectrum ⥤
      SmoothTopologicalSheaf R G Y.InducedSpectrum :=
  SmoothDirectImage.functor f.inducedMap f.inducedMap_smul

/-- The smooth image embeds into the unchanged full rational direct image. -/
def inclusion (f : X ⟶ Y) :
    directImage R f ⋙ Langlands.Sheaf.Equivariant.smoothInclusion R G Y.InducedSpectrum ⟶
      Langlands.Sheaf.Equivariant.smoothInclusion R G X.InducedSpectrum ⋙
        SheafVariation.directImage (ModuleCat.{u} R) f :=
  SmoothDirectImage.inclusion f.inducedMap f.inducedMap_smul

/-- The identity comparison uses equality of the original rational identity map. -/
def directImageIdIso (X : ρ.OpenSubgroupTransport)
    [HasStableNeighbourhoods X.subgroup.toSubgroup X.LocalSpectrum] :
    𝟭 (SmoothTopologicalSheaf R G X.InducedSpectrum) ≅ directImage R (𝟙 X) :=
  SmoothDirectImage.idIso ≪≫
    (eqToIso (directImage_congr (R := R) (Hom.inducedMap_smul (𝟙 X))
      (fun (_ : G) (_ : X.InducedSpectrum) => rfl)
      (SheafVariation.inducedMap_id_eq X))).symm

/-- Iterated smooth images map to the actual composite image by the lax comparison. -/
def directImageCompMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    directImage R f ⋙ directImage R g ⟶ directImage R (f ≫ g) :=
  SmoothDirectImage.compMap f.inducedMap f.inducedMap_smul g.inducedMap g.inducedMap_smul ≫
    (eqToIso (directImage_congr (R := R) (Hom.inducedMap_smul (f ≫ g))
      (fun k x => by
        change g.inducedMap (f.inducedMap (k • x)) = k • g.inducedMap (f.inducedMap x)
        rw [f.inducedMap_smul, g.inducedMap_smul])
      (SheafVariation.inducedMap_comp_eq f g))).inv

/-- Every original coefficient section pulls back through smooth direct image. -/
def coefficientMap (f : X ⟶ Y) (M : Langlands.SmoothRep.{u, u, u} R G) :
    (coefficientFunctor R Y).obj M ⟶
      (directImage R f).obj ((coefficientFunctor R X).obj M) :=
  SmoothDirectImage.coefficientMap f.inducedMap f.inducedMap_smul M

/-- The smooth pullback has exactly the full ordinary rational coefficient map. -/
@[reassoc (attr := simp)]
theorem coefficientMap_inclusion (f : X ⟶ Y)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (Langlands.Sheaf.Equivariant.smoothInclusion R G Y.InducedSpectrum).map (coefficientMap R f M) ≫
        (inclusion R f).app ((coefficientFunctor R X).obj M) =
      SheafVariation.coefficientMap f M.representation := rfl

/-- The original section is precomposed with the original rational spatial map. -/
@[simp]
theorem coefficientMap_apply (f : X ⟶ Y)
    (M : Langlands.SmoothRep.{u, u, u} R G)
    (U : ActionOpens G Y.InducedSpectrum) (s : LocallyConstant U.openSet M)
    (z : ((SheafVariation.preimage f).obj U).openSet) :
    LocallyConstant.toFun
      ((((coefficientMap R f M).hom.hom.app (op U)).hom s).val) z =
        s (DirectImage.pointMap f.inducedMap f.inducedMap_smul U z) := rfl

/-- Rational pullback on representatives retains the original inverse label. -/
theorem coefficientMap_mk_apply (f : X ⟶ Y)
    (M : Langlands.SmoothRep.{u, u, u} R G)
    (U : ActionOpens G Y.InducedSpectrum) (s : LocallyConstant U.openSet M)
    (a : G) (x : X.LocalSpectrum)
    (h : X.inducedMk a x ∈ ((SheafVariation.preimage f).obj U).openSet) :
    LocallyConstant.toFun
      ((((coefficientMap R f M).hom.hom.app (op U)).hom s).val)
        ⟨X.inducedMk a x, h⟩ =
      s ⟨Y.inducedMk (a * f.label⁻¹) (f.localSpectrumMap x),
        (SheafVariation.inducedMk_mem_preimage f U a x).mp h⟩ :=
  SheafVariation.coefficientMap_mk_apply f M.representation U s a x h

/-- The pullback retains all original smooth coefficients and intertwiners. -/
def coefficientNatTrans (f : X ⟶ Y) :
    coefficientFunctor R Y ⟶ coefficientFunctor R X ⋙ directImage R f :=
  SmoothDirectImage.coefficientNatTrans f.inducedMap f.inducedMap_smul

@[simp]
theorem coefficientNatTrans_app (f : X ⟶ Y) (M : Langlands.SmoothRep.{u, u, u} R G) :
    (coefficientNatTrans R f).app M = coefficientMap R f M := rfl

@[reassoc]
theorem coefficientMap_naturality (f : X ⟶ Y)
    {M N : Langlands.SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (coefficientFunctor R Y).map a ≫ coefficientMap R f N =
      coefficientMap R f M ≫ (directImage R f).map ((coefficientFunctor R X).map a) :=
  (coefficientNatTrans R f).naturality a

/-- The original rational identity pullback is the actual smooth comparison unit. -/
theorem coefficientMap_id (M : Langlands.SmoothRep.{u, u, u} R G) :
    coefficientMap R (𝟙 X) M =
      (directImageIdIso R X).hom.app ((coefficientFunctor R X).obj M) :=
  coefficientMap_id_congr (Hom.inducedMap_smul (𝟙 X))
    (SheafVariation.inducedMap_id_eq X) M

/-- Rational pullbacks compose through the actual lax smooth-image comparison. -/
@[reassoc]
theorem coefficientMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    coefficientMap R (f ≫ g) M =
      coefficientMap R g M ≫ (directImage R g).map (coefficientMap R f M) ≫
        (directImageCompMap R f g).app ((coefficientFunctor R X).obj M) :=
  coefficientMap_comp_congr f.inducedMap f.inducedMap_smul g.inducedMap g.inducedMap_smul
    (Hom.inducedMap_smul (f ≫ g)) (SheafVariation.inducedMap_comp_eq f g) M

/-- Trace from the actual smooth image, with the full original smooth target. -/
def coefficientTrace (f : X ⟶ Y) [∀ y, Finite (f.inducedMap ⁻¹' {y})]
    (hf : IsCoveringMap f.inducedMap) (M : Langlands.SmoothRep.{u, u, u} R G) :
    (directImage R f).obj ((coefficientFunctor R X).obj M) ⟶
      (coefficientFunctor R Y).obj M :=
  SmoothDirectImage.coefficientTrace f.inducedMap f.inducedMap_smul hf M

/-- Forgetting smoothness gives inclusion followed by the existing full rational trace. -/
@[simp]
theorem coefficientTrace_forget (f : X ⟶ Y) [∀ y, Finite (f.inducedMap ⁻¹' {y})]
    (hf : IsCoveringMap f.inducedMap) (M : Langlands.SmoothRep.{u, u, u} R G) :
    (Langlands.Sheaf.Equivariant.smoothInclusion R G Y.InducedSpectrum).map (coefficientTrace R f hf M) =
      (inclusion R f).app ((coefficientFunctor R X).obj M) ≫
        SheafVariation.coefficientTrace f hf M.representation := rfl

/-- Evaluation sums the original underlying section over the entire original fiber. -/
theorem coefficientTrace_apply_sum (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})]
    (hf : IsCoveringMap f.inducedMap) (M : Langlands.SmoothRep.{u, u, u} R G)
    (U : ActionOpens G Y.InducedSpectrum)
    (s : ((directImage R f).obj ((coefficientFunctor R X).obj M)).obj.obj.obj (op U))
    (y : U.openSet) [Fintype (f.inducedMap ⁻¹' {y.val})] :
    LocallyConstant.toFun (((coefficientTrace R f hf M).hom.hom.app (op U)).hom s) y =
      ∑ x : f.inducedMap ⁻¹' {y.val},
        (LocallyConstant.toFun
          (s.val : LocallyConstant ((SheafVariation.preimage f).obj U).openSet M)) ⟨x.val, by
          change f.inducedMap x.val ∈ U.openSet
          rw [show f.inducedMap x.val = y.val from x.property]
          exact y.property⟩ :=
  SmoothDirectImage.coefficientTrace_apply_sum f.inducedMap f.inducedMap_smul hf M U s y

/-- Smooth pullback followed by trace counts the actual rational fiber pointwise. -/
theorem coefficientTrace_pullback_apply (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})]
    (hf : IsCoveringMap f.inducedMap) (M : Langlands.SmoothRep.{u, u, u} R G)
    (U : ActionOpens G Y.InducedSpectrum) (s : LocallyConstant U.openSet M)
    (y : U.openSet) :
    LocallyConstant.toFun
        (((coefficientMap R f M ≫ coefficientTrace R f hf M).hom.hom.app (op U)).hom s) y =
      Nat.card (f.inducedMap ⁻¹' {y.val}) • s y :=
  SmoothDirectImage.coefficientTrace_pullback_apply
    f.inducedMap f.inducedMap_smul hf M U s y

/-- The degree formula evaluates at the actual inverse-label rational image. -/
theorem coefficientTrace_pullback_mk_apply (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})]
    (hf : IsCoveringMap f.inducedMap) (M : Langlands.SmoothRep.{u, u, u} R G)
    (U : ActionOpens G Y.InducedSpectrum) (s : LocallyConstant U.openSet M)
    (a : G) (x : X.LocalSpectrum)
    (hy : Y.inducedMk (a * f.label⁻¹) (f.localSpectrumMap x) ∈ U.openSet) :
    LocallyConstant.toFun
        (((coefficientMap R f M ≫ coefficientTrace R f hf M).hom.hom.app (op U)).hom s)
        ⟨Y.inducedMk (a * f.label⁻¹) (f.localSpectrumMap x), hy⟩ =
      Nat.card (f.inducedMap ⁻¹'
        {Y.inducedMk (a * f.label⁻¹) (f.localSpectrumMap x)}) •
          s ⟨Y.inducedMk (a * f.label⁻¹) (f.localSpectrumMap x), hy⟩ :=
  coefficientTrace_pullback_apply R f hf M U s _

/-- The finite trace commutes with every original smooth coefficient intertwiner. -/
def coefficientTraceNatTrans (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] (hf : IsCoveringMap f.inducedMap) :
    coefficientFunctor R X ⋙ directImage R f ⟶ coefficientFunctor R Y :=
  SmoothDirectImage.coefficientTraceNatTrans f.inducedMap f.inducedMap_smul hf

@[simp]
theorem coefficientTraceNatTrans_app (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] (hf : IsCoveringMap f.inducedMap)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (coefficientTraceNatTrans R f hf).app M = coefficientTrace R f hf M := rfl

@[reassoc]
theorem coefficientTrace_naturality (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] (hf : IsCoveringMap f.inducedMap)
    {M N : Langlands.SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (directImage R f).map ((coefficientFunctor R X).map a) ≫ coefficientTrace R f hf N =
      coefficientTrace R f hf M ≫ (coefficientFunctor R Y).map a :=
  (coefficientTraceNatTrans R f hf).naturality a

section Identity

local instance finite_identityFiber :
    ∀ x : X.InducedSpectrum, Finite ((𝟙 X : X ⟶ X).inducedMap ⁻¹' {x}) :=
  Hom.finite_inducedMap_id_fiber X

/-- Rational identity trace is the inverse of the actual smooth identity comparison. -/
@[simp]
theorem coefficientTrace_id (M : Langlands.SmoothRep.{u, u, u} R G) :
    coefficientTrace R (𝟙 X) (Hom.isCoveringMap_inducedMap_id X) M =
      (directImageIdIso R X).inv.app ((coefficientFunctor R X).obj M) := by
  let : ∀ x : X.InducedSpectrum, Finite ((ContinuousMap.id X.InducedSpectrum) ⁻¹' {x}) :=
    finite_id_fiber
  exact (trace_congr (Hom.inducedMap_smul (𝟙 X))
    (fun (_ : G) (_ : X.InducedSpectrum) => rfl) (SheafVariation.inducedMap_id_eq X)
    (Hom.isCoveringMap_inducedMap_id X) isCoveringMap_id M).trans
      (congrArg (fun k =>
        (eqToIso (directImage_congr (R := R) (Hom.inducedMap_smul (𝟙 X))
          (fun (_ : G) (_ : X.InducedSpectrum) => rfl)
          (SheafVariation.inducedMap_id_eq X))).hom.app
            ((coefficientFunctor R X).obj M) ≫ k)
        (SmoothDirectImage.coefficientTrace_id M))

/-- Identity trace comparison is natural on the full original coefficient category. -/
@[simp]
theorem coefficientTraceNatTrans_id :
    coefficientTraceNatTrans R (𝟙 X) (Hom.isCoveringMap_inducedMap_id X) =
      Functor.whiskerLeft (coefficientFunctor R X) (directImageIdIso R X).inv := by
  apply NatTrans.ext
  funext M
  exact coefficientTrace_id R M

end Identity

/-- Successive rational traces agree after the actual lax smooth-image comparison. -/
theorem coefficientTrace_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] [∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [∀ z, Finite ((f ≫ g).inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hfg : IsCoveringMap (f ≫ g).inducedMap)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (directImageCompMap R f g).app ((coefficientFunctor R X).obj M) ≫
        coefficientTrace R (f ≫ g) hfg M =
      (directImage R g).map (coefficientTrace R f hf M) ≫ coefficientTrace R g hg M :=
  trace_comp_congr f.inducedMap f.inducedMap_smul g.inducedMap g.inducedMap_smul
    (Hom.inducedMap_smul (f ≫ g)) (SheafVariation.inducedMap_comp_eq f g) hf hg hfg M

/-- The rational lax composition law retains all original coefficient intertwiners. -/
theorem coefficientTraceNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] [∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [∀ z, Finite ((f ≫ g).inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hfg : IsCoveringMap (f ≫ g).inducedMap) :
    Functor.whiskerLeft (coefficientFunctor R X) (directImageCompMap R f g) ≫
        coefficientTraceNatTrans R (f ≫ g) hfg =
      Functor.whiskerRight (coefficientTraceNatTrans R f hf) (directImage R g) ≫
        coefficientTraceNatTrans R g hg := by
  apply NatTrans.ext
  funext M
  exact coefficientTrace_comp R f g hf hg hfg M

end OpenSubgroupTransport.SmoothSheafVariation

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
