import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCoveringTrace
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCompactComplex
import Langlands.Representation.LocallyConstant.Correspondence

/-! # Actual compact-function correspondences on induced rational spectra -/

noncomputable section

universe u v r w

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Limits Topology
open Langlands.LocallyConstantCovering

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type r} [CommRing R]

namespace OpenSubgroupTransport.Hom

open CompactSections

variable {S T W X Y Z : ρ.OpenSubgroupTransport}

/-- An original rational transport span acts by proper pullback and the
unnormalized trace on its actual finite covering fibers. -/
def compactSupportCorrespondence (a : S ⟶ X) (b : S ⟶ Y)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    (M : SmoothRep.{r, v, w} R G) :
    smoothRepresentation X M ⟶ smoothRepresentation Y M :=
  a.compactSupportPullback ha M ≫ b.compactSupportTrace hb M

@[simp]
theorem compactSupportCorrespondence_apply (a : S ⟶ X) (b : S ⟶ Y)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    (M : SmoothRep.{r, v, w} R G) (s : Functions (R := R) (V := M) X)
    (y : Y.InducedSpectrum) :
    (SmoothRep.hom (compactSupportCorrespondence a b ha hb M) s).val y =
      fiberSum b.inducedMap (s.val ∘ a.inducedMap) y := rfl

/-- The span acts naturally on all original smooth coefficient objects and maps. -/
def compactSupportCorrespondenceNatTrans (a : S ⟶ X) (b : S ⟶ Y)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap) :
    (coefficientFunctor X :
      SmoothRep.{r, v, w} R G ⥤ SmoothRep.{r, v, max u v w} R G) ⟶ coefficientFunctor Y :=
  a.compactSupportPullbackNatTrans ha ≫ b.compactSupportTraceNatTrans hb

@[simp]
theorem compactSupportCorrespondenceNatTrans_app (a : S ⟶ X) (b : S ⟶ Y)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    (M : SmoothRep.{r, v, w} R G) :
    (compactSupportCorrespondenceNatTrans (R := R) a b ha hb).app M =
      compactSupportCorrespondence a b ha hb M := rfl

theorem compactSupportCorrespondence_naturality (a : S ⟶ X) (b : S ⟶ Y)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    {M N : SmoothRep.{r, v, w} R G} (c : M ⟶ N) :
    (coefficientFunctor X).map c ≫ compactSupportCorrespondence a b ha hb N =
      compactSupportCorrespondence a b ha hb M ≫ (coefficientFunctor Y).map c :=
  (compactSupportCorrespondenceNatTrans a b ha hb).naturality c

@[simp]
theorem compactSupportCorrespondence_id
    [∀ x, Finite ((𝟙 X : X ⟶ X).inducedMap ⁻¹' {x})]
    (M : SmoothRep.{r, v, w} R G) :
    compactSupportCorrespondence (𝟙 X) (𝟙 X) (isProperMap_inducedMap_id X)
        (isCoveringMap_inducedMap_id X) M = 𝟙 (smoothRepresentation X M) := by
  simp [compactSupportCorrespondence]

@[simp]
theorem compactSupportCorrespondenceNatTrans_id
    [∀ x, Finite ((𝟙 X : X ⟶ X).inducedMap ⁻¹' {x})] :
    compactSupportCorrespondenceNatTrans.{u, v, r, w} (R := R) (𝟙 X) (𝟙 X)
        (isProperMap_inducedMap_id X) (isCoveringMap_inducedMap_id X) =
      𝟙 (coefficientFunctor X) := by
  apply NatTrans.ext
  funext M
  exact compactSupportCorrespondence_id M

/-- A self-span has the literal fiber degree, without inverting that degree. -/
theorem compactSupportCorrespondence_self_apply (a : S ⟶ X)
    [∀ x, Finite (a.inducedMap ⁻¹' {x})]
    (ha : IsProperMap a.inducedMap) (hc : IsCoveringMap a.inducedMap)
    (M : SmoothRep.{r, v, w} R G) (s : Functions (R := R) (V := M) X)
    (x : X.InducedSpectrum) :
    (SmoothRep.hom (compactSupportCorrespondence a a ha hc M) s).val x =
      Nat.card (a.inducedMap ⁻¹' {x}) • s.val x :=
  fiberSum_comap a.inducedMap s.val x

/-- The original base-changed map has finite fibers by actual cartesianness. -/
theorem finite_inducedMap_pullback_fiber
    (a : S ⟶ X) (b : S ⟶ Y) (q : X ⟶ Z) (p : Y ⟶ Z)
    [∀ z, Finite (q.inducedMap ⁻¹' {z})]
    (h : IsPullback (↾a.inducedMap) (↾b.inducedMap) (↾q.inducedMap) (↾p.inducedMap))
    (y : Y.InducedSpectrum) : Finite (b.inducedMap ⁻¹' {y}) :=
  finite_pullback_fiber a.inducedMap b.inducedMap q.inducedMap p.inducedMap h y

/-- Genuine cartesianness is required of the actual induced spectrum maps. -/
theorem compactSupportTrace_baseChange
    (a : S ⟶ X) (b : S ⟶ Y) (q : X ⟶ Z) (p : Y ⟶ Z)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    [∀ z, Finite (q.inducedMap ⁻¹' {z})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    (hq : IsCoveringMap q.inducedMap) (hp : IsProperMap p.inducedMap)
    (h : IsPullback (↾a.inducedMap) (↾b.inducedMap) (↾q.inducedMap) (↾p.inducedMap))
    (M : SmoothRep.{r, v, w} R G) :
    a.compactSupportPullback ha M ≫ b.compactSupportTrace hb M =
      q.compactSupportTrace hq M ≫ p.compactSupportPullback hp M := by
  ext s
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  exact fiberSum_baseChange a.inducedMap b.inducedMap q.inducedMap p.inducedMap h s.val y

/-- Base change retains full coefficient naturality. -/
theorem compactSupportTraceNatTrans_baseChange
    (a : S ⟶ X) (b : S ⟶ Y) (q : X ⟶ Z) (p : Y ⟶ Z)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    [∀ z, Finite (q.inducedMap ⁻¹' {z})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    (hq : IsCoveringMap q.inducedMap) (hp : IsProperMap p.inducedMap)
    (h : IsPullback (↾a.inducedMap) (↾b.inducedMap) (↾q.inducedMap) (↾p.inducedMap)) :
    a.compactSupportPullbackNatTrans (R := R) ha ≫ b.compactSupportTraceNatTrans hb =
      q.compactSupportTraceNatTrans hq ≫ p.compactSupportPullbackNatTrans hp := by
  apply NatTrans.ext
  funext M
  exact compactSupportTrace_baseChange a b q p ha hb hq hp h M

/-- Compose original spans by an actual cartesian square. Properness and
covering are predicates of the original legs and the resulting composite. -/
theorem compactSupportCorrespondence_comp
    (a : S ⟶ X) (b : S ⟶ Y) (c : T ⟶ Y) (d : T ⟶ Z)
    (e : W ⟶ S) (f : W ⟶ T)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    [∀ t, Finite (f.inducedMap ⁻¹' {t})]
    [∀ z, Finite (d.inducedMap ⁻¹' {z})]
    [∀ z, Finite ((f ≫ d).inducedMap ⁻¹' {z})]
    (ha : IsProperMap a.inducedMap) (hc : IsProperMap c.inducedMap)
    (he : IsProperMap e.inducedMap)
    (hb : IsCoveringMap b.inducedMap) (hd : IsCoveringMap d.inducedMap)
    (hfd : IsCoveringMap (f ≫ d).inducedMap)
    (h : IsPullback (↾e.inducedMap) (↾f.inducedMap) (↾b.inducedMap) (↾c.inducedMap))
    (M : SmoothRep.{r, v, w} R G) :
    compactSupportCorrespondence (e ≫ a) (f ≫ d)
        (isProperMap_inducedMap_comp e a he ha) hfd M =
      compactSupportCorrespondence a b ha hb M ≫ compactSupportCorrespondence c d hc hd M := by
  ext s
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  change fiberSum (f ≫ d).inducedMap (s.val ∘ (e ≫ a).inducedMap) z =
    fiberSum d.inducedMap (fun t =>
      fiberSum b.inducedMap (s.val ∘ a.inducedMap) (c.inducedMap t)) z
  let : ∀ z, Finite ((d.inducedMap ∘ f.inducedMap) ⁻¹' {z}) :=
    finite_comp_fiber f.inducedMap d.inducedMap
  calc
    _ = fiberSum (d.inducedMap ∘ f.inducedMap)
        ((s.val ∘ a.inducedMap) ∘ e.inducedMap) z := by
      rw [fiberSum_congr (p := d.inducedMap ∘ f.inducedMap)
        (funext (inducedMap_comp f d))]
      exact congrArg (fun k : W.InducedSpectrum → M =>
        fiberSum (d.inducedMap ∘ f.inducedMap) k z)
        (funext (fun w => congrArg s.val (inducedMap_comp e a w)))
    _ = _ := fiberSum_pullback_comp e.inducedMap f.inducedMap b.inducedMap c.inducedMap
      d.inducedMap h (s.val ∘ a.inducedMap) z

/-- The cartesian span-composition law holds as a coefficient-natural equality. -/
theorem compactSupportCorrespondenceNatTrans_comp
    (a : S ⟶ X) (b : S ⟶ Y) (c : T ⟶ Y) (d : T ⟶ Z)
    (e : W ⟶ S) (f : W ⟶ T)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    [∀ t, Finite (f.inducedMap ⁻¹' {t})]
    [∀ z, Finite (d.inducedMap ⁻¹' {z})]
    [∀ z, Finite ((f ≫ d).inducedMap ⁻¹' {z})]
    (ha : IsProperMap a.inducedMap) (hc : IsProperMap c.inducedMap)
    (he : IsProperMap e.inducedMap)
    (hb : IsCoveringMap b.inducedMap) (hd : IsCoveringMap d.inducedMap)
    (hfd : IsCoveringMap (f ≫ d).inducedMap)
    (h : IsPullback (↾e.inducedMap) (↾f.inducedMap) (↾b.inducedMap) (↾c.inducedMap)) :
    compactSupportCorrespondenceNatTrans (R := R) (e ≫ a) (f ≫ d)
        (isProperMap_inducedMap_comp e a he ha) hfd =
      compactSupportCorrespondenceNatTrans a b ha hb ≫
        compactSupportCorrespondenceNatTrans c d hc hd := by
  apply NatTrans.ext
  funext M
  exact compactSupportCorrespondence_comp a b c d e f ha hc he hb hd hfd h M

end OpenSubgroupTransport.Hom

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
