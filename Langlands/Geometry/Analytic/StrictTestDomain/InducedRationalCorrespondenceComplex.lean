import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCorrespondence

/-! # Trace and correspondence maps on supported coefficient complexes -/

noncomputable section

universe u v r w t

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Limits Topology
open Langlands.LocallyConstantCovering

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type r} [CommRing R]
  {ι : Type t}

namespace OpenSubgroupTransport.Hom

open CompactSections

variable {S T W X Y Z : ρ.OpenSubgroupTransport}

@[simp]
theorem compactSupportTraceNatTrans_id
    [∀ x, Finite ((𝟙 X : X ⟶ X).inducedMap ⁻¹' {x})] :
    compactSupportTraceNatTrans.{u, v, r, w} (R := R) (𝟙 X)
        (isCoveringMap_inducedMap_id X) = 𝟙 (coefficientFunctor X) := by
  apply NatTrans.ext
  funext M
  exact compactSupportTrace_id M

theorem compactSupportTraceNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] [∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [∀ z, Finite ((f ≫ g).inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hfg : IsCoveringMap (f ≫ g).inducedMap) :
    compactSupportTraceNatTrans.{u, v, r, w} (R := R) (f ≫ g) hfg =
      compactSupportTraceNatTrans f hf ≫ compactSupportTraceNatTrans g hg := by
  apply NatTrans.ext
  funext M
  exact compactSupportTrace_comp f g hf hg hfg M

/-- The original finite-covering trace in every degree of a supplied coefficient complex. -/
def compactComplexTraceNatTrans (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] (hf : IsCoveringMap f.inducedMap)
    (c : ComplexShape ι) :
    supportedComplexFunctor.{u, v, r, w, t} (R := R) X c ⟶
      supportedComplexFunctor Y c :=
  (compactSupportTraceNatTrans f hf).mapHomologicalComplex c

@[simp]
theorem compactComplexTrace_apply (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] (hf : IsCoveringMap f.inducedMap)
    (c : ComplexShape ι) (C : HomologicalComplex (SmoothRep.{r, v, w} R G) c)
    (i : ι) (s : Functions (R := R) (V := C.X i) X) (y : Y.InducedSpectrum) :
    (SmoothRep.hom (((compactComplexTraceNatTrans f hf c).app C).f i) s).val y =
      fiberSum f.inducedMap s.val y := rfl

@[simp]
theorem compactComplexTraceNatTrans_id
    [∀ x, Finite ((𝟙 X : X ⟶ X).inducedMap ⁻¹' {x})]
    (c : ComplexShape ι) :
    compactComplexTraceNatTrans.{u, v, r, w, t} (R := R) (𝟙 X)
        (isCoveringMap_inducedMap_id X) c = 𝟙 (supportedComplexFunctor X c) := by
  simp [compactComplexTraceNatTrans, supportedComplexFunctor]

theorem compactComplexTraceNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] [∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [∀ z, Finite ((f ≫ g).inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hfg : IsCoveringMap (f ≫ g).inducedMap) (c : ComplexShape ι) :
    compactComplexTraceNatTrans.{u, v, r, w, t} (R := R) (f ≫ g) hfg c =
      compactComplexTraceNatTrans f hf c ≫ compactComplexTraceNatTrans g hg c := by
  change NatTrans.mapHomologicalComplex (compactSupportTraceNatTrans (f ≫ g) hfg) c = _
  rw [compactSupportTraceNatTrans_comp f g hf hg hfg]
  exact NatTrans.mapHomologicalComplex_comp c _ _

/-- Apply genuine homology to the explicitly constructed supported trace chain map. -/
def compactHomologyTraceNatTrans (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] (hf : IsCoveringMap f.inducedMap)
    (c : ComplexShape ι) (i : ι) :
    supportedHomologyFunctor.{u, v, r, w, t} (R := R) X c i ⟶
      supportedHomologyFunctor Y c i :=
  Functor.whiskerRight (compactComplexTraceNatTrans f hf c)
    (HomologicalComplex.homologyFunctor (SmoothRep.{r, v, max u v w} R G) c i)

@[simp]
theorem compactHomologyTraceNatTrans_id
    [∀ x, Finite ((𝟙 X : X ⟶ X).inducedMap ⁻¹' {x})]
    (c : ComplexShape ι) (i : ι) :
    compactHomologyTraceNatTrans.{u, v, r, w, t} (R := R) (𝟙 X)
        (isCoveringMap_inducedMap_id X) c i = 𝟙 (supportedHomologyFunctor X c i) := by
  apply NatTrans.ext
  funext C
  change (HomologicalComplex.homologyFunctor _ c i).map _ = 𝟙 _
  rw [compactComplexTraceNatTrans_id]
  exact (HomologicalComplex.homologyFunctor _ c i).map_id _

theorem compactHomologyTraceNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] [∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [∀ z, Finite ((f ≫ g).inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hfg : IsCoveringMap (f ≫ g).inducedMap) (c : ComplexShape ι) (i : ι) :
    compactHomologyTraceNatTrans.{u, v, r, w, t} (R := R) (f ≫ g) hfg c i =
      compactHomologyTraceNatTrans f hf c i ≫ compactHomologyTraceNatTrans g hg c i := by
  apply NatTrans.ext
  funext C
  change (HomologicalComplex.homologyFunctor _ c i).map _ = _
  rw [compactComplexTraceNatTrans_comp f g hf hg hfg]
  exact Functor.map_comp _ _ _

/-- The actual pull-push correspondence, prolonged to the supported coefficient complex. -/
def compactComplexCorrespondenceNatTrans (a : S ⟶ X) (b : S ⟶ Y)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    (c : ComplexShape ι) :
    supportedComplexFunctor.{u, v, r, w, t} (R := R) X c ⟶
      supportedComplexFunctor Y c :=
  (compactSupportCorrespondenceNatTrans a b ha hb).mapHomologicalComplex c

theorem compactComplexCorrespondenceNatTrans_eq_pullback_trace
    (a : S ⟶ X) (b : S ⟶ Y) [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    (c : ComplexShape ι) :
    compactComplexCorrespondenceNatTrans.{u, v, r, w, t} (R := R) a b ha hb c =
      compactComplexPullbackNatTrans a ha c ≫ compactComplexTraceNatTrans b hb c :=
  NatTrans.mapHomologicalComplex_comp c _ _

@[simp]
theorem compactComplexCorrespondence_apply
    (a : S ⟶ X) (b : S ⟶ Y) [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    (c : ComplexShape ι) (C : HomologicalComplex (SmoothRep.{r, v, w} R G) c)
    (i : ι) (s : Functions (R := R) (V := C.X i) X) (y : Y.InducedSpectrum) :
    (SmoothRep.hom (((compactComplexCorrespondenceNatTrans a b ha hb c).app C).f i)
        s).val y = fiberSum b.inducedMap (s.val ∘ a.inducedMap) y := rfl

theorem compactComplexCorrespondence_self_apply (a : S ⟶ X)
    [∀ x, Finite (a.inducedMap ⁻¹' {x})]
    (ha : IsProperMap a.inducedMap) (hc : IsCoveringMap a.inducedMap)
    (c : ComplexShape ι) (C : HomologicalComplex (SmoothRep.{r, v, w} R G) c)
    (i : ι) (s : Functions (R := R) (V := C.X i) X) (x : X.InducedSpectrum) :
    (SmoothRep.hom (((compactComplexCorrespondenceNatTrans a a ha hc c).app C).f i)
        s).val x = Nat.card (a.inducedMap ⁻¹' {x}) • s.val x :=
  compactSupportCorrespondence_self_apply a ha hc (C.X i) s x

@[simp]
theorem compactComplexCorrespondenceNatTrans_id
    [∀ x, Finite ((𝟙 X : X ⟶ X).inducedMap ⁻¹' {x})] (c : ComplexShape ι) :
    compactComplexCorrespondenceNatTrans.{u, v, r, w, t} (R := R) (𝟙 X) (𝟙 X)
        (isProperMap_inducedMap_id X) (isCoveringMap_inducedMap_id X) c =
      𝟙 (supportedComplexFunctor X c) := by
  simp [compactComplexCorrespondenceNatTrans, supportedComplexFunctor]

/-- Cartesian base change for the original induced maps is an equality of chain maps. -/
theorem compactComplexTraceNatTrans_baseChange
    (a : S ⟶ X) (b : S ⟶ Y) (q : X ⟶ Z) (p : Y ⟶ Z)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    [∀ z, Finite (q.inducedMap ⁻¹' {z})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    (hq : IsCoveringMap q.inducedMap) (hp : IsProperMap p.inducedMap)
    (h : IsPullback (↾a.inducedMap) (↾b.inducedMap) (↾q.inducedMap) (↾p.inducedMap))
    (c : ComplexShape ι) :
    compactComplexPullbackNatTrans.{u, v, r, w, t} (R := R) a ha c ≫
        compactComplexTraceNatTrans b hb c =
      compactComplexTraceNatTrans q hq c ≫ compactComplexPullbackNatTrans p hp c := by
  change NatTrans.mapHomologicalComplex (compactSupportPullbackNatTrans a ha) c ≫
      NatTrans.mapHomologicalComplex (compactSupportTraceNatTrans b hb) c = _
  rw [← NatTrans.mapHomologicalComplex_comp,
    compactSupportTraceNatTrans_baseChange a b q p ha hb hq hp h]
  exact NatTrans.mapHomologicalComplex_comp c _ _

/-- Cartesian composition of original spans holds for the supported chain maps. -/
theorem compactComplexCorrespondenceNatTrans_comp
    (a : S ⟶ X) (b : S ⟶ Y) (l : T ⟶ Y) (d : T ⟶ Z)
    (e : W ⟶ S) (f : W ⟶ T)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    [∀ z, Finite (f.inducedMap ⁻¹' {z})]
    [∀ z, Finite (d.inducedMap ⁻¹' {z})]
    [∀ z, Finite ((f ≫ d).inducedMap ⁻¹' {z})]
    (ha : IsProperMap a.inducedMap) (hl : IsProperMap l.inducedMap)
    (he : IsProperMap e.inducedMap)
    (hb : IsCoveringMap b.inducedMap) (hd : IsCoveringMap d.inducedMap)
    (hfd : IsCoveringMap (f ≫ d).inducedMap)
    (h : IsPullback (↾e.inducedMap) (↾f.inducedMap) (↾b.inducedMap) (↾l.inducedMap))
    (c : ComplexShape ι) :
    compactComplexCorrespondenceNatTrans.{u, v, r, w, t} (R := R) (e ≫ a) (f ≫ d)
        (isProperMap_inducedMap_comp e a he ha) hfd c =
      compactComplexCorrespondenceNatTrans a b ha hb c ≫
        compactComplexCorrespondenceNatTrans l d hl hd c := by
  change NatTrans.mapHomologicalComplex
      (compactSupportCorrespondenceNatTrans (e ≫ a) (f ≫ d)
        (isProperMap_inducedMap_comp e a he ha) hfd) c = _
  rw [compactSupportCorrespondenceNatTrans_comp a b l d e f ha hl he hb hd hfd h]
  exact NatTrans.mapHomologicalComplex_comp c _ _

/-- The actual homology map of the supported correspondence chain map. -/
def compactHomologyCorrespondenceNatTrans (a : S ⟶ X) (b : S ⟶ Y)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    (c : ComplexShape ι) (i : ι) :
    supportedHomologyFunctor.{u, v, r, w, t} (R := R) X c i ⟶
      supportedHomologyFunctor Y c i :=
  Functor.whiskerRight (compactComplexCorrespondenceNatTrans a b ha hb c)
    (HomologicalComplex.homologyFunctor (SmoothRep.{r, v, max u v w} R G) c i)

theorem compactHomologyCorrespondenceNatTrans_eq_pullback_trace
    (a : S ⟶ X) (b : S ⟶ Y) [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    (c : ComplexShape ι) (i : ι) :
    compactHomologyCorrespondenceNatTrans.{u, v, r, w, t} (R := R) a b ha hb c i =
      compactHomologyPullbackNatTrans a ha c i ≫ compactHomologyTraceNatTrans b hb c i := by
  apply NatTrans.ext
  funext C
  change (HomologicalComplex.homologyFunctor _ c i).map _ = _
  rw [compactComplexCorrespondenceNatTrans_eq_pullback_trace]
  exact Functor.map_comp _ _ _

@[simp]
theorem compactHomologyCorrespondenceNatTrans_id
    [∀ x, Finite ((𝟙 X : X ⟶ X).inducedMap ⁻¹' {x})]
    (c : ComplexShape ι) (i : ι) :
    compactHomologyCorrespondenceNatTrans.{u, v, r, w, t} (R := R) (𝟙 X) (𝟙 X)
        (isProperMap_inducedMap_id X) (isCoveringMap_inducedMap_id X) c i =
      𝟙 (supportedHomologyFunctor X c i) := by
  apply NatTrans.ext
  funext C
  change (HomologicalComplex.homologyFunctor _ c i).map _ = 𝟙 _
  rw [compactComplexCorrespondenceNatTrans_id]
  exact (HomologicalComplex.homologyFunctor _ c i).map_id _

theorem compactHomologyTraceNatTrans_baseChange
    (a : S ⟶ X) (b : S ⟶ Y) (q : X ⟶ Z) (p : Y ⟶ Z)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    [∀ z, Finite (q.inducedMap ⁻¹' {z})]
    (ha : IsProperMap a.inducedMap) (hb : IsCoveringMap b.inducedMap)
    (hq : IsCoveringMap q.inducedMap) (hp : IsProperMap p.inducedMap)
    (h : IsPullback (↾a.inducedMap) (↾b.inducedMap) (↾q.inducedMap) (↾p.inducedMap))
    (c : ComplexShape ι) (i : ι) :
    compactHomologyPullbackNatTrans.{u, v, r, w, t} (R := R) a ha c i ≫
        compactHomologyTraceNatTrans b hb c i =
      compactHomologyTraceNatTrans q hq c i ≫ compactHomologyPullbackNatTrans p hp c i := by
  apply NatTrans.ext
  funext C
  let H := HomologicalComplex.homologyFunctor (SmoothRep.{r, v, max u v w} R G) c i
  change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
  exact (H.map_comp _ _).symm.trans
    ((H.congr_map (NatTrans.congr_app
      (compactComplexTraceNatTrans_baseChange a b q p ha hb hq hp h c) C)).trans
      (H.map_comp _ _))

theorem compactHomologyCorrespondenceNatTrans_comp
    (a : S ⟶ X) (b : S ⟶ Y) (l : T ⟶ Y) (d : T ⟶ Z)
    (e : W ⟶ S) (f : W ⟶ T)
    [∀ y, Finite (b.inducedMap ⁻¹' {y})]
    [∀ z, Finite (f.inducedMap ⁻¹' {z})]
    [∀ z, Finite (d.inducedMap ⁻¹' {z})]
    [∀ z, Finite ((f ≫ d).inducedMap ⁻¹' {z})]
    (ha : IsProperMap a.inducedMap) (hl : IsProperMap l.inducedMap)
    (he : IsProperMap e.inducedMap)
    (hb : IsCoveringMap b.inducedMap) (hd : IsCoveringMap d.inducedMap)
    (hfd : IsCoveringMap (f ≫ d).inducedMap)
    (h : IsPullback (↾e.inducedMap) (↾f.inducedMap) (↾b.inducedMap) (↾l.inducedMap))
    (c : ComplexShape ι) (i : ι) :
    compactHomologyCorrespondenceNatTrans.{u, v, r, w, t} (R := R) (e ≫ a) (f ≫ d)
        (isProperMap_inducedMap_comp e a he ha) hfd c i =
      compactHomologyCorrespondenceNatTrans a b ha hb c i ≫
        compactHomologyCorrespondenceNatTrans l d hl hd c i := by
  apply NatTrans.ext
  funext C
  change (HomologicalComplex.homologyFunctor _ c i).map _ = _
  rw [compactComplexCorrespondenceNatTrans_comp a b l d e f ha hl he hb hd hfd h]
  exact Functor.map_comp _ _ _

end OpenSubgroupTransport.Hom

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
