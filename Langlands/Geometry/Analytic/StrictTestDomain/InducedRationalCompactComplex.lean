import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCompactSupport
import Langlands.Representation.Category.Abelian
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Supported coefficient complexes on actual induced rational spectra -/

noncomputable section

universe u v r w t

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type r} [CommRing R]
  {ι : Type t}

namespace OpenSubgroupTransport

namespace CompactSections

variable (X : ρ.OpenSubgroupTransport)

/-- The actual supported coefficient functor preserves addition of intertwiners. -/
instance coefficientFunctor_additive :
    (coefficientFunctor.{u, v, r, w} (R := R) X).Additive where
  map_add := by
    intro M N b d
    ext s
    apply Subtype.ext
    apply LocallyConstant.ext
    intro z
    rfl

/-- Degreewise supported functions on an actual complex of smooth coefficients. -/
def supportedComplexFunctor (c : ComplexShape ι) :
    HomologicalComplex (SmoothRep.{r, v, w} R G) c ⥤
      HomologicalComplex (SmoothRep.{r, v, max u v w} R G) c :=
  (coefficientFunctor X).mapHomologicalComplex c

instance supportedComplexFunctor_additive (c : ComplexShape ι) :
    (supportedComplexFunctor.{u, v, r, w, t} (R := R) X c).Additive :=
  inferInstanceAs ((coefficientFunctor X).mapHomologicalComplex c).Additive

@[simp]
theorem supportedComplex_d_apply (c : ComplexShape ι)
    (C : HomologicalComplex (SmoothRep.{r, v, w} R G) c) (i j : ι)
    (s : Functions (R := R) (V := C.X i) X) (z : X.InducedSpectrum) :
    (SmoothRep.hom (((supportedComplexFunctor X c).obj C).d i j) s).val z =
      SmoothRep.hom (C.d i j) (s.val z) := rfl

@[simp]
theorem supportedComplex_map_apply (c : ComplexShape ι)
    {C D : HomologicalComplex (SmoothRep.{r, v, w} R G) c}
    (b : C ⟶ D) (i : ι) (s : Functions (R := R) (V := C.X i) X)
    (z : X.InducedSpectrum) :
    (SmoothRep.hom (((supportedComplexFunctor X c).map b).f i) s).val z =
      SmoothRep.hom (b.f i) (s.val z) := rfl

/-- The homology of this explicitly constructed supported-function complex,
retaining the proved smooth full-group action. -/
def supportedHomologyFunctor (c : ComplexShape ι) (i : ι) :
    HomologicalComplex (SmoothRep.{r, v, w} R G) c ⥤
      SmoothRep.{r, v, max u v w} R G :=
  supportedComplexFunctor X c ⋙
    HomologicalComplex.homologyFunctor (SmoothRep.{r, v, max u v w} R G) c i

/-- Supported nonnegative cochains, with pointwise coefficient differential. -/
abbrev supportedCochainFunctor :
    CochainComplex (SmoothRep.{r, v, w} R G) ℕ ⥤
      CochainComplex (SmoothRep.{r, v, max u v w} R G) ℕ :=
  supportedComplexFunctor X (ComplexShape.up ℕ)

end CompactSections

namespace Hom

open CompactSections

variable {X Y Z : ρ.OpenSubgroupTransport}

/-- Proper transport pullback is a natural transformation in smooth coefficients. -/
def compactSupportPullbackNatTrans (f : X ⟶ Y) (hf : IsProperMap f.inducedMap) :
    coefficientFunctor.{u, v, r, w} (R := R) Y ⟶ coefficientFunctor X where
  app := f.compactSupportPullback hf
  naturality _ _ b := compactSupportPullback_naturality f hf b

@[simp]
theorem compactSupportPullbackNatTrans_id (X : ρ.OpenSubgroupTransport) :
    compactSupportPullbackNatTrans.{u, v, r, w} (R := R)
      (𝟙 X) (isProperMap_inducedMap_id X) = 𝟙 (coefficientFunctor X) := by
  apply NatTrans.ext
  funext M
  exact compactSupportPullback_id M

theorem compactSupportPullbackNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap) :
    compactSupportPullbackNatTrans.{u, v, r, w} (R := R) (f ≫ g)
        (isProperMap_inducedMap_comp f g hf hg) =
      compactSupportPullbackNatTrans g hg ≫ compactSupportPullbackNatTrans f hf := by
  apply NatTrans.ext
  funext M
  exact compactSupportPullback_comp f g hf hg M

/-- The induced chain map is ordinary proper pullback in every degree. -/
def compactComplexPullbackNatTrans (f : X ⟶ Y) (hf : IsProperMap f.inducedMap)
    (c : ComplexShape ι) :
    supportedComplexFunctor.{u, v, r, w, t} (R := R) Y c ⟶
      supportedComplexFunctor X c :=
  (compactSupportPullbackNatTrans f hf).mapHomologicalComplex c

@[simp]
theorem compactComplexPullback_apply (f : X ⟶ Y) (hf : IsProperMap f.inducedMap)
    (c : ComplexShape ι) (C : HomologicalComplex (SmoothRep.{r, v, w} R G) c)
    (i : ι) (s : Functions (R := R) (V := C.X i) Y) (z : X.InducedSpectrum) :
    (SmoothRep.hom (((compactComplexPullbackNatTrans f hf c).app C).f i) s).val z =
      s.val (f.inducedMap z) := rfl

@[simp]
theorem compactComplexPullbackNatTrans_id (X : ρ.OpenSubgroupTransport)
    (c : ComplexShape ι) :
    compactComplexPullbackNatTrans.{u, v, r, w, t} (R := R)
      (𝟙 X) (isProperMap_inducedMap_id X) c =
        𝟙 (supportedComplexFunctor X c) := by
  simp [compactComplexPullbackNatTrans, supportedComplexFunctor]

theorem compactComplexPullbackNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap)
    (c : ComplexShape ι) :
    compactComplexPullbackNatTrans.{u, v, r, w, t} (R := R)
        (f ≫ g) (isProperMap_inducedMap_comp f g hf hg) c =
      compactComplexPullbackNatTrans g hg c ≫ compactComplexPullbackNatTrans f hf c := by
  change NatTrans.mapHomologicalComplex
      (compactSupportPullbackNatTrans (f ≫ g)
        (isProperMap_inducedMap_comp f g hf hg)) c = _
  rw [compactSupportPullbackNatTrans_comp f g hf hg]
  exact NatTrans.mapHomologicalComplex_comp c _ _

/-- The genuine induced map on homology, obtained by applying the homology functor. -/
def compactHomologyPullbackNatTrans (f : X ⟶ Y) (hf : IsProperMap f.inducedMap)
    (c : ComplexShape ι) (i : ι) :
    supportedHomologyFunctor.{u, v, r, w, t} (R := R) Y c i ⟶
      supportedHomologyFunctor X c i :=
  Functor.whiskerRight (compactComplexPullbackNatTrans f hf c)
    (HomologicalComplex.homologyFunctor (SmoothRep.{r, v, max u v w} R G) c i)

@[simp]
theorem compactHomologyPullbackNatTrans_id (X : ρ.OpenSubgroupTransport)
    (c : ComplexShape ι) (i : ι) :
    compactHomologyPullbackNatTrans.{u, v, r, w, t} (R := R)
      (𝟙 X) (isProperMap_inducedMap_id X) c i =
        𝟙 (supportedHomologyFunctor X c i) := by
  apply NatTrans.ext
  funext C
  change (HomologicalComplex.homologyFunctor _ c i).map _ = 𝟙 _
  rw [compactComplexPullbackNatTrans_id]
  exact (HomologicalComplex.homologyFunctor _ c i).map_id _

theorem compactHomologyPullbackNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap)
    (c : ComplexShape ι) (i : ι) :
    compactHomologyPullbackNatTrans.{u, v, r, w, t} (R := R)
        (f ≫ g) (isProperMap_inducedMap_comp f g hf hg) c i =
      compactHomologyPullbackNatTrans g hg c i ≫
        compactHomologyPullbackNatTrans f hf c i := by
  apply NatTrans.ext
  funext C
  change (HomologicalComplex.homologyFunctor _ c i).map _ = _
  rw [compactComplexPullbackNatTrans_comp]
  exact Functor.map_comp _ _ _

end Hom

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
