import Langlands.AlgebraicGeometry.Picard.FiniteTypePicardStackAtlasStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypePointSmoothChartStatement
import Langlands.AlgebraicGeometry.Picard.PointFiberChartRestriction
import Langlands.AlgebraicGeometry.Picard.CoproductChartLineBundle
import Langlands.AlgebraicGeometry.Picard.PointFiberTestReduction
import Langlands.AlgebraicGeometry.Picard.UnitH1LineBundleClassification
import Langlands.AlgebraicGeometry.Picard.InfinitesimalGluing
import Langlands.AlgebraicGeometry.NoetherianApproximation.ClosedFiberPolynomialCharts
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberObjectIso
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-! # Smooth Picard atlases from charts at finite-type field points -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open AlgebraicSpace.CoproductChart

section Coproduct

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- Isomorphic families have isomorphic actual point fibres. -/
def pointFiberPresheafIsoOfChartIso {U T : Over S}
    {L L' : LineBundle ((relativeSpace f).obj U)} (eL : L ≅ L')
    (M : LineBundle ((relativeSpace f).obj T)) :
    pointFiberPresheaf f L M ≅ pointFiberPresheaf f L' M :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft T.iteratedSliceBackward.op
    (Langlands.CategoryTheory.PseudofunctorPointFiberObjectIso.presheafIso (relative f)
      (Core.isoMk eL) (Core.mk M))) uliftFunctor.{u + 1}

/-- Two schemes representing the same presheaf are isomorphic over the base. -/
def representingIso {T : Scheme.{u}} {P P' : Over T} {G : AlgebraicSpace.Presheaf T}
    (e : (AlgebraicSpace.schemeYoneda T).obj P ≅ G)
    (e' : (AlgebraicSpace.schemeYoneda T).obj P' ≅ G) : P ≅ P' :=
  (ULiftYoneda.fullyFaithful.{u + 1} (Over T)).preimageIso (e ≪≫ e'.symm)

/-- A coproduct chart whose point fibres are represented by schemes has smooth
point fibres when each of its components has. -/
theorem coproductChart_hasSmoothPointFibers {ι : Type u} (V : ι → Over S)
    (L : ∀ i, LineBundle ((relativeSpace f).obj (V i)))
    (hL : ∀ i, HasSmoothPointFibers f (L i))
    (hrep : ∀ (T : Over S) (M : LineBundle ((relativeSpace f).obj T)),
      ∃ P : Over T.left, Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅
        pointFiberPresheaf f (CoproductChartBundle.bundle f V L) M)) :
    HasSmoothPointFibers f (CoproductChartBundle.bundle f V L) := by
  intro T M
  obtain ⟨P, ⟨e⟩⟩ := hrep T M
  refine ⟨P, ⟨e⟩, ?_⟩
  refine IsZariskiLocalAtSource.of_openCover
    ((sigmaOpenCover (fun i ↦ (V i).left)).pullback₁ (universalMap e)) (fun i ↦ ?_)
  have : Mono (sigmaOverι V i) :=
    (Over.forget S).mono_of_mono_map (show Mono (sigmaOverι V i).left from inferInstance)
  obtain ⟨Q, ⟨eQ⟩, hQ⟩ := hL i T M
  let φ := representingIso (restrictIso e (sigmaOverι V i) ≪≫
    pointFiberPresheafIsoOfChartIso f (CoproductChartBundle.bundleIso f V L i) M) eQ
  have hsm : Smooth (restrictScheme e (sigmaOverι V i)).hom := by
    rw [← Over.w φ.hom]
    infer_instance
  exact hsm

/-- Pulling a restricted family back along a point is pulling the original
family back along the composite point. -/
def residueBundleCompIso {U V W : Over S} (L : LineBundle ((relativeSpace f).obj U))
    (j : V ⟶ U) (a : W ⟶ V) :
    (LineBundle.pullback ((relativeSpace f).map (a ≫ j))).obj L ≅
      (LineBundle.pullback ((relativeSpace f).map a)).obj (restrictBundle f L j) :=
  eqToIso (by rw [Functor.map_comp]) ≪≫
    ((LineBundle.pullbackComp ((relativeSpace f).map a) ((relativeSpace f).map j)).app L).symm

end Coproduct

section ChartPoint

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  {U : Over (Spec (CommRingCat.of R))} (L : LineBundle ((relativeSpace f).obj U))
  {B : Type u} [CommRing B] [Algebra R B]
  {M : LineBundle ((relativeSpace f).obj (affineBase R B))}
  {P : Over (affineBase R B).left}

/-- A chart point over a field-valued point `φ` of an affine test, with an
isomorphism to the pulled-back test bundle, lies in the image of every
representing scheme. -/
theorem mem_range_of_chartPoint
    (e : (AlgebraicSpace.schemeYoneda (affineBase R B).left).obj P ≅
      pointFiberPresheaf f L M)
    {K : Type u} [Field K] [Algebra R K] (φ : B →ₐ[R] K)
    (a : Deformation.ArtinianTest.residueBase R K ⟶ U)
    (c : ArtinianChartVersality.residueBundle f L a ≅
      (LineBundle.pullback ((relativeSpace f).map (affineBaseMap φ))).obj M)
    (x : (Spec (CommRingCat.of K) : Scheme.{u})) :
    (affineBaseMap φ).left.base x ∈ Set.range P.hom.base := by
  let T := affineBase R B
  let g : Deformation.ArtinianTest.residueBase R K ⟶ T := affineBaseMap φ
  let Z : Over T.left := Over.mk g.left
  let ζ : (T.iteratedSliceBackward.obj Z).left ⟶ Deformation.ArtinianTest.residueBase R K :=
    Over.homMk (𝟙 _) (by simp [Z])
  have hζ : ζ ≫ g = (T.iteratedSliceBackward.obj Z).hom := by
    ext1
    simp [ζ, Z]
  let y : PointFiberPoints f L M Z :=
    ⟨ζ ≫ a, Langlands.CategoryTheory.PseudofunctorPointFiber.pullIso (F := relative f)
      (Core.isoMk c) ζ (ζ ≫ a) (T.iteratedSliceBackward.obj Z).hom rfl hζ⟩
  let h : Z ⟶ P := (pointEquiv e Z).symm y
  refine ⟨h.left.base x, ?_⟩
  rw [← Scheme.Hom.comp_apply, Over.w h]
  rfl

end ChartPoint

/-- A morphism to a Jacobson scheme with open image containing every closed
point is surjective. -/
lemma surjective_of_isOpenMap_of_closedPoints {W Y : Scheme.{u}} [JacobsonSpace Y]
    (g : W ⟶ Y) (ho : IsOpenMap g.base)
    (hc : ∀ y : Y, IsClosed ({y} : Set Y) → y ∈ Set.range g.base) :
    Surjective g := by
  refine ⟨fun y ↦ ?_⟩
  by_contra hy
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := (Set.range g.base)ᶜ) ⟨y, hy⟩
    ho.isOpen_range.isClosed_compl.isLocallyClosed
  exact hz (hc z hzc)

section Assembly

variable {R : Type u} [CommRing R]

/-- The field `R[x₁, …, xₙ]/𝔪` of a maximal ideal of a polynomial ring. -/
abbrev PointField (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) R)) : Type u :=
  MvPolynomial (Fin n) R ⧸ m.asIdeal

instance (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) R)) : Field (PointField n m) :=
  Ideal.Quotient.field m.asIdeal

instance (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) R)) :
    Algebra.FiniteType R (PointField n m) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R m.asIdeal)
    (Ideal.Quotient.mkₐ_surjective R m.asIdeal)

variable (X : Over (Spec (CommRingCat.of R)))

/-- The base change of `X` to the point `Spec (R[x₁, …, xₙ]/𝔪)`. -/
abbrev pointFiber (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) R)) : Scheme.{u} :=
  (relativeSpace X.hom).obj (Deformation.ArtinianTest.residueBase R (PointField n m))

instance [QuasiCompact X.hom] (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) R)) :
    CompactSpace (pointFiber X n m) :=
  inferInstanceAs (CompactSpace (Limits.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap R (PointField n m)))) X.hom : Scheme.{u}))

/-- Chart indices: a presented field point `R[x₁, …, xₙ]/𝔪` of finite type over
`R` and an actual unit-sheaf `H¹` class on the fibre of `X` there. -/
def ChartIndex [QuasiCompact X.hom] : Type u :=
  Σ (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) R)),
    Sheaf.H.{u} (UnitCechH1Comparison.unitSheaf (pointFiber X n m)) 1

variable {X}

/-- A line bundle on the fibre realizing the class of a chart index. -/
def ChartIndex.bundle [QuasiCompact X.hom] (i : ChartIndex X) :
    LineBundle (pointFiber X i.1 i.2.1) :=
  Classical.choose (LineBundle.unitCohomologyClass_surjective i.2.2)

lemma ChartIndex.unitCohomologyClass_bundle [QuasiCompact X.hom] (i : ChartIndex X) :
    i.bundle.unitCohomologyClass = i.2.2 :=
  Classical.choose_spec (LineBundle.unitCohomologyClass_surjective i.2.2)

/-- The field point of a polynomial presentation lying over a maximal ideal. -/
lemma exists_pointField_base_eq {B : Type u} [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] (y : PrimeSpectrum B) (hy : y.asIdeal.IsMaximal) :
    ∃ (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) R)) (φ : B →ₐ[R] PointField n m),
      ∀ x : (Spec (CommRingCat.of (PointField n m)) : Scheme.{u}),
        (affineBaseMap φ).left.base x = y := by
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    ‹Algebra.FiniteType R B›
  let m : MaximalSpectrum (MvPolynomial (Fin n) R) :=
    ⟨Ideal.comap π y.asIdeal, Ideal.comap_isMaximal_of_surjective π hπ⟩
  let φ : B →ₐ[R] PointField n m :=
    AlgHom.liftOfSurjective π hπ (Ideal.Quotient.mkₐ R m.asIdeal) (by
      intro a ha
      rw [RingHom.mem_ker] at ha ⊢
      change Ideal.Quotient.mk m.asIdeal a = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      change π a ∈ y.asIdeal
      change π a = 0 at ha
      rw [ha]
      exact y.asIdeal.zero_mem)
  have hker : RingHom.ker φ.toRingHom = y.asIdeal := by
    ext b
    obtain ⟨a, rfl⟩ := hπ b
    rw [RingHom.mem_ker]
    change AlgHom.liftOfSurjective π hπ (Ideal.Quotient.mkₐ R m.asIdeal) _ (π a) = 0 ↔ _
    rw [AlgHom.liftOfSurjective_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    rfl
  refine ⟨n, m, φ, fun x ↦ ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap φ.toRingHom (x : PrimeSpectrum (PointField n m)).asIdeal = y.asIdeal
  refine (hy.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
  rw [← hker]
  intro b hb
  rw [RingHom.mem_ker] at hb
  rw [Ideal.mem_comap, hb]
  exact zero_mem _

end Assembly

open Deformation in
/-- Smooth charts through all finite-type field points give a smooth surjective
scheme atlas locally of finite type. -/
theorem finiteTypePicardStackAtlas_of_pointSmoothCharts
    (h : FiniteTypePointSmoothChartStatement.{u}) :
    FiniteTypePicardStackAtlasStatement.{u} := by
  intro R _ _ X hp hf
  have : IsProper X.hom := hp
  have : Flat X.hom := hf
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have : LocallyOfFinitePresentation X.hom := inferInstance
  have : IsJacobsonRing R := by
    have := NoetherianApproximation.isJacobsonRing_int
    exact isJacobsonRing_of_finiteType (A := ℤ)
  choose V Lc p hV hL hpL using fun i : ChartIndex X ↦
    h R X hp hf (PointField i.1 i.2.1) i.bundle
  have : ∀ i, LocallyOfFiniteType (V i).hom := hV
  let L := CoproductChartBundle.bundle X.hom V Lc
  have hsm : HasSmoothPointFibers X.hom L :=
    coproductChart_hasSmoothPointFibers X.hom V Lc hL (fun T M ↦ by
      obtain ⟨_, e, -, -⟩ := hasAffinePointFiberSchemes X.hom (sigmaOver V) T L M
      exact ⟨_, e⟩)
  refine ⟨sigmaOver V, L, inferInstance,
    isSmoothSurjectivePresentation_of_finiteTypeAffine X.hom L (fun B _ _ _ M ↦ ?_)⟩
  obtain ⟨P, ⟨e⟩, hP⟩ := hsm (affineBase R B) M
  refine ⟨PointFiberProperty.of_exists e hP, PointFiberProperty.of_exists e ?_⟩
  have : Smooth P.hom := hP
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := R)
  have : JacobsonSpace (affineBase R B).left :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of B)))
  refine surjective_of_isOpenMap_of_closedPoints P.hom P.hom.isOpenMap (fun y hy ↦ ?_)
  have hy' : (y : PrimeSpectrum B).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (y : PrimeSpectrum B)).mp hy
  obtain ⟨n, m, φ, hφ⟩ := exists_pointField_base_eq (y : PrimeSpectrum B) hy'
  let N : LineBundle (pointFiber X n m) :=
    (LineBundle.pullback ((relativeSpace X.hom).map (affineBaseMap φ))).obj M
  let i : ChartIndex X := ⟨n, m, N.unitCohomologyClass⟩
  have hN : Nonempty (i.bundle ≅ N) :=
    (LineBundle.unitCohomologyClass_eq_iff_iso i.bundle N).mp i.unitCohomologyClass_bundle
  let c : ArtinianChartVersality.residueBundle X.hom L (p i ≫ sigmaOverι V i) ≅
      (LineBundle.pullback ((relativeSpace X.hom).map (affineBaseMap φ))).obj M :=
    residueBundleCompIso X.hom L (sigmaOverι V i) (p i) ≪≫
      (LineBundle.pullback ((relativeSpace X.hom).map (p i))).mapIso
        (CoproductChartBundle.bundleIso X.hom V Lc i) ≪≫ (hpL i).some ≪≫ hN.some
  let x : (Spec (CommRingCat.of (PointField n m)) : Scheme.{u}) :=
    (⊥ : PrimeSpectrum (PointField n m))
  rw [← hφ x]
  exact mem_range_of_chartPoint X.hom L e φ (p i ≫ sigmaOverι V i) c x

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
