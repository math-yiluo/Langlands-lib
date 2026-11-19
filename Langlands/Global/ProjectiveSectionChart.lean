import Langlands.AlgebraicGeometry.ProjectiveSpace.PointLines
import Langlands.AlgebraicGeometry.ProjectiveSpace.RationalPointZeros
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedTransport
import Langlands.GroupScheme.HomogeneousQuotientRationalPoints
import Langlands.Global.RationalFunctionHeight
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Algebraic sections on projective affine charts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped Topology

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Langlands.Global

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F : Type u} [Field F] {m : ℕ} {Q X : Over (Spec (CommRingCat.of F))}

private abbrev chartRing (j : Fin (m + 1)) :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) F)
    (MvPolynomial.X j)

local instance chartAlgebra (j : Fin (m + 1)) : Algebra F (chartRing (F := F) j) :=
  AlgebraicGeometry.ProjSpace.algebraAway F m j

private abbrev chartInclusion (j : Fin (m + 1)) :
    Spec (CommRingCat.of (chartRing (F := F) j)) ⟶ ProjectiveSpace F m :=
  (ProjectiveSpace.affineOpenCover F m).openCover.f j

private abbrev chartTarget (j : Fin (m + 1)) : Over (Spec (CommRingCat.of F)) :=
  ringTest F (chartRing (F := F) j)

variable (e : Q.left ⟶ ProjectiveSpace F m)

/-- The preimage of the standard projective coordinate chart in a scheme over the field. -/
def projectiveChartPreimage (j : Fin (m + 1)) : Q.left.Opens :=
  e ⁻¹ᵁ (chartInclusion (F := F) j).opensRange

private abbrev chartSource (j : Fin (m + 1)) :=
  openOver F Q (projectiveChartPreimage e j)

private abbrev chartSourceι (j : Fin (m + 1)) :
    chartSource e j ⟶ Q := openOverι F Q (projectiveChartPreimage e j)

private def chartIso (j : Fin (m + 1)) :
    Spec (CommRingCat.of (chartRing (F := F) j)) ≅
      (chartInclusion (F := F) j).opensRange.toScheme :=
  IsOpenImmersion.isoOfRangeEq (chartInclusion (F := F) j)
    (chartInclusion (F := F) j).opensRange.ι Subtype.range_coe.symm

private def chartProjectionMap (j : Fin (m + 1)) :
    (chartSource e j).left ⟶ Spec (CommRingCat.of (chartRing (F := F) j)) :=
  (e ∣_ (chartInclusion (F := F) j).opensRange) ≫ (chartIso j).inv

private theorem chartProjectionMap_fac (j : Fin (m + 1)) :
    chartProjectionMap e j ≫ chartInclusion j = (chartSourceι e j).left ≫ e := by
  unfold chartProjectionMap chartIso
  rw [Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac, morphismRestrict_ι]
  rfl

variable [IsClosedImmersion e]

private instance chartProjectionMap_closed (j : Fin (m + 1)) :
    IsClosedImmersion (chartProjectionMap e j) := by
  unfold chartProjectionMap
  infer_instance

private instance chartSource_affine (j : Fin (m + 1)) :
    IsAffine (chartSource e j).left :=
  isAffine_of_isAffineHom (chartProjectionMap e j)

private def chartProjection
    (he : e ≫ projectiveSpaceToSpec F m = Q.hom) (j : Fin (m + 1)) :
    chartSource e j ⟶ chartTarget j := by
  refine Over.homMk (chartProjectionMap e j) ?_
  have hchart : chartInclusion (F := F) j ≫ projectiveSpaceToSpec F m =
      Spec.map (CommRingCat.ofHom (algebraMap F (chartRing (F := F) j))) :=
    ProjectiveSpace.affineOpenCover_comp_toSpec F m j
  change chartProjectionMap e j ≫ Spec.map
      (CommRingCat.ofHom (algebraMap F (chartRing (F := F) j))) = _
  rw [← hchart, ← Category.assoc, chartProjectionMap_fac, Category.assoc, he]
  rfl

omit [IsClosedImmersion e] in
/-- A quotient section on a basic open inside the preimage of a standard projective chart. -/
structure ProjectiveSectionChart (q : X ⟶ Q) where
  index : Fin (m + 1)
  cut : Γ((chartSource e index).left, ⊤)
  lift : openOver F (chartSource e index) ((chartSource e index).left.basicOpen cut) ⟶ X
  fac : lift ≫ q =
    openOverι F (chartSource e index) ((chartSource e index).left.basicOpen cut) ≫
      chartSourceι e index

namespace ProjectiveSectionChart

variable {e} {q : X ⟶ Q} (D : ProjectiveSectionChart e q)

/-- The domain of the section as an affine open scheme over the field. -/
def domain : Over (Spec (CommRingCat.of F)) :=
  openOver F (chartSource e D.index) ((chartSource e D.index).left.basicOpen D.cut)

private abbrev domainι : D.domain ⟶ chartSource e D.index :=
  openOverι F (chartSource e D.index) _

/-- The open inclusion of the section's domain into the quotient. -/
def inclusion : D.domain ⟶ Q :=
  D.domainι ≫ chartSourceι e D.index

instance : IsOpenImmersion D.inclusion.left := by
  change IsOpenImmersion (((chartSource e D.index).left.basicOpen D.cut).ι ≫
    (projectiveChartPreimage e D.index).ι)
  infer_instance

instance : IsAffine D.domain.left := by
  let : IsAffine ((chartSource e D.index).left.basicOpen D.cut) :=
    (isAffineOpen_top _).basicOpen _
  unfold domain
  infer_instance

omit [IsClosedImmersion e] in
theorem lift_comp : D.lift ≫ q = D.inclusion :=
  D.fac

/-- A rational point in the open image of the section's domain lifts to that domain. -/
def pointLift (x : RationalPoint F Q)
    (hx : x.left (IsLocalRing.closedPoint F) ∈ D.inclusion.left.opensRange) :
    RationalPoint F D.domain := by
  have hx' : (rationalPointEquiv F Q x).left (IsLocalRing.closedPoint F) ∈
      D.inclusion.left.opensRange := by
    rw [rationalPointEquiv_left]
    exact hx
  have hr := (range_subset_open_iff_closedPoint F Q F D.inclusion.left.opensRange
    (rationalPointEquiv F Q x)).mpr hx'
  rw [rationalPointEquiv_left] at hr
  have hl (l : Spec (CommRingCat.of F) ⟶ D.domain.left)
      (hl : l ≫ D.inclusion.left = x.left) : l ≫ D.domain.hom = 𝟙 _ := by
    rw [← Over.w D.inclusion, ← Category.assoc, hl, Over.w x]
    rfl
  exact Over.homMk (IsOpenImmersion.lift D.inclusion.left x.left hr)
    (hl _ (IsOpenImmersion.lift_fac _ _ _))

omit [IsClosedImmersion e] in
theorem pointLift_comp (x : RationalPoint F Q)
    (hx : x.left (IsLocalRing.closedPoint F) ∈ D.inclusion.left.opensRange) :
    D.pointLift x hx ≫ D.inclusion = x :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

private theorem exists_at_point
    (he : e ≫ projectiveSpaceToSpec F m = Q.hom)
    (x : RationalPoint F Q) (V : Q.left.Opens) (s : openOver F Q V ⟶ X)
    (hx : x.left (IsLocalRing.closedPoint F) ∈ V) (hs : s ≫ q = openOverι F Q V) :
    ∃ D : ProjectiveSectionChart e q,
      x.left (IsLocalRing.closedPoint F) ∈ D.inclusion.left.opensRange := by
  have hbase : (x.left ≫ e) ≫ projectiveSpaceToSpec F m = 𝟙 _ := by
    rw [Category.assoc, he, Over.w x]
    rfl
  obtain ⟨i, φ, hφ⟩ := ProjectiveSpace.exists_chartPoint m (x.left ≫ e) hbase
  have hxi : x.left (IsLocalRing.closedPoint F) ∈ projectiveChartPreimage e i := by
    change e (x.left (IsLocalRing.closedPoint F)) ∈ Set.range (chartInclusion i)
    rw [← Scheme.Hom.comp_apply, ← hφ]
    exact ⟨_, rfl⟩
  let xW := Langlands.GroupScheme.HomogeneousQuotient.rationalPointInOpen F
    (projectiveChartPreimage e i) x hxi
  have hxW : xW ≫ chartSourceι e i = x :=
    Langlands.GroupScheme.HomogeneousQuotient.rationalPointInOpen_comp F _ _ _
  let W := (chartSourceι e i).left ⁻¹ᵁ V
  have hxW' : xW.left (IsLocalRing.closedPoint F) ∈ W := by
    change (chartSourceι e i).left (xW.left (IsLocalRing.closedPoint F)) ∈ V
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hxW]
    exact hx
  obtain ⟨f, hfV, hxf⟩ := (isAffineOpen_top (chartSource e i).left).exists_basicOpen_le
    (V := W) ⟨_, hxW'⟩ (by trivial)
  let inc : openOver F (chartSource e i) ((chartSource e i).left.basicOpen f) ⟶ Q :=
    openOverι F (chartSource e i) _ ≫ chartSourceι e i
  have hrange : Set.range inc.left ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨inc.left z, ?_⟩, rfl⟩
    change (chartSourceι e i).left z.val ∈ V
    exact hfV z.property
  let t : openOver F (chartSource e i) ((chartSource e i).left.basicOpen f) ⟶
      openOver F Q V :=
    Over.homMk (IsOpenImmersion.lift V.ι inc.left hrange) (by
      change _ ≫ V.ι ≫ Q.hom = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w inc)
  have ht : t ≫ openOverι F Q V = inc :=
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  refine ⟨⟨i, f, t ≫ s, by rw [Category.assoc, hs, ht]⟩, ?_⟩
  change x.left (IsLocalRing.closedPoint F) ∈ Set.range inc.left
  refine ⟨⟨xW.left (IsLocalRing.closedPoint F), hxf⟩, ?_⟩
  change (xW ≫ chartSourceι e i).left (IsLocalRing.closedPoint F) = _
  rw [hxW]

/-- A finite family of such charts covers the rational points when the quotient
is Noetherian and has sections at its rational points. -/
theorem exists_finite_cover [IsNoetherian Q.left]
    (he : e ≫ projectiveSpaceToSpec F m = Q.hom)
    (hs : ∀ x : RingPoint F Q F, ∃ (V : Q.left.Opens) (s : openOver F Q V ⟶ X),
      Set.range x.left ⊆ V ∧ s ≫ q = openOverι F Q V) :
    ∃ t : Finset (ProjectiveSectionChart e q), ∀ x : RationalPoint F Q,
      ∃ D ∈ t, x.left (IsLocalRing.closedPoint F) ∈ D.inclusion.left.opensRange := by
  classical
  have hcovered (x : RationalPoint F Q) :
      ∃ D : ProjectiveSectionChart e q,
        x.left (IsLocalRing.closedPoint F) ∈ D.inclusion.left.opensRange := by
    obtain ⟨V, s, hx, hsec⟩ := hs (rationalPointEquiv F Q x)
    rw [rationalPointEquiv_left] at hx
    exact exists_at_point he x V s (hx ⟨_, rfl⟩) hsec
  let points : Set Q.left := Set.range fun x : RationalPoint F Q =>
    x.left (IsLocalRing.closedPoint F)
  obtain ⟨t, ht⟩ := (TopologicalSpace.NoetherianSpace.isCompact points).elim_finite_subcover
    (fun D : ProjectiveSectionChart e q => (D.inclusion.left.opensRange : Set Q.left))
    (fun D => D.inclusion.left.opensRange.2) (by
      rintro _ ⟨x, rfl⟩
      exact Set.mem_iUnion.mpr (hcovered x))
  refine ⟨t, fun x => ?_⟩
  obtain ⟨D, hDt, hxD⟩ := Set.mem_iUnion₂.mp (ht ⟨x, rfl⟩)
  exact ⟨D, hDt, hxD⟩

private theorem ratio_eq_of_hasCoordinates
    (j : Fin (m + 1)) (φ : chartRing (F := F) j →ₐ[F] F) (a : Fin (m + 1) → F)
    (ha : ProjectiveSpace.HasCoordinates
      (ProjectiveSpace.chartPoint m j φ (IsLocalRing.closedPoint F)) a) (i : Fin (m + 1)) :
    φ (AlgebraicGeometry.ProjSpace.ratio F m j i) = a i / a j := by
  have hratio (l : Fin (m + 1)) : φ (AlgebraicGeometry.ProjSpace.ratio F m j l) * a j = a l := by
    let ℓ : (Fin (m + 1) → F) →ₗ[F] F :=
      LinearMap.proj l - φ (AlgebraicGeometry.ProjSpace.ratio F m j l) • LinearMap.proj j
    let f := ProjectiveSpace.linearFormPolynomialEquiv F m ℓ
    have hz : ℓ (ProjectiveSpace.chartCoordinates m j φ) = 0 := by
      change ProjectiveSpace.chartCoordinates m j φ l -
        φ (AlgebraicGeometry.ProjSpace.ratio F m j l) * ProjectiveSpace.chartCoordinates m j φ j = 0
      rw [ProjectiveSpace.chartCoordinates_self]
      simp [ProjectiveSpace.chartCoordinates]
    have hm := (ProjectiveSpace.chartPoint_linearForm_mem_iff m j φ ℓ).mpr hz
    have hhomog : (f : ProjectiveCoordinateRing F m).IsHomogeneous 1 :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mp f.property
    have heval := (ha 1 f hhomog).mp hm
    rw [ProjectiveSpace.eval_linearFormPolynomialEquiv F m ℓ] at heval
    exact (sub_eq_zero.mp heval).symm
  have hj : a j ≠ 0 := by
    intro h
    apply ha.ne_zero
    funext l
    rw [← hratio l, h, mul_zero]
    rfl
  exact (eq_div_iff hj).mpr (hratio i)

private theorem specMap_rationalPointAlgebraHom
    {A : Type u} [CommRing A] [Algebra F A] (p : RationalPoint F (ringTest F A)) :
    Spec.map (CommRingCat.ofHom ((rationalPointAlgebraHom F (ringTest F A) p).comp
      (spectrumCoordinateAlgEquiv F A).symm.toAlgHom).toRingHom) = p.left := by
  have hp := affineSchemePointEquiv_spec F (X := ringTest F A) F
    (rationalPointEquiv F (ringTest F A) p)
  rw [rationalPointEquiv_left] at hp
  change Spec.map (CommRingCat.ofHom (rationalPointAlgebraHom F (ringTest F A) p).toRingHom) =
    p.left ≫ (Spec (CommRingCat.of A)).isoSpec.hom at hp
  change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    CommRingCat.ofHom (rationalPointAlgebraHom F (ringTest F A) p).toRingHom) = p.left
  rw [Spec.map_comp, hp, ← Scheme.isoSpec_Spec_inv, Category.assoc, Iso.hom_inv_id, Category.comp_id]

open Height in
/-- A fixed regular function evaluated on lifts through a fixed chart section
has polynomial height growth in the supplied homogeneous coordinates. -/
theorem regularFunction_mem_polynomialHeightBounded
    [NumberField F] [IsAffine X.left] {I : Type*}
    (he : e ≫ projectiveSpaceToSpec F m = Q.hom)
    (x : I → RationalPoint F Q)
    (hx : ∀ i, (x i).left (IsLocalRing.closedPoint F) ∈ D.inclusion.left.opensRange)
    (a : I → Fin (m + 1) → F)
    (ha : ∀ i, ProjectiveSpace.HasCoordinates
      (((x i).left ≫ e) (IsLocalRing.closedPoint F)) (a i))
    (f : AffineCoordinateRing F X) :
    (fun i => rationalPointAlgebraHom F X (D.pointLift (x i) (hx i) ≫ D.lift) f) ∈
      polynomialHeightBounded (fun i => mulHeight (a i)) (fun i => one_le_mulHeight (a i)) := by
  let A := AffineCoordinateRing F (chartSource e D.index)
  let B := AffineCoordinateRing F D.domain
  let : Algebra A B := inferInstanceAs (Algebra Γ((chartSource e D.index).left, ⊤)
    Γ(((chartSource e D.index).left.basicOpen D.cut), ⊤))
  let : IsScalarTower F A B :=
    IsScalarTower.of_algebraMap_eq' (affineCoordinateMap_natural F D.domainι).symm
  let : IsLocalization.Away (show A from D.cut) B :=
    Γ_restrict_isLocalization (chartSource e D.index).left D.cut
  let π := chartProjection e he D.index
  have : IsClosedImmersion π.left := by
    change IsClosedImmersion (chartProjectionMap e D.index)
    infer_instance
  let φ : chartRing (F := F) D.index →ₐ[F] A := (affineCoordinatePullback F π).comp
    (spectrumCoordinateAlgEquiv F (chartRing (F := F) D.index)).symm.toAlgHom
  have hs : Function.Surjective φ :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine π.left).2.comp
      (spectrumCoordinateAlgEquiv F (chartRing (F := F) D.index)).symm.surjective
  let ev (i : I) : B →ₐ[F] F := rationalPointAlgebraHom F D.domain (D.pointLift (x i) (hx i))
  let φev (i : I) : chartRing (F := F) D.index →ₐ[F] F :=
    (ev i).comp ((Algebra.algHom F A B).comp φ)
  have hfac (i : I) : ProjectiveSpace.chartPoint m D.index (φev i) = (x i).left ≫ e := by
    let p : RationalPoint F (chartTarget D.index) := D.pointLift (x i) (hx i) ≫ D.domainι ≫ π
    have hφ : φev i = (rationalPointAlgebraHom F (chartTarget D.index) p).comp
        (spectrumCoordinateAlgEquiv F (chartRing (F := F) D.index)).symm.toAlgHom := by
      ext r
      simp only [φev, φ, AlgHom.comp_apply, ev]
      change rationalPointAlgebraHom F D.domain _ (affineCoordinatePullback F D.domainι
        (affineCoordinatePullback F π _)) = _
      rw [rationalPointAlgebraHom_pullback, rationalPointAlgebraHom_pullback, Category.assoc]
      rfl
    rw [hφ, ProjectiveSpace.chartPoint, specMap_rationalPointAlgebraHom]
    change (D.pointLift (x i) (hx i)).left ≫ D.domainι.left ≫
      chartProjectionMap e D.index ≫ chartInclusion D.index = _
    calc
      _ = ((D.pointLift (x i) (hx i)).left ≫
          (D.domainι.left ≫ (chartSourceι e D.index).left)) ≫ e := by
        simp only [chartProjectionMap_fac, Category.assoc]
      _ = _ := by
        change (D.pointLift (x i) (hx i) ≫ D.inclusion).left ≫ e = _
        rw [D.pointLift_comp]
  have hbase (b : A) :
      (fun i => ev i (algebraMap A B b)) ∈
        polynomialHeightBounded (fun i => mulHeight (a i)) (fun i => one_le_mulHeight (a i)) := by
    obtain ⟨r, rfl⟩ := hs b
    change (fun i => φev i r) ∈
      polynomialHeightBounded (fun i => mulHeight (a i)) (fun i => one_le_mulHeight (a i))
    apply mem_polynomialHeightBounded_of_adjoin_eq_top φev
      (AlgebraicGeometry.ProjSpace.adjoin_range_ratio F m D.index) _ r
    rintro _ ⟨l, rfl⟩
    refine ⟨1, zero_lt_one, 1, fun i => ?_⟩
    have hc := ha i
    rw [← hfac i] at hc
    change mulHeight₁ (φev i (AlgebraicGeometry.ProjSpace.ratio F m D.index l)) ≤
      1 * mulHeight (a i) ^ (1 : ℕ)
    rw [ratio_eq_of_hasCoordinates D.index (φev i) (a i) hc, pow_one, one_mul]
    exact mulHeight₁_div_le_mulHeight (a i) l D.index
  have hf := mem_polynomialHeightBounded_away (show A from D.cut) ev hbase
    (affineCoordinatePullback F D.lift f)
  have heq : (fun i => ev i (affineCoordinatePullback F D.lift f)) =
      fun i => rationalPointAlgebraHom F X (D.pointLift (x i) (hx i) ≫ D.lift) f := by
    funext i
    exact rationalPointAlgebraHom_pullback F D.lift (D.pointLift (x i) (hx i)) f
  rwa [heq] at hf

end ProjectiveSectionChart

end Langlands.Global
