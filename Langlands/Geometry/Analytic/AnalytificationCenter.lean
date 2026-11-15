import Langlands.Geometry.Analytic.AffineAnalytificationSeminorm
import Langlands.Geometry.Analytic.SchemeAnalytificationSpace

/-! # Berkovich's center map from an analytification to its scheme -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open Set Topology PresentedAffinoidAlgebra AnalyticAffineSpace

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-- The kernel of the multiplicative seminorm of a point: the elements of `A` at which
the seminorm of the point vanishes. -/
def kernel (x : Space K P) : Ideal A where
  carrier := {a | pointSeminorm K P x a = 0}
  zero_mem' := map_zero (pointSeminorm K P x)
  add_mem' {a b} ha hb := by
    change pointSeminorm K P x a = 0 at ha
    change pointSeminorm K P x b = 0 at hb
    change pointSeminorm K P x (a + b) = 0
    apply le_antisymm _ (apply_nonneg _ _)
    simpa only [ha, hb, add_zero] using map_add_le_add (pointSeminorm K P x) a b
  smul_mem' c a ha := by
    change pointSeminorm K P x a = 0 at ha
    change pointSeminorm K P x (c * a) = 0
    rw [map_mul, ha, mul_zero]

@[simp]
theorem mem_kernel (x : Space K P) (a : A) :
    a ∈ kernel K P x ↔ pointSeminorm K P x a = 0 :=
  Iff.rfl

/-- The kernel of a multiplicative seminorm is prime: it misses `1` because the
seminorm takes the value `1` there, and it is closed under factors of products
because the seminorm is multiplicative. -/
theorem kernel_isPrime (x : Space K P) : (kernel K P x).IsPrime where
  ne_top' h := by
    have h1 : (1 : A) ∈ kernel K P x := h ▸ Submodule.mem_top
    rw [mem_kernel, map_one] at h1
    exact one_ne_zero h1
  mem_or_mem' {a b} h := by
    rw [mem_kernel, map_mul] at h
    exact mul_eq_zero.1 h

/-- Berkovich's center map on the affine analytification: a point goes to the prime
ideal of `A` on which its seminorm vanishes. -/
def center (x : Space K P) : PrimeSpectrum A :=
  ⟨kernel K P x, kernel_isPrime K P x⟩

@[simp]
theorem center_asIdeal (x : Space K P) : (center K P x).asIdeal = kernel K P x :=
  rfl

/-- The center of a point lies in the basic open set of `a` exactly when the seminorm of
the point does not vanish at `a`. -/
theorem center_mem_basicOpen (x : Space K P) (a : A) :
    center K P x ∈ PrimeSpectrum.basicOpen a ↔ pointSeminorm K P x a ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen, center_asIdeal, mem_kernel]

/-- The center map is continuous for the Zariski topology. -/
theorem continuous_center : Continuous (center K P) := by
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff]
  rintro _ ⟨a, rfl⟩
  have e : center K P ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) =
      (fun x : Space K P => pointSeminorm K P x a) ⁻¹' {0}ᶜ := by
    ext x
    exact center_mem_basicOpen K P x a
  rw [e]
  exact isOpen_compl_singleton.preimage (continuous_pointSeminorm_apply K P a)

/-- The center map as a continuous map to the prime spectrum. -/
def centerMap : C(Space K P, PrimeSpectrum A) :=
  ⟨center K P, continuous_center K P⟩

@[simp]
theorem centerMap_apply (x : Space K P) : centerMap K P x = center K P x :=
  rfl

variable {B : Type w} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-- The seminorm of the image of a point under the map induced by `f` is the seminorm
of the point composed with `f`. -/
theorem pointSeminorm_baseMap (y : Space K Q) (a : A) :
    pointSeminorm K P (baseMap K P Q f y) a = pointSeminorm K Q y (f a) := by
  obtain ⟨k, x, rfl⟩ := exists_chart K Q y
  rw [baseMap_chart, pointSeminorm_chart, pointSeminorm_chart, chartSeminorm_apply,
    chartSeminorm_apply]
  change x (chartMap K P Q f k
    (PolynomialLocus.algebraMap P (polyradius K P.arity (level K P Q f k)) a)) = _
  rw [chartMap_algebraMap]

theorem kernel_baseMap (y : Space K Q) :
    kernel K P (baseMap K P Q f y) = (kernel K Q y).comap f := by
  ext a
  rw [Ideal.mem_comap, mem_kernel, mem_kernel, pointSeminorm_baseMap]

/-- The center map is natural: the center of the image of a point is the preimage
under `f` of the center of the point. -/
theorem center_baseMap (y : Space K Q) :
    center K P (baseMap K P Q f y) = PrimeSpectrum.comap (f : A →+* B) (center K Q y) :=
  PrimeSpectrum.ext (kernel_baseMap K P Q f y)

end Langlands.Analytic.AffineAnalytification

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

/-- The open immersion into `X` of the spectrum of the global sections of an affine open
`U`: the inverse of the canonical isomorphism `U ≅ Spec Γ(U, ⊤)` followed by the
inclusion of `U`. -/
def affineOpenMap (U : X.affineOpens) : Spec Γ((U : X.Opens), ⊤) ⟶ X :=
  (U : X.Opens).toScheme.isoSpec.inv ≫ (U : X.Opens).ι

/-- The center of a point of the analytification of an affine open `U`, as a point of
`Spec Γ(U, ⊤)`: the prime ideal of global sections of `U` on which its seminorm
vanishes. -/
def localCenterPoint (U : X.affineOpens) (y : LocalSpace K f U) : Spec Γ((U : X.Opens), ⊤) :=
  (AffineAnalytification.center K (chartPresentation K f U) y :
    PrimeSpectrum (CoordinateRing (structureMap f U)))

theorem continuous_localCenterPoint (U : X.affineOpens) :
    Continuous (localCenterPoint K f U) :=
  AffineAnalytification.continuous_center K (chartPresentation K f U)

/-- The centers of a point of the analytification of `V` and of its image in the
analytification of a larger affine open `U` correspond under restriction of global
sections. -/
theorem localCenterPoint_localMap {U V : X.affineOpens} (h : (V : X.Opens) ≤ U)
    (y : LocalSpace K f V) :
    localCenterPoint K f U (localMap K f h y) =
      Spec.map (X.homOfLE h).appTop (localCenterPoint K f V y) :=
  AffineAnalytification.center_baseMap K _ _ (restriction f h) y

/-- The center map on the analytification of an affine open `U`, with values in `X`:
the center of a point, as a point of `Spec Γ(U, ⊤)`, sent to `X`. -/
def localCenter (U : X.affineOpens) : C(LocalSpace K f U, X) :=
  ⟨fun y => affineOpenMap U (localCenterPoint K f U y),
    (affineOpenMap U).continuous.comp (continuous_localCenterPoint K f U)⟩

theorem localCenter_apply (U : X.affineOpens) (y : LocalSpace K f U) :
    localCenter K f U y = affineOpenMap U (localCenterPoint K f U y) :=
  rfl

/-- The local center maps are compatible with the maps induced by inclusions of
affine opens. -/
theorem localCenter_localMap {U V : X.affineOpens} (h : (V : X.Opens) ≤ U)
    (y : LocalSpace K f V) :
    localCenter K f U (localMap K f h y) = localCenter K f V y := by
  rw [localCenter_apply, localCenter_apply, localCenterPoint_localMap, affineOpenMap,
    affineOpenMap, ← Scheme.Hom.comp_apply, Scheme.isoSpec_inv_naturality_assoc, X.homOfLE_ι]

/-- Berkovich's map `π : X^an → X` on the glued analytification space: on the
analytification of each affine open it is the local center map. -/
def center : C(Space K f, X) :=
  desc K f (localCenter K f) (fun h y => localCenter_localMap K f h y)

@[simp]
theorem center_ι (U : X.affineOpens) (y : LocalSpace K f U) :
    center K f (ι K f U y) = localCenter K f U y :=
  rfl

/-- The center of a point coming from an affine open `U` lies in `U`. -/
theorem center_ι_mem (U : X.affineOpens) (y : LocalSpace K f U) :
    center K f (ι K f U y) ∈ (U : X.Opens) := by
  rw [center_ι, localCenter_apply, affineOpenMap, Scheme.Hom.comp_apply]
  exact ((U : X.Opens).toScheme.isoSpec.inv (localCenterPoint K f U y)).2

end Langlands.Analytic.SchemeAnalytification
