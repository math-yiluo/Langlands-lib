import Langlands.BruhatTits.IntegralModels.RootDepthKernelNoHigher
import Langlands.FieldTheory.HenselianSeparableIntegers
import Langlands.Geometry.Building.MultipliableRootGroupCoordinates
import Langlands.Geometry.Building.IntegerRootReflections
import Langlands.GroupScheme.Examples.SU3RootUnitaryCanonicalWeilPoints
import Langlands.GroupScheme.Examples.SU3RootUnitaryMaximalUnramified
import Langlands.GroupScheme.Examples.SU3RootRescaledJumps
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence

/-! # KP Lemma C.5.3 for multipliable roots, from valued unitary coordinates -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.LocalGalois.Separable

namespace Langlands.GroupScheme.SU3Root

/-! ### Normalizing the prolonged valuation on a separable tower -/

section SeparableTower

variable {k : Type u} [Field k]
  (v : Valuation k (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v)
  (hH : HenselianLocalRing v.valuationSubring)
  (E L : Type u) [Field E] [Field L] [Algebra k E] [Algebra E L] [Algebra k L]
  [IsScalarTower k E L] [FiniteDimensional k E] [Algebra.IsSeparable k E]
  [Algebra.IsQuadraticExtension E L] [Algebra.IsSeparable E L] [Algebra.IsSeparable k L]

/-- A positive scale `c` such that `c` times the prolonged value is integral on `E^×` and
takes the value `1` on `E`. -/
def towerScale : ℝ :=
  Classical.choose (FieldTheory.henselianSeparable_exists_integer_scale v hH E hv)

theorem towerScale_pos : 0 < towerScale v hv hH E :=
  (Classical.choose_spec (FieldTheory.henselianSeparable_exists_integer_scale v hH E hv)).1

theorem towerScale_spec :
    (∀ a : E, a ≠ 0 → ∃ m : ℤ, ∃ t : ℝ,
        FieldTheory.henselianSeparableAddValuation v hH E a = (t : WithTop ℝ) ∧
          towerScale v hv hH E * t = m) ∧
      ∃ ϖ : E, FieldTheory.henselianSeparableAddValuation v hH E ϖ =
        ((1 / towerScale v hv hH E : ℝ) : WithTop ℝ) :=
  (Classical.choose_spec (FieldTheory.henselianSeparable_exists_integer_scale v hH E hv)).2

/-- The prolonged valuation on `L`, rescaled by `towerScale` so that its values on `E^×`
form the group `ℤ`. -/
def towerNormalizedValuation : AddValuation L (WithTop ℝ) :=
  rescaleValuation (FieldTheory.henselianSeparableAddValuation v hH L) (towerScale v hv hH E)
    (towerScale_pos v hv hH E)

omit [Algebra E L] [IsScalarTower k E L] [Algebra.IsQuadraticExtension E L]
  [Algebra.IsSeparable E L] in
theorem towerNormalizedValuation_apply (x : L) :
    towerNormalizedValuation v hv hH E L x =
      scaleTop (towerScale v hv hH E) (FieldTheory.henselianSeparableAddValuation v hH L x) :=
  rfl

omit [FiniteDimensional k E] [Algebra.IsQuadraticExtension E L] [Algebra.IsSeparable E L] in
/-- The prolongations to `E` and to `L` are compatible. -/
theorem henselianSeparableAddValuation_tower (a : E) :
    FieldTheory.henselianSeparableAddValuation v hH L (algebraMap E L a) =
      FieldTheory.henselianSeparableAddValuation v hH E a :=
  FieldTheory.henselianSeparableAddValuation_algHom v hH L (IsScalarTower.toAlgHom k E L) a

omit [Algebra.IsQuadraticExtension E L] [Algebra.IsSeparable E L] in
theorem towerNormalizedValuation_algebraMap (a : E) :
    towerNormalizedValuation v hv hH E L (algebraMap E L a) =
      scaleTop (towerScale v hv hH E) (FieldTheory.henselianSeparableAddValuation v hH E a) := by
  rw [towerNormalizedValuation_apply, henselianSeparableAddValuation_tower]

private theorem scaleTop_nonneg_iff {c : ℝ} (hc : 0 < c) (x : WithTop ℝ) :
    0 ≤ scaleTop c x ↔ 0 ≤ x := by
  have h := (scaleTop_strictMono hc).le_iff_le (a := 0) (b := x)
  rwa [map_zero] at h

private theorem scaleTop_pos_iff {c : ℝ} (hc : 0 < c) (x : WithTop ℝ) :
    0 < scaleTop c x ↔ 0 < x := by
  have h := (scaleTop_strictMono hc).lt_iff_lt (a := 0) (b := x)
  rwa [map_zero] at h

/-- Over a henselian base with algebraically closed residue field, the normalized valuation
satisfies the hypotheses of the unitary lattice models: it is conjugation invariant, integral
on `E^×`, and takes the value `1/2`. -/
theorem towerNormalizedValuation_isRamified
    [IsAlgClosed (IsLocalRing.ResidueField v.valuationSubring)] :
    IsRamifiedQuadraticValuation E L (towerNormalizedValuation v hv hH E L) := by
  obtain ⟨hint, ϖ, hϖ⟩ := towerScale_spec v hv hH E
  have hc := towerScale_pos v hv hH E
  refine IsRamifiedQuadraticValuation.of_hasResidueQuadraticRoots (ϖ := ϖ) ?_ ?_ ?_ ?_
  · intro z
    rw [towerNormalizedValuation_apply, towerNormalizedValuation_apply]
    congr 1
    exact FieldTheory.henselianSeparableAddValuation_invariant v hH L
      ((conjugation E L).restrictScalars k) z
  · intro a ha
    obtain ⟨m, t, ht, hm⟩ := hint a ha
    refine ⟨m, ?_⟩
    rw [towerNormalizedValuation_algebraMap, ht, scaleTop_coe, hm]
  · rw [towerNormalizedValuation_algebraMap, hϖ, scaleTop_coe, mul_one_div_cancel hc.ne']
  · intro t n ht hn
    rw [towerNormalizedValuation_algebraMap, scaleTop_nonneg_iff hc] at ht hn
    obtain ⟨b, hb⟩ :=
      FieldTheory.henselianSeparable_exists_quadratic_approxRoot v hH E hv t n ht hn
    refine ⟨b, ?_⟩
    rw [towerNormalizedValuation_algebraMap, scaleTop_pos_iff hc]
    exact hb

omit [Algebra.IsQuadraticExtension E L] [Algebra.IsSeparable E L] in
/-- The ring of integers of `E` is the ring of integers for the normalized valuation. -/
theorem towerNormalizedValuation_isValuationIntegers :
    IsValuationIntegers (FieldTheory.henselianSeparableIntegers v hH E) E
      (towerNormalizedValuation v hv hH E L) := by
  intro a
  rw [towerNormalizedValuation_algebraMap, scaleTop_nonneg_iff (towerScale_pos v hv hH E),
    ← FieldTheory.mem_henselianSeparableIntegers]
  constructor
  · rintro ⟨b, rfl⟩
    exact b.2
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

end SeparableTower

/-! ### The filtration product at doubled central depth -/

namespace IsRamifiedQuadraticValuation

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {ω : AddValuation L (WithTop ℝ)} (hω : IsRamifiedQuadraticValuation K L ω)

/-- At central depth `2r` the central factor is absorbed, and `X(K)_r · Z(K)_{2r}` is the
filtration subgroup `{(u, v) | ω(v) ≥ 2r + μ}`. -/
theorem mem_filtrationProduct_double_iff (r : ℝ) (p : rationalParameters K L) :
    p ∈ hω.filtrationProduct r (2 * r) ↔
      ((2 * r + mu K L ω : ℝ) : WithTop ℝ) ≤ ω p.second := by
  have h2 : 2 * (r + mu K L ω / 2) = 2 * r + mu K L ω := by ring
  have hle : Parameters.centralFiltration ω hω.bar_eq (2 * r + mu K L ω) ≤
      Parameters.filtration ω hω.bar_eq (r + mu K L ω / 2) := by
    intro x hx
    rw [Parameters.mem_filtration, h2]
    exact hx.2
  rw [filtrationProduct, sup_eq_left.mpr hle, Parameters.mem_filtration, h2]

end IsRamifiedQuadraticValuation

end Langlands.GroupScheme.SU3Root

/-! ### Integral models of multipliable root filtration groups -/

namespace Langlands.Geometry.Building.ValuedUnitaryRootGroupCoordinates

open SU3Root SU3Root.IntegralChart BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

instance henselianSeparableIntegers_finite (E : Type u) [Field E]
    [Algebra (inertiaFixedField F) E] [FiniteDimensional (inertiaFixedField F) E]
    [Algebra.IsSeparable (inertiaFixedField F) E] :
    Module.Finite (MaximalUnramified.valuation F).valuationSubring
      (FieldTheory.henselianSeparableIntegers (MaximalUnramified.valuation F)
        (MaximalUnramified.valuationSubring_isHenselian F) E) :=
  FieldTheory.henselianSeparableIntegers_finite _ _ E (MaximalUnramified.valuation_surjective F)

instance henselianSeparableIntegers_free (E : Type u) [Field E]
    [Algebra (inertiaFixedField F) E] [FiniteDimensional (inertiaFixedField F) E]
    [Algebra.IsSeparable (inertiaFixedField F) E] :
    Module.Free (MaximalUnramified.valuation F).valuationSubring
      (FieldTheory.henselianSeparableIntegers (MaximalUnramified.valuation F)
        (MaximalUnramified.valuationSubring_isHenselian F) E) :=
  FieldTheory.henselianSeparableIntegers_free _ _ E (MaximalUnramified.valuation_surjective F)

variable {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))} [IsAffineHom G.X.hom]
  {B : MaximalUnramified.BuildingData F G} {a : relativeRoots B.i}
  (P : ValuedUnitaryRootGroupCoordinates B a)

/-- The ring of integers of the double-root field `E`. -/
abbrev integers : ValuationSubring P.base :=
  FieldTheory.henselianSeparableIntegers (MaximalUnramified.valuation F)
    (MaximalUnramified.valuationSubring_isHenselian F) P.base

/-- The scale normalizing the prolonged valuation on `E^×` to `ℤ`. -/
abbrev scale : ℝ :=
  towerScale (MaximalUnramified.valuation F) (MaximalUnramified.valuation_surjective F)
    (MaximalUnramified.valuationSubring_isHenselian F) P.base

/-- The valuation on the root field `L` normalized on the double-root field `E`. -/
abbrev normalizedValuation : AddValuation P.extension (WithTop ℝ) :=
  towerNormalizedValuation (MaximalUnramified.valuation F)
    (MaximalUnramified.valuation_surjective F) (MaximalUnramified.valuationSubring_isHenselian F)
    P.base P.extension

theorem normalizedValuation_isRamified :
    IsRamifiedQuadraticValuation P.base P.extension P.normalizedValuation :=
  haveI := MaximalUnramified.residueField_isAlgClosed F
  towerNormalizedValuation_isRamified _ _ _ _ _

theorem normalizedValuation_isValuationIntegers :
    IsValuationIntegers P.integers P.base P.normalizedValuation :=
  towerNormalizedValuation_isValuationIntegers _ _ _ _ _

/-- The restricted unitary group `R_{E/K} U_{L/E}`, in its canonical generic form over the
ring of integers. -/
abbrev weilGroup : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))) :=
  canonicalWeilGroup (MaximalUnramified.valuation F).valuationSubring (inertiaFixedField F)
    P.integers P.base P.extension

/-- The rational points of the restricted unitary group are the unitary parameters. -/
abbrev pointsEquiv : rationalPoints P.weilGroup ≃* rationalParameters P.base P.extension :=
  canonicalWeilRationalPointsEquiv (MaximalUnramified.valuation F).valuationSubring
    (inertiaFixedField F) P.integers P.base P.extension

/-- The value `a(y - origin)` of the root on the translation from the origin. -/
def depthShift (y : B.Apartment) : ℝ :=
  rootForm B.i a (y -ᵥ P.origin)

/-- The lattice depth `r' = c (r - a(y - origin)) - μ / 2` of the unitary lattice model
presenting `U_{a,y,r}`. -/
def latticeDepth (y : B.Apartment) (r : ℝ) : ℝ :=
  P.scale * (r - P.depthShift y) - mu P.base P.extension P.normalizedValuation / 2

/-- The canonical restricted unitary lattice model `R_{O_E/O} X_{r',2r'}`. -/
abbrev latticeModel (y : B.Apartment) (r : ℝ) :
    IntegralModel (MaximalUnramified.valuation F).valuationSubring (inertiaFixedField F)
      P.weilGroup :=
  P.normalizedValuation_isRamified.canonicalWeilLatticeModel
    (MaximalUnramified.valuation F).valuationSubring (inertiaFixedField F) P.integers P.base
    P.extension P.normalizedValuation_isValuationIntegers (P.latticeDepth y r)
    (2 * P.latticeDepth y r)

/-- The value of the root at `y` on the coordinate point of a unitary parameter. -/
theorem val_map_inclusion (y : B.Apartment) (g : rationalPoints P.weilGroup) :
    y.val a (rationalPoints.map P.inclusion g) =
      towerDepth (inertiaFixedField F) P.base P.extension (MaximalUnramified.valuation F)
          (MaximalUnramified.valuationSubring_isHenselian F) (P.pointsEquiv g) +
        ((P.depthShift y : ℝ) : WithTop ℝ) := by
  rw [IntegerValuationBuildingData.val_apply_eq_add B P.origin y a]
  congr 1
  calc P.origin.val a (rationalPoints.map P.inclusion g) =
        P.origin.val a (rationalPoints.map P.inclusion (P.pointsEquiv.symm (P.pointsEquiv g))) := by
          rw [MulEquiv.symm_apply_apply]
    _ = _ := P.depth (P.pointsEquiv g)

private theorem depth_iff {c : ℝ} (hc : 0 < c) (m d r : ℝ) (t : WithTop ℝ) :
    (((2 * (c * (r - d) - m / 2) + m : ℝ)) : WithTop ℝ) ≤ scaleTop c t ↔
      (r : WithTop ℝ) ≤ halfTop t + (d : WithTop ℝ) := by
  induction t with
  | top => simp
  | coe t =>
    rw [scaleTop_coe, halfTop_coe, ← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith

/-- Integral points of the lattice model are the points whose image lies in `U_{a,y,r}`. -/
theorem mem_integralPoints_latticeModel_iff (y : B.Apartment) (r : ℝ)
    (g : rationalPoints P.weilGroup) :
    g ∈ (P.latticeModel y r).integralPoints ↔
      (r : WithTop ℝ) ≤ y.val a (rationalPoints.map P.inclusion g) := by
  rw [IsRamifiedQuadraticValuation.mem_integralPoints_canonicalWeilLatticeModel_iff,
    IsRamifiedQuadraticValuation.mem_filtrationProduct_double_iff, P.val_map_inclusion y g,
    towerNormalizedValuation_apply]
  exact depth_iff (towerScale_pos _ _ _ _) _ _ _ _

/-- The ambient image of the integral points of the lattice model is `U_{a,y,r}`. -/
theorem latticeModel_integralPoints_map (y : B.Apartment) (r : ℝ) :
    (P.latticeModel y r).integralPoints.map (rationalPoints.map P.inclusion) =
      B.apartment.filtration y a r := by
  have hq := P.isRootSubgroup
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(hq.pointsEquiv (Over.mk (𝟙 _)) z).property,
      (P.mem_integralPoints_latticeModel_iff y r z).mp hz⟩
  · rintro ⟨hg, hdepth⟩
    let z := (hq.pointsEquiv (Over.mk (𝟙 _))).symm ⟨g, hg⟩
    have hz : rationalPoints.map P.inclusion z = g := hq.pointsEquiv_symm_comp ⟨g, hg⟩
    refine ⟨z, (P.mem_integralPoints_latticeModel_iff y r z).mpr ?_, hz⟩
    rwa [hz]

/-- **The unitary lattice presentation of `U_{a,y,r}`.** Valued unitary coordinates of the
multipliable root `a` present the filtration group `U_{a,y,r}` by the actual restriction
`R_{O_E/O} X_{r',2r'}` of the unitary lattice model at depth
`r' = c (r - a(y - origin)) - μ / 2`. -/
def rootFiltrationModelData (y : B.Apartment) (r : ℝ) :
    RootFiltrationModelData (MaximalUnramified.valuation F).valuationSubring
      (inertiaFixedField F) B.apartment y a r where
  rootGroup := P.weilGroup
  inclusion := P.inclusion
  isRootSubgroup := P.isRootSubgroup
  model := P.latticeModel y r
  smooth := P.normalizedValuation_isRamified.canonicalWeilLatticeModel_isSmooth _ _ _ _ _
    P.normalizedValuation_isValuationIntegers _ _
  geometricallyConnected :=
    P.normalizedValuation_isRamified.canonicalWeilLatticeModel_hasGeometricallyConnectedFibres
      _ _ _ _ _ P.normalizedValuation_isValuationIntegers _ _
  integralPoints_eq := P.latticeModel_integralPoints_map y r

theorem latticeDepth_mono (y : B.Apartment) {r s : ℝ} (hrs : r ≤ s) :
    P.latticeDepth y r ≤ P.latticeDepth y s := by
  have hc : 0 < P.scale := towerScale_pos _ _ _ _
  unfold latticeDepth
  nlinarith

include P in
/-- **Kernels between root-depth models of a multipliable root.** Given valued unitary
coordinates of the root `a`, for every point `y` of the apartment, any two supplied smooth
connected models of `U_{a,y,r}` and `U_{a,y,s}` with `r ≤ s` over a valuation ring `O` equal
to the valuation ring of the maximal unramified field, and every model map compatible with the
inclusions into `G`, the special-fibre kernel is smooth, connected and unipotent, provided
smooth model maps extend over `O`. -/
theorem specialFibreKernel_properties
    {O : ValuationSubring (inertiaFixedField F)}
    (hO : (MaximalUnramified.valuation F).valuationSubring = O)
    (hext : IntegralModel.HasSmoothHomExtension (R := O) (L := inertiaFixedField F))
    (y : B.Apartment) {r s : ℝ} (hrs : r ≤ s)
    (U : RootFiltrationModelData O (inertiaFixedField F) B.apartment y a r)
    (V : RootFiltrationModelData O (inertiaFixedField F) B.apartment y a s)
    (g : V.rootGroup ⟶ U.rootGroup) (hg : g ≫ U.inclusion = V.inclusion)
    (φ : V.model.Hom U.model g) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  subst hO
  have hr := P.latticeDepth_mono y hrs
  have h2 : 2 * P.latticeDepth y r ≤ 2 * P.latticeDepth y s := by linarith
  let ψ : (P.rootFiltrationModelData y s).model.Hom (P.rootFiltrationModelData y r).model (𝟙 _) :=
    P.normalizedValuation_isRamified.canonicalWeilLatticeTransition _ _ _ _ _
      P.normalizedValuation_isValuationIntegers hr h2
  have hψ := P.normalizedValuation_isRamified.canonicalWeilLatticeModel_kernel_properties _ _ _ _
    _ P.normalizedValuation_isValuationIntegers hr h2 ψ
  exact U.specialFibreKernel_properties_of_presentation V (P.rootFiltrationModelData y r)
    (P.rootFiltrationModelData y s) hext g hg (𝟙 _) (Category.id_comp _) φ ψ hψ

end Langlands.Geometry.Building.ValuedUnitaryRootGroupCoordinates

namespace Langlands.BruhatTits.IntegralModels

/-- **KP Lemma C.5.3 from valued unitary coordinates.** If every multipliable relative root
group over the maximal unramified field admits valued scheme-level unitary coordinates, then
`UnramifiedRootDepthKernelStatement` holds. Roots whose double is not a root have no higher
multiples, and are covered by `unramifiedNoHigherRootDepthKernel`. -/
theorem unramifiedRootDepthKernel_of_multipliableCoordinates
    (h : MultipliableRootGroupCoordinatesExistenceStatement.{u}) :
    UnramifiedRootDepthKernelStatement.{u} := by
  intro F _ _ _ _ G _ C x a r s hrs U V g hg φ
  by_cases h2 : 2 • (a : characterLattice C.S) ∈ relativeRoots C.i
  · obtain ⟨P⟩ := h F G C a h2
    exact P.specialFibreKernel_properties (MaximalUnramified.valuationSubring_eq F)
      (IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F) x hrs
      U V g hg φ
  · have : Smooth G.X.hom := C.isConnectedReductive.smooth
    have h2' : (2 : ℤ) • (a : characterLattice C.S) ∉ relativeRoots C.i := by
      rwa [two_zsmul, ← two_nsmul]
    have hhigh : RelativeRoot.HasNoHigherRoots C.i a :=
      C.hasOppositeFactorPairs.hasNoHigherRoots_of_two_not_mem C.i C.isMaximalSplitTorus.1.1 h2'
    exact unramifiedNoHigherRootDepthKernel F G C x a hhigh r s hrs U V g hg φ

end Langlands.BruhatTits.IntegralModels
