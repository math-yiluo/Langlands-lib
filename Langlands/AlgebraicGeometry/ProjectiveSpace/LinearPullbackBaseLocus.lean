import Langlands.AlgebraicGeometry.ProjectiveSpace.LinearSectionGenerationOpen
import Langlands.AlgebraicGeometry.ProjectiveSpace.RationalPointLinearForms

/-! # The base locus of the linear forms through a rational point, pulled back -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-- Let `i : X ⟶ ℙᵐ_K` be injective on points and let `σ` be a `K`-point of `X` over `K`.
A point `y` of `X` has every linear form through `i (σ pt)` in its homogeneous prime
exactly when `y = σ pt`. -/
theorem forall_linear_mem_iff_eq_section {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace K m)
    (hi : Function.Injective i) (σ : Spec (CommRingCat.of K) ⟶ X)
    (hσ : σ ≫ i ≫ projectiveSpaceToSpec K m = 𝟙 _) (y : X) :
    (∀ l : projectiveSpaceGrading K m 1,
      (l : ProjectiveCoordinateRing K m) ∈
          (i (σ (IsLocalRing.closedPoint K))).asHomogeneousIdeal →
        (l : ProjectiveCoordinateRing K m) ∈ (i y).asHomogeneousIdeal) ↔
      y = σ (IsLocalRing.closedPoint K) := by
  constructor
  · intro h
    obtain ⟨k, c, hk, hc⟩ :=
      exists_linearCoordinates_of_section (σ ≫ i) (by rw [Category.assoc]; exact hσ)
    rw [Scheme.Hom.comp_apply] at hk hc
    exact hi (eq_of_forall_linear_mem hk hc h)
  · rintro rfl l hl
    exact hl

end Langlands.AlgebraicGeometry.ProjectiveSpace

namespace Langlands.AlgebraicGeometry

universe u

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

variable {K : Type u} [Field K] {m : ℕ}

/-- A point lies in the generation open of the pullback of the section `f / 1` of `𝒪(1)`
along `i` (transported along an isomorphism) iff `f` is not in the homogeneous prime of
its image. -/
theorem mem_trivializationOpen_isoPullbackSection_twistOne_iff {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace K m) {N : X.Modules}
    (e : (Scheme.Modules.pullback i).obj (twistOneLineBundle K m).obj ≅ N)
    (f : projectiveSpaceGrading K m 1) (x : X) :
    x ∈ trivializationOpen N
        (isoPullbackSection i (twistOneLineBundle K m) e (twistOneLinearSection K m f)) ↔
      (f : ProjectiveCoordinateRing K m) ∉ (i x).asHomogeneousIdeal := by
  rw [trivializationOpen_isoPullbackSection, Scheme.Hom.mem_preimage]
  exact mem_trivializationOpen_twistOneLinearSection_iff K m f (i x)

/-- The section of `N` obtained from a linear form `l` by pulling `l / 1` back along
`i : X ⟶ ℙᵐ_K` to the line bundle `M` and then along `h : Y ⟶ X` to `N`, each time
transporting along the supplied isomorphism. -/
def linearPullbackSection {X Y : Scheme.{u}} (i : X ⟶ ProjectiveSpace K m) (M : LineBundle X)
    (eM : (Scheme.Modules.pullback i).obj (twistOneLineBundle K m).obj ≅ M.obj) (h : Y ⟶ X)
    {N : Y.Modules} (eN : (Scheme.Modules.pullback h).obj M.obj ≅ N)
    (l : projectiveSpaceGrading K m 1) : GlobalSections N :=
  isoPullbackSection h M eN
    (isoPullbackSection i (twistOneLineBundle K m) eM (twistOneLinearSection K m l))

/-- A point `y` lies in the generation open of `linearPullbackSection` attached to `l` iff
`l` is not in the homogeneous prime of `i (h y)`. -/
theorem mem_trivializationOpen_linearPullbackSection_iff {X Y : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace K m) (M : LineBundle X)
    (eM : (Scheme.Modules.pullback i).obj (twistOneLineBundle K m).obj ≅ M.obj) (h : Y ⟶ X)
    {N : Y.Modules} (eN : (Scheme.Modules.pullback h).obj M.obj ≅ N)
    (l : projectiveSpaceGrading K m 1) (y : Y) :
    y ∈ trivializationOpen N (linearPullbackSection i M eM h eN l) ↔
      (l : ProjectiveCoordinateRing K m) ∉ (i (h y)).asHomogeneousIdeal := by
  rw [linearPullbackSection, trivializationOpen_isoPullbackSection, Scheme.Hom.mem_preimage,
    mem_trivializationOpen_isoPullbackSection_twistOne_iff]

/-- The sections `linearPullbackSection` attached to the linear forms that vanish at the
point `x₀` of `X`. -/
def linearPullbackSystem {X Y : Scheme.{u}} (i : X ⟶ ProjectiveSpace K m) (M : LineBundle X)
    (eM : (Scheme.Modules.pullback i).obj (twistOneLineBundle K m).obj ≅ M.obj) (h : Y ⟶ X)
    {N : Y.Modules} (eN : (Scheme.Modules.pullback h).obj M.obj ≅ N) (x₀ : X) :
    Set (GlobalSections N) :=
  {t | ∃ l : projectiveSpaceGrading K m 1,
    (l : ProjectiveCoordinateRing K m) ∈ (i x₀).asHomogeneousIdeal ∧
      linearPullbackSection i M eM h eN l = t}

/-- If `i` is injective on points and `σ` is a `K`-point of `X` over `K`, then the base
locus of the pulled-back linear forms through `i (σ pt)` is the fibre of `h` over `σ pt`. -/
theorem baseLocus_linearPullbackSystem {X Y : Scheme.{u}} (i : X ⟶ ProjectiveSpace K m)
    (hi : Function.Injective i) (σ : Spec (CommRingCat.of K) ⟶ X)
    (hσ : σ ≫ i ≫ projectiveSpaceToSpec K m = 𝟙 _) (M : LineBundle X)
    (eM : (Scheme.Modules.pullback i).obj (twistOneLineBundle K m).obj ≅ M.obj) (h : Y ⟶ X)
    {N : Y.Modules} (eN : (Scheme.Modules.pullback h).obj M.obj ≅ N) :
    {y : Y | ∀ t ∈ linearPullbackSystem i M eM h eN (σ (IsLocalRing.closedPoint K)),
        y ∉ trivializationOpen N t} =
      h ⁻¹' {σ (IsLocalRing.closedPoint K)} := by
  ext y
  rw [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
    ← ProjectiveSpace.forall_linear_mem_iff_eq_section i hi σ hσ (h y)]
  constructor
  · intro H l hl
    have := H _ ⟨l, hl, rfl⟩
    rwa [mem_trivializationOpen_linearPullbackSection_iff, not_not] at this
  · rintro H t ⟨l, hl, rfl⟩
    rw [mem_trivializationOpen_linearPullbackSection_iff, not_not]
    exact H l hl

end Langlands.AlgebraicGeometry
