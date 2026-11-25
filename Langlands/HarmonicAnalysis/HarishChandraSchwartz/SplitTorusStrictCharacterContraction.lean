import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedExponentCone
import Langlands.Representation.Plancherel.SplitTorusCompactKernel
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.BruhatTits.Cartan.RenardLeviCones
import Langlands.Representation.Jacquet.StandardJacquetExponentRayBound

/-! # Strict contraction from chamber bounds on the actual split-torus section -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.Cartan.RenardLeviCones

namespace Langlands.HarishChandraSchwartz

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (A : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine A.X.left]

local instance splitTorusStrictCharacterContractionTopologicalSpace : TopologicalSpace (rationalPoints A.toGrp) := rationalPointTopology F A.X

/-- The character takes a value of norm different from one on the
intrinsic lattice section of the split torus. -/
abbrev IsNonunitaryOnCA (χ : rationalPoints A.toGrp →* ℂˣ) : Prop :=
  ∃ a : CocharacterUniformizer.CA F A, ‖(χ a : ℂ)‖ ≠ 1

/-- A nonunitary smooth character of the actual split torus is already
nonunitary on its intrinsic uniformizer section. -/
theorem exists_norm_ne_one_on_CA
    (hA : IsSplitTorus A.toGrp) (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp)))
    (hne : ¬ ∀ a, ‖(χ a : ℂ)‖ = 1) :
    IsNonunitaryOnCA A χ := by
  classical
  push Not at hne
  obtain ⟨b, hb⟩ := hne
  obtain ⟨c, hc, _⟩ := (CocharacterUniformizer.isUniformizerLatticeSection F A hA).2.2 b
  have hknorm := Plancherel.SplitTorus.norm_eq_one_on_commonNormKernel hA χ hχ hc
  refine ⟨⟨CocharacterUniformizer.latticeSection F A c, ⟨c, rfl⟩⟩, ?_⟩
  intro hunit
  apply hb
  simpa only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
    norm_inv, hunit, inv_one, mul_one] using hknorm

/-- Bounds by one on the strict intrinsic lattice chamber force every
nonunitary smooth character to be strictly contracting there. The chamber
is specified by any finite set of actual algebraic characters. -/
theorem norm_lt_one_of_CAprime_bound
    (hA : IsSplitTorus A.toGrp) (R : Set (characterLattice A)) (hR : R.Finite)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp)))
    (hbound : ∀ a ∈ CocharacterUniformizer.CAstrict F A R, ‖(χ a : ℂ)‖ ≤ 1)
    (a₀ : rationalPoints A.toGrp) (ha₀ : a₀ ∈ CocharacterUniformizer.CAstrict F A R)
    (hne : ¬ ∀ a, ‖(χ a : ℂ)‖ = 1) :
    ‖(χ a₀ : ℂ)‖ < 1 := by
  classical
  let E := characterLattice A → ℝ
  let HM : CocharacterUniformizer.CA F A → E :=
    fun a α => (characterOrder A α a : ℝ)
  let S : Finset (Module.Dual ℝ E) :=
    hR.toFinset.image (fun α => (LinearMap.proj α : Module.Dual ℝ E))
  have hHM : ∀ a b, HM (a * b) = HM a + HM b := by
    intro a b
    funext α
    change (characterOrder A α ((a * b : CocharacterUniformizer.CA F A) :
      rationalPoints A.toGrp) : ℝ) = _
    rw [Subgroup.coe_mul, characterOrder_mul, Int.cast_add]
    rfl
  have hmem : ∀ α, α ∈ S ↔
      ∃ β ∈ R, (LinearMap.proj β : Module.Dual ℝ E) = α := by
    intro α
    simp only [S, Finset.mem_image, Set.Finite.mem_toFinset]
  have hstrict : ∀ α ∈ S, 0 < α (HM ⟨a₀, ha₀.1⟩) := by
    intro α hα
    obtain ⟨β, hβ, rfl⟩ := (hmem α).mp hα
    have hpos := (characterNorm_lt_one_iff A β a₀).mp (ha₀.2 β hβ)
    change (0 : ℝ) < (characterOrder A β a₀ : ℝ)
    exact_mod_cast hpos
  have hle : ∀ a : CocharacterUniformizer.CA F A,
      (∀ α ∈ S, 0 < α (HM a)) → ‖(χ (a : rationalPoints A.toGrp) : ℂ)‖ ≤ 1 := by
    intro a ha
    apply hbound a
    refine ⟨a.property, fun β hβ => ?_⟩
    apply (characterNorm_lt_one_iff A β a).mpr
    have hpos := ha (LinearMap.proj β) ((hmem _).mpr ⟨β, hβ, rfl⟩)
    change (0 : ℝ) < (characterOrder A β a : ℝ) at hpos
    exact_mod_cast hpos
  obtain ⟨b, hb⟩ := exists_norm_ne_one_on_CA A hA χ hχ hne
  exact norm_lt_one_of_norm_le_one
    (χ := χ.comp (CocharacterUniformizer.CA F A).subtype) hHM hstrict hle ⟨b, hb⟩

end Langlands.HarishChandraSchwartz

open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup standardConstantTermT2Field standardConstantTermLocallyCompact
  standardConstantTermNonarchimedean

variable {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
  {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν J q L)

include hi hB hmem in
set_option maxHeartbeats 1200000 in
/-- Coefficient Xi control and the corresponding polynomial Xi upper bound
along every strict component lattice ray imply strict contraction of every
nonunitary exponent of the actual ordinary normalized standard Jacquet action. -/
theorem norm_standardJacquet_exponent_lt_one_of_ray_bounds
    (ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) (hρ : ρ.IsAdmissible)
    {Ξ : rationalPoints G → ℝ} (hcoeff : HasXiBoundedCoefficients Ξ ρ.representation)
    (hray : ∀ a ∈ CocharacterUniformizer.CAstrict F A
      (standardParabolicComponentCharacters i ν J q),
      ∃ (C : ℝ) (d : ℕ), ∀ n : ℕ, 1 ≤ n →
        Ξ ((standardComponentHom hA a : rationalPoints G) ^ n) ≤
          C * ‖standardHalfModulus i ν J (standardComponentHom hA a)‖ ^ n * (1 + n) ^ d)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsGeneralizedEigencharacter
      ((standardOrdinaryJacquetObject (i := i) (ν := ν) (J := J) ρ).representation.comp
        (standardComponentHom hA)) χ)
    (hne : ¬ ∀ b, ‖(χ b : ℂ)‖ = 1)
    (a : rationalPoints A.toGrp)
    (ha : a ∈ CocharacterUniformizer.CAstrict F A
      (standardParabolicComponentCharacters i ν J q)) :
    ‖(χ a : ℂ)‖ < 1 := by
  let : IsAffineHom A.X.hom := hA.1.1.isAffineHom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  let : TopologicalSpace (rationalPoints A.toGrp) := rationalPointTopology F A.X
  have hj : Continuous (standardComponentHom hA) := by
    apply Continuous.subtype_mk
    exact continuous_rationalPointMap F (q ≫ i).hom.hom
  have hχker := isOpen_ker_of_isGeneralizedEigencharacter_comp
    (standardOrdinaryJacquetObject (i := i) (ν := ν) (J := J) ρ).representation
    (standardOrdinaryJacquetObject (i := i) (ν := ν) (J := J) ρ).isSmooth
    (standardComponentHom hA) hj χ hχ
  have hR : (standardParabolicComponentCharacters i ν J q).Finite :=
    ((hi.1.1.finite_simpleRelativeRoots i ν).subset Set.sdiff_subset).image _
  exact norm_lt_one_of_CAprime_bound A hA.1.1 _ hR χ hχker
    (fun b hb => norm_standardJacquet_exponent_le_one_of_ray_bound
      hA hB hmem ρ hρ hcoeff b hb (hray b hb) χ hχ) a ha hne

end Langlands.HarishChandraSchwartz
