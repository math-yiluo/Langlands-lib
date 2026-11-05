import Langlands.Representation.Aubert.General.CartanSupportReduction
import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionStatement
import Langlands.Representation.Plancherel.RationalCharacterTopology
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation

/-! # Compact support from actual bounded Cartan expressions -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General

open RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- The literal positive uniformizer cone gives nonnegative integral pairings. -/
theorem exists_cocharacter_of_mem_CAplus
    {a : rationalPoints S.toGrp}
    (ha : a ∈ CocharacterUniformizer.CAplus F S (simpleRelativeRoots i ν)) :
    ∃ x : cocharacterLattice S,
      a = CocharacterUniformizer.latticeSection F S (.ofAdd x) ∧
        ∀ β : SimpleRoot i ν, 0 ≤ simpleRootPairing i ν β x := by
  obtain ⟨⟨c, rfl⟩, hc⟩ := ha
  refine ⟨c.toAdd, rfl, fun β => ?_⟩
  have hβ := hc β.1 β.2
  rw [show c = Multiplicative.ofAdd c.toAdd from rfl,
    CocharacterUniformizer.characterNorm_latticeSection] at hβ
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  exact neg_nonpos.mp ((zpow_le_one_iff_right₀ hq).mp hβ)

/-- Uniform bounds on the simple-root coordinates of nonzero values in actual
Cartan expressions, for a specified finite set of centralizer factors. -/
def RationalCartanSupportBound {E : Type v} [Zero E]
    (K : Subgroup (rationalPoints G)) (F₀ : Finset (centralizerPoints i))
    (φ : rationalPoints G → E) : Prop :=
  ∃ B : ℤ, ∀ (k₁ k₂ : rationalPoints G) (f : centralizerPoints i)
    (x : cocharacterLattice S),
    k₁ ∈ K → k₂ ∈ K → f ∈ F₀ →
    (∀ β : SimpleRoot i ν, 0 ≤ simpleRootPairing i ν β x) →
    φ (k₁ * uniformizerPowers i (.ofAdd x) * (f : rationalPoints G) * k₂) ≠ 0 →
      ∀ β : SimpleRoot i ν, simpleRootPairing i ν β x ≤ B

variable [IsAffine G.X.left]

local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- A finite actual Cartan cover with bounded nonzero parameters gives compact
support on the actual norm kernel, provided joint detection is known. -/
theorem hasCompactSupport_normKernel_of_cartanSupportBound
    [Finite (SimpleRoot i ν)] [IsTopologicalGroup (rationalPoints G)]
    [T2Space (rationalPoints G)] {E : Type v} [Zero E]
    (K : Subgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (F₀ : Finset (centralizerPoints i))
    (hcover : ∀ g : rationalPoints G,
      ∃ (k₁ k₂ : rationalPoints G) (f : centralizerPoints i) (a : rationalPoints S.toGrp),
        k₁ ∈ K ∧ k₂ ∈ K ∧ f ∈ F₀ ∧
        a ∈ CocharacterUniformizer.CAplus F S (simpleRelativeRoots i ν) ∧
        g = k₁ * (f : rationalPoints G) * rationalPoints.map i a * k₂)
    (hdet : JointCartanDetection (fun β x => simpleRootPairing i ν β x)
      (fun x => Plancherel.rationalCharacterValuation G (uniformizerPowers i (.ofAdd x))))
    (φ : rationalPoints G → E) (hbound : RationalCartanSupportBound i ν K F₀ φ) :
    HasCompactSupport (fun g : Plancherel.rationalCommonNormKernel G => φ g) := by
  obtain ⟨B, hB⟩ := hbound
  have hKq : K ≤ (Plancherel.rationalCharacterValuation G).ker := by
    rw [Plancherel.rationalCharacterValuation_ker]
    exact Plancherel.compactSubgroup_le_rationalCommonNormKernel G K hK
  have hq : IsClosed ((Plancherel.rationalCharacterValuation G).ker :
      Set (rationalPoints G)) := by
    rw [Plancherel.rationalCharacterValuation_ker]
    exact Plancherel.isClosed_rationalCommonNormKernel G
  have hcompact := hasCompactSupport_of_bounded_cartan_parameters
    (Plancherel.rationalCharacterValuation G) K hK hKq hq
    (fun x => uniformizerPowers i (.ofAdd x)) (fun β x => simpleRootPairing i ν β x) hdet
    (Subtype.val '' (F₀ : Set (centralizerPoints i))) (F₀.finite_toSet.image _)
    0 B (fun g => φ g.val) ?_
  · let e : Plancherel.rationalCommonNormKernel G ≃ₜ
        (Plancherel.rationalCharacterValuation G).ker :=
      Homeomorph.setCongr (congrArg (fun H : Subgroup (rationalPoints G) =>
        (H : Set (rationalPoints G))) (Plancherel.rationalCharacterValuation_ker G).symm)
    exact hcompact.comp_homeomorph e
  · intro g hg
    obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hrep⟩ := hcover g
    obtain ⟨x, rfl, hx⟩ := exists_cocharacter_of_mem_CAplus i ν ha
    have he : rationalPoints.map i (CocharacterUniformizer.latticeSection F S (.ofAdd x)) =
        uniformizerPowers i (.ofAdd x) := rfl
    rw [he] at hrep
    have hxT : uniformizerPowers i (.ofAdd x) ∈ torusPoints i :=
      (mem_torusPoints i _).mpr ⟨CocharacterUniformizer.latticeSection F S (.ofAdd x), rfl⟩
    have hcomm : (f : rationalPoints G) * uniformizerPowers i (.ofAdd x) =
        uniformizerPowers i (.ofAdd x) * (f : rationalPoints G) :=
      (centralizerPoints_le_pointCentralizer i f.property _ hxT).symm
    have hrep' : (g : rationalPoints G) =
        k₁ * uniformizerPowers i (.ofAdd x) * (f : rationalPoints G) * k₂ := by
      rw [mul_assoc k₁, hcomm, ← mul_assoc] at hrep
      exact hrep
    have hupper := hB k₁ k₂ f x hk₁ hk₂ hf hx (by simpa only [← hrep'] using hg)
    exact ⟨k₁, hk₁, f, ⟨f, hf, rfl⟩, x, k₂, hk₂,
      fun β => ⟨hx β, hupper β⟩, hrep⟩

/-- The published literal finite covering can be used directly when bounds are
available for every finite set of centralizer factors. -/
theorem hasCompactSupport_normKernel_of_finiteCartanCovering
    [Finite (SimpleRoot i ν)] [IsTopologicalGroup (rationalPoints G)]
    [T2Space (rationalPoints G)] {E : Type v} [Zero E]
    (K : Subgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hcover : FiniteCartanCovering F i ν K)
    (hdet : JointCartanDetection (fun β x => simpleRootPairing i ν β x)
      (fun x => Plancherel.rationalCharacterValuation G (uniformizerPowers i (.ofAdd x))))
    (φ : rationalPoints G → E)
    (hbound : ∀ F₀ : Finset (centralizerPoints i), RationalCartanSupportBound i ν K F₀ φ) :
    HasCompactSupport (fun g : Plancherel.rationalCommonNormKernel G => φ g) := by
  obtain ⟨F₀, hF₀⟩ := hcover
  exact hasCompactSupport_normKernel_of_cartanSupportBound i ν K hK F₀ hF₀ hdet φ (hbound F₀)

end Langlands.Aubert.General
