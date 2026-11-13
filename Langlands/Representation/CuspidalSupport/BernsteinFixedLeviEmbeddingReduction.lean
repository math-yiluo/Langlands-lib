import Langlands.Representation.CuspidalSupport.BernsteinSupportJacquetPresentation
import Langlands.Representation.CuspidalSupport.BernsteinBlockCharacterizationStatement
import Langlands.Representation.CuspidalSupport.BernsteinBlockJacquetFaithfulStatement
import Langlands.Representation.CuspidalSupport.BernsteinCuspAdjunction
import Langlands.Representation.CuspidalSupport.BernsteinLeviInertiaCofan
import Langlands.Representation.CuspidalSupport.RestrictionConstituentExistence
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.Aubert.General.DirectedUnions
import Langlands.Representation.Category.FiniteGenerationCoproducts

/-! # The fixed-Levi embedding of a Bernstein block from a Levi block projection

Renard VI.7.2: a conditional derivation of the fixed-Levi embedding step
`BernsteinFixedLeviBlockEmbedding`. Its inputs are a Levi-side block projection (derived
from VI.3.3.1), VI.10.3 and VI.4.1. The proved VI.3.2 is also used. The module then
assembles the published characterization from these inputs and geometric exclusion. -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance instFixedLeviEmbeddingGroupAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance instFixedLeviEmbeddingFieldT2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance instFixedLeviEmbeddingTopology :
    TopologicalSpace (rationalPoints G) := pointTopology
local instance instFixedLeviEmbeddingLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance instFixedLeviEmbeddingLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance instFixedLeviEmbeddingLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance instFixedLeviEmbeddingLeviPointTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

local instance instFixedLeviEmbeddingLeviLocalCompact (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) := by
  have := (isClosed_levi i ν I).locallyCompactSpace
  exact (leviRationalPointHomeomorph i ν I).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance instFixedLeviEmbeddingLeviNonarchimedean (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) := by
  let e := leviRationalPointHomeomorph i ν I
  have : IsTopologicalGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMulEquiv.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

/-- Levi-side input, derived from Renard VI.3.3.1: every smooth representation `W` of the
literal standard Levi of `a` maps to the literal transport of an object `τ` of the inertia
block `M(M)_D` of `a.representation`, by a map `p` that is nonzero on every nonzero map from
an object of that block. With the decomposition `W = W_D ⊕ W^D`, `p` is the projection to
the `D`-component. -/
def BernsteinLeviBlockProjection : Prop :=
  ∀ (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (W : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν a.roots)),
    ∃ (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)))
      (p : W ⟶ bernsteinLiteralLeviRep i ν a.roots τ),
      rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ ∧
      ∀ Y : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)),
        rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation Y →
        ∀ f : bernsteinLiteralLeviRep i ν a.roots Y ⟶ W, f ≠ 0 → f ≫ p ≠ 0

/-- Detection of block objects by the Jacquet module: every nonzero object `X` of the
Bernstein block of `a` receives a nonzero map, into its normalized Jacquet module along the
standard parabolic of `a.roots`, from the literal transport of an object of `M(M)_D`. -/
def BernsteinLeviBlockJacquetDetection : Prop :=
  ∀ (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (X : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)),
    Nontrivial X.obj →
      ∃ (Y : SmoothRep.{0, uF, max uF uV} ℂ
          (rationalPoints (bernsteinLeviScheme i ν a.roots)))
        (f : bernsteinLiteralLeviRep i ν a.roots Y ⟶
          (jacquetFunctor (family.decomposition a.roots) (family.closedUnipotent a.roots)).obj
            X.obj),
        rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation Y ∧
          f ≠ 0

/-- The fixed-Levi embedding (condition (i) for block objects) from the Levi block
projection and Jacquet detection. The embedding is the first-adjointness transpose of the
projection of `r_P(V)`; its kernel is a block object whose Jacquet module is killed by the
projection, so detection forces it to vanish. -/
theorem bernsteinFixedLeviBlockEmbedding_of_projection_of_detection
    (hProj : BernsteinLeviBlockProjection.{uF, uV} i ν family)
    (hDet : BernsteinLeviBlockJacquetDetection.{uF, uV} i ν family) :
    BernsteinFixedLeviBlockEmbedding.{uF, uV} i ν family := by
  intro a V hV
  let Jf := jacquetFunctor.{uF, max uF uV} (family.decomposition a.roots)
    (family.closedUnipotent a.roots)
  let Ind := normalizedInductionFunctor.{uF, max uF uV} (family.decomposition a.roots)
    (family.closedUnipotent a.roots)
  let adj : Jf ⊣ Ind := normalizedJacquetInductionAdjunction.{uF, uV}
    (family.decomposition a.roots) (family.closedUnipotent a.roots)
    (standardUnipotent_isUnimodular_of_standardCocharacterStatement i ν standardCocharacter
      family.connectedReductive family.maximalSplitTorus family.genericCocharacter a.roots
      (family.closedUnipotent a.roots))
  have : Jf.IsLeftAdjoint := adj.isLeftAdjoint
  obtain ⟨τ, p, hτ, hp⟩ := hProj a (Jf.obj V)
  let φ : V ⟶ Ind.obj (bernsteinLiteralLeviRep i ν a.roots τ) := adj.homEquiv _ _ p
  have hφ : Function.Injective (SmoothRep.hom φ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    let K := SmoothRep.kernel φ
    let incl : K ⟶ V := SmoothRep.kernelι φ
    have hKnt : Nontrivial K := ⟨⟨⟨x, hx⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
    have hinclφ : incl ≫ φ = 0 := by
      apply ObjectProperty.hom_ext
      ext v
      exact v.2
    have hinclp : Jf.map incl ≫ p = 0 := by
      have h1 := adj.homEquiv_naturality_left_symm incl φ
      rw [hinclφ] at h1
      simp only [φ, Equiv.symm_apply_apply] at h1
      rw [← h1, Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
    have hKV : SmoothRep.IsSubquotient K V :=
      SmoothRep.IsSubrepresentation.isSubquotient ⟨incl, SmoothRep.subtype_injective V _⟩
    have hK : bernsteinSaturatedBlockProperty i ν family
        (bernsteinInertialClass i ν family a) K :=
      fun π hπ hπK => hV π hπ (smoothSubquotientTransitivity ℂ _ _ _ _ hπK hKV)
    obtain ⟨Y, f, hY, hf⟩ := hDet a ⟨K, hK⟩ hKnt
    have hinj : Function.Injective (SmoothRep.hom (Jf.map incl)) :=
      normalizedJacquetFunctor_map_injective _ _ _ _
        (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement i ν
          standardCocharacter family.connectedReductive family.maximalSplitTorus
          family.genericCocharacter a.roots) incl (SmoothRep.subtype_injective V _)
    have : Mono (Jf.map incl) := (SmoothRep.mono_iff_injective _).mpr hinj
    have hfincl : f ≫ Jf.map incl ≠ 0 := fun h =>
      hf ((cancel_mono (Jf.map incl)).mp (h.trans zero_comp.symm))
    exact hp Y hY (f ≫ Jf.map incl) hfincl (by rw [Category.assoc, hinclp, comp_zero])
  refine ⟨PUnit.{max uF uV + 1}, fun _ => τ, fun _ => hτ, ?_⟩
  let _ : DecidableEq PUnit.{max uF uV + 1} := Classical.decEq _
  let ιs := SmoothRep.directSumι.{uF, max uF uV, max uF uV}
    (fun _ : PUnit.{max uF uV + 1} => Ind.obj (bernsteinLiteralLeviRep i ν a.roots τ))
    PUnit.unit
  have : Mono φ := (SmoothRep.mono_iff_injective _).mpr hφ
  have : IsSplitMono ιs := IsSplitMono.mk'
    { retraction := SmoothRep.directSumπ _ PUnit.unit
      id := SmoothRep.directSumι_comp_π_self _ _ }
  have : Mono ιs := IsSplitMono.mono ιs
  have hm : Mono (φ ≫ ιs) := mono_comp φ ιs
  exact ⟨φ ≫ ιs, (SmoothRep.mono_iff_injective _).mp hm⟩

/-- Jacquet detection from Renard VI.10.3 and the membership half of VI.4.1. The object
`Y` is `Π_D = ind_{⁰M}^M(ρ₀)` for an irreducible constituent `ρ₀` of the restriction of
`a.representation` to `⁰M`, which exists by the proved VI.3.2. VI.10.3 gives the nonzero
map, and VI.4.1 places `Π_D` in `M(M)_D`. -/
theorem bernsteinLeviBlockJacquetDetection_of_faithful
    (hJF : BernsteinBlockJacquetFaithfulStatement.{uF, uV})
    (hProg : RationalSummandSmallProgeneratorStatement.{uF, max uF uV}) :
    BernsteinLeviBlockJacquetDetection.{uF, uV} i ν family := by
  intro a X hX
  let L := bernsteinLeviScheme i ν a.roots
  let : T2Space (rationalPoints L) := rationalPoint_t2Space F L
  let jT := bernsteinLeviTorus i ν a.roots
  let fam := bernsteinLeviStandardFamily i ν family a.roots
  have := family.maximalSplitTorus.isSplitSubtorus.mono
  obtain ⟨W, hW⟩ := rationalNormKernelConstituent_of_finiteRestriction
    rationalNormKernelFiniteRestriction.{uF, max uF uV} F L fam.connectedReductive
    a.representation a.irreducible
  let H := Plancherel.rationalCommonNormKernel L
  let ρ₀ := SmoothRep.subrepresentation (SmoothRep.restrictSubgroup H a.representation) W
  have hρ₀ : ρ₀.IsIrreducible := hW
  let j : ρ₀ ⟶ SmoothRep.restrictSubgroup H a.representation :=
    SmoothRep.subtype (SmoothRep.restrictSubgroup H a.representation) W
  have hj : Function.Injective (SmoothRep.hom j) :=
    SmoothRep.subtype_injective (SmoothRep.restrictSubgroup H a.representation) W
  obtain ⟨f, hf⟩ := hJF F G T i ν family a ρ₀ hρ₀ j hj X hX
  refine ⟨_, f, ?_, hf⟩
  have := fam.maximalSplitTorus.isSplitSubtorus.mono
  let hRoots := relativeRootSystem F L fam.connectedReductive T jT fam.maximalSplitTorus
  let := simpleRelativeRootFintype jT hRoots fam.maximalSplitTorus.isSplitSubtorus.1 ν
  have hA := (rationalLeviCuspidalityTransport dynamicLie standardCocharacter
    F G family.connectedReductive T i family.maximalSplitTorus ν
    family.genericCocharacter a.roots fam.connectedReductive family.closedUnipotent
    fam.closedUnipotent (family.closedLevi a.roots) (family.leviDecomposition a.roots)
    fam.decomposition _).mpr a.cuspidal
  have hc := hA.of_iso (SmoothRep.pullbackSymmIso
    (leviRationalPointHomeomorph i ν a.roots).symm a.representation).symm
  obtain ⟨hmem, -⟩ := hProg F L fam.connectedReductive T jT fam.maximalSplitTorus ν
    fam.genericCocharacter standardCocharacter hRoots fam.closedUnipotent a.representation
    a.irreducible hc ρ₀ hρ₀ j hj
  exact (rationalInertiaBlockProperty_iff_of_related (IsRationalInertiaRelated.of_iso
    (SmoothRep.mkIso (SmoothRep.universeLiftEquiv a.representation)).symm)).mp hmem

/-- The fixed-Levi embedding from the Levi block projection, VI.10.3 and VI.4.1. -/
theorem bernsteinFixedLeviBlockEmbedding_of_projection
    (hProj : BernsteinLeviBlockProjection.{uF, uV} i ν family)
    (hJF : BernsteinBlockJacquetFaithfulStatement.{uF, uV})
    (hProg : RationalSummandSmallProgeneratorStatement.{uF, max uF uV}) :
    BernsteinFixedLeviBlockEmbedding.{uF, uV} i ν family :=
  bernsteinFixedLeviBlockEmbedding_of_projection_of_detection i ν family hProj
    (bernsteinLeviBlockJacquetDetection_of_faithful i ν family hJF hProg)

/-- The per-family inputs that remain after this reduction, quantified over all data at the
universes of the published characterization: the Levi block projection (derived from
VI.3.3.1) and the geometric exclusion step. This is a target, not an axiom. -/
def BernsteinBlockCharacterizationLeviInputs : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν),
      BernsteinLeviBlockProjection.{uF, uV} i ν family ∧
      BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family

/-- Renard VI.7.2, conditional on the Levi block projection and geometric exclusion for
every family, together with VI.10.3 and VI.4.1. None of these inputs is discharged here. -/
theorem bernsteinBlockCharacterization_of_leviInputs
    (h : BernsteinBlockCharacterizationLeviInputs.{uF, uV})
    (hJF : BernsteinBlockJacquetFaithfulStatement.{uF, uV})
    (hProg : RationalSummandSmallProgeneratorStatement.{uF, max uF uV}) :
    BernsteinBlockCharacterizationStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν _ _ family a
  dsimp only
  intro V
  obtain ⟨hProj, hGeom⟩ := h F G T i ν family
  exact bernsteinBlockCharacterization_of_embedding_and_exclusion i ν family
    (bernsteinFixedLeviBlockEmbedding_of_projection i ν family hProj hJF hProg) hGeom a V

end Langlands.CuspidalSupport
