import Langlands.Representation.CuspidalSupport.BernsteinRepresentedCuspidality
import Langlands.Representation.CuspidalSupport.RationalSummandCenterVarietyProof
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement
import Langlands.Representation.CuspidalSupport.RestrictionConstituentExistence
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.CuspidalSupport.NormalHeckeTwist

/-! # VI.4.4 on the Levi of an actual Bernstein cuspidal datum -/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.4.4, Proposition, last sentence, on the rational Levi `M = M_a` of every actual
standard cuspidal datum `a = (M, ρ)` of a standard family (carriers in `Type (max uF uV)`). For an
irreducible smooth `ρ₀` of `⁰M` with an injective `⁰M`-map `j : ρ₀ → ρ|_{⁰M}`, let
`Π_D = ind_{⁰M}^{M} ρ₀`, `X = X(M)` and `Stab = {s ∈ X | ρ ⊗ s ≅ ρ}`. There is an injective
algebra homomorphism `Ψ` from the centre of `End Π_D` to the functions on `X` whose range is the
set of `Stab`-invariant elements of `ℂ[X]` (`unramifiedRegularFunctions`), such that every
central `z` acts on every map `Π_D → ρ ⊗ ω` by the scalar `Ψ z ω`. -/
def BernsteinLeviCenterVarietyStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family),
      haveI : IsClosedImmersion (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left :=
        Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots)
      haveI : IsAffine (bernsteinLeviScheme i ν a.roots).X.left :=
        isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left
      haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν a.roots).X.hom := by
        rw [← (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.w]
        infer_instance
      letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
        rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X
      ∀ (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
          (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots))),
        ρ₀.IsIrreducible →
        ∀ (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
          (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation),
        Function.Injective (SmoothRep.hom j) →
        let X := unramifiedCharacters
          (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
        let piD := rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀
        let Stab : Set X := {s | Nonempty
          (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) s a.representation ≅
            a.representation)}
        ∃ Ψ : Subalgebra.center ℂ (End piD) →ₐ[ℂ] (X → ℂ),
          Function.Injective Ψ ∧
          Set.range Ψ =
            {φ | φ ∈ unramifiedRegularFunctions
                (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) ∧
              ∀ s ∈ Stab, ∀ χ, φ (χ * s) = φ χ} ∧
          ∀ (z : Subalgebra.center ℂ (End piD)) (ω : X)
            (φ : piD ⟶ rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω
              a.representation),
            (z : End piD) ≫ φ = Ψ z ω • φ

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinLeviCenterInstance1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance bernsteinLeviCenterInstance2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinLeviCenterInstance3 : TopologicalSpace (rationalPoints G) := pointTopology
local instance bernsteinLeviCenterInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinLeviCenterInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinLeviCenterInstance10 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinLeviCenterInstance6 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

local instance bernsteinLeviCenterInstance7 (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) := by
  have := (isClosed_levi i ν I).locallyCompactSpace
  exact (leviRationalPointHomeomorph i ν I).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance bernsteinLeviCenterInstance8 (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) := by
  let e := leviRationalPointHomeomorph i ν I
  have : IsTopologicalGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMulEquiv.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

local instance bernsteinLeviCenterInstance9 (I : Finset (SimpleRoot i ν)) :
    T2Space (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPoint_t2Space F (bernsteinLeviScheme i ν I)

/-- `BernsteinLeviCenterVarietyStatement` holds: `rationalSummandCenterVariety` applied at the
rational Levi `M_a`, which is connected reductive with the standard-family structure of
`bernsteinStandardRepresentativesGeometric`, `ρ` being cuspidal for it by
`rationalLeviCuspidalityTransport`. -/
theorem bernsteinLeviCenterVarietyStatement_holds :
    BernsteinLeviCenterVarietyStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν _ _ family a ρ₀ hρ₀ j hj X piD Stab
  classical
  let : Mono i.hom.hom.left := family.maximalSplitTorus.isSplitSubtorus.mono
  let hgeom := bernsteinStandardRepresentativesGeometric i ν family a.roots
  let hL := hgeom.2.1.isConnectedReductive
  let j' := standardLeviTorusFactor i ν (rootSet i ν a.roots)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν a.roots))
  have hj' : IsMaximalSplitTorus j' :=
    family.maximalSplitTorus.isMaximalSplitTorus_standardLeviTorusFactor
      i ν (rootSet i ν a.roots) (Standard.isRepresentedBy_leviHom i ν (rootSet i ν a.roots))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots))
  have hjmono := hj'.isSplitSubtorus.mono
  let : Mono j'.hom.hom.left := hjmono
  have hνj : IsGenericCocharacter j' ν :=
    (standardLeviStandardFamilies dynamicLie standardCocharacter F G
      family.connectedReductive T i family.maximalSplitTorus ν
      family.genericCocharacter (rootSet i ν a.roots) (rootSet_subset i ν a.roots)
      (bernsteinLeviScheme i ν a.roots) hL (Standard.leviHom i ν (rootSet i ν a.roots))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν a.roots))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots))).2.1
  have hRoots := relativeRootSystem F (bernsteinLeviScheme i ν a.roots) hL T j' hj'
  let := simpleRelativeRootFintype j' hRoots hj'.isSplitSubtorus.1 ν
  let hOwn := isSemidirectDecomposition_of_standardCocharacterStatement
    j' ν standardCocharacter hL hj' hνj
  have hUL (J : Finset (SimpleRoot j' ν)) :
      IsClosed (unipotent j' ν J : Set (rationalPoints (bernsteinLeviScheme i ν a.roots))) :=
    isClosed_unipotent j' ν J
  let A := bernsteinLiteralLeviRep i ν a.roots a.representation
  have hc := (rationalLeviCuspidalityTransport dynamicLie standardCocharacter
    F G family.connectedReductive T i family.maximalSplitTorus ν
    family.genericCocharacter a.roots hL family.closedUnipotent hUL
    (family.closedLevi a.roots) (family.leviDecomposition a.roots) hOwn A).mpr a.cuspidal
  have hc' : IsCuspidal (parabolic j' ν) (levi j' ν) (unipotent j' ν)
      hOwn hUL a.representation :=
    hc.of_iso (SmoothRep.pullbackSymmIso (leviRationalPointHomeomorph i ν a.roots).symm
      a.representation).symm
  obtain ⟨Ψ, hinj, hrange, hΨ⟩ := rationalSummandCenterVariety.{uF, max uF uV} F
    (bernsteinLeviScheme i ν a.roots) hL T j' hj'
    ν hνj standardCocharacter hRoots hUL a.representation a.irreducible hc' ρ₀ hρ₀ j hj
  refine ⟨Ψ, hinj, hrange, fun z ω φ => ?_⟩
  let e := (SmoothRep.twistFunctor _ (isOpen_rationalUnramifiedCharacter_ker (bernsteinLeviScheme i ν a.roots) ω)).mapIso
    (SmoothRep.mkIso (SmoothRep.universeLiftEquiv a.representation) :
      a.representation ≅ rationalInertiaBaseLift (bernsteinLeviScheme i ν a.roots) a.representation)
  have h := hΨ z ω (φ ≫ e.hom)
  rw [← Category.assoc, ← Linear.smul_comp] at h
  exact (cancel_mono e.hom).mp h


omit [LocallyOfFiniteType G.X.hom] in
/-- Renard VI.3.2(ii) at the Levi `M = M_a` of an actual Bernstein cuspidal datum `a = (M, ρ)`:
there is an irreducible smooth representation `ρ₀` of `⁰M` together with an injective
`⁰M`-equivariant map `ρ₀ → ρ|_{⁰M}`. -/
theorem bernsteinCuspidalDatum_exists_normKernelConstituent
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) :
    ∃ (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
        (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
      (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
        (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation),
      ρ₀.IsIrreducible ∧ Function.Injective (SmoothRep.hom j) := by
  have hL := (bernsteinStandardRepresentativesGeometric i ν family a.roots).2.1.isConnectedReductive
  obtain ⟨W, hW⟩ := rationalNormKernelConstituent_of_finiteRestriction
    rationalNormKernelFiniteRestriction.{uF, max uF uV} F _ hL a.representation a.irreducible
  let H := rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)
  let ρ₀ := SmoothRep.subrepresentation (SmoothRep.restrictSubgroup H a.representation) W
  have hρ₀ : ρ₀.IsIrreducible := hW
  exact ⟨ρ₀, SmoothRep.subtype (SmoothRep.restrictSubgroup H a.representation) W, hρ₀,
    SmoothRep.subtype_injective (SmoothRep.restrictSubgroup H a.representation) W⟩

/-- At the Levi `M = M_a` of an actual Bernstein cuspidal datum `a = (M, ρ)`, for a nonzero
`ρ₀` of `⁰M` embedded in `ρ|_{⁰M}` and every `ω ∈ X(M)`, there is a surjective `M`-equivariant
map `Π_D = ind_{⁰M}^{M} ρ₀ → ρ ⊗ ω` (Frobenius reciprocity, `ω` being trivial on `⁰M`, and
irreducibility of `ρ ⊗ ω`). -/
theorem bernsteinCuspidalDatum_exists_surjective_twist
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    [Nontrivial ρ₀]
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j))
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)) :
    ∃ φ : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶
        rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation,
      Function.Surjective (SmoothRep.hom φ) := by
  let M := bernsteinLeviScheme i ν a.roots
  let H := rationalCommonNormKernel M
  have hH : IsOpen (H : Set (rationalPoints M)) := isOpen_rationalCommonNormKernel M
  have hωH : H ≤ ω.val.toMonoidHom.ker := ω.2
  have hω := isOpen_rationalUnramifiedCharacter_ker M ω
  let T : ρ₀.representation.IntertwiningMap
      (a.representation.representation.comp H.subtype) := SmoothRep.hom j
  let φ := (NormalHecke.inducedHomEquiv H ρ₀ hH
    (a.representation.twist ω.val.toMonoidHom hω)).symm
      ((NormalHecke.twistRestrictEquiv ρ₀ ω.val.toMonoidHom hω hωH a.representation).symm T)
  have hirr : (rationalUnramifiedTwist M ω a.representation).representation.IsIrreducible :=
    (isIrreducible_rationalUnramifiedTwist_iff M ω a.representation).mpr a.irreducible
  refine ⟨φ, (Representation.IsIrreducible.surjective_or_eq_zero (SmoothRep.hom φ)).resolve_right
    fun h0 => ?_⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ₀)
  apply hv
  apply hj
  have h1 : NormalHecke.inducedHomEquiv H ρ₀ hH
      (a.representation.twist ω.val.toMonoidHom hω) φ v = 0 := by
    rw [NormalHecke.inducedHomEquiv_apply, h0]
    rfl
  simp only [φ, LinearEquiv.apply_symm_apply] at h1
  rw [map_zero]
  exact h1

end Langlands.CuspidalSupport
