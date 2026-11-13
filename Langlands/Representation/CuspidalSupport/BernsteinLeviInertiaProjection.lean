import Langlands.Representation.CuspidalSupport.BernsteinLeviInertiaCofan
import Langlands.Representation.CuspidalSupport.RationalInertiaDecompositionStatement
import Langlands.Representation.Category.DecompositionCentralProjectors
import Langlands.Representation.Category.ExactFunctor
import Langlands.Representation.Parabolic.FlattenedTensorOccurrences
import Langlands.Representation.Aubert.General.RationalLeviCuspidalityTransportProof

/-! # Projection of a standard Levi object onto one cuspidal inertia block

Given Renard VI.3.3.1 (`RationalCuspidalInertiaDecompositionStatement`), every
smooth representation of an actual standard Levi maps onto an object of the
inertia block of a fixed Bernstein cuspidal datum, through a map that keeps
every morphism coming from that block. The statements are conditional on
VI.3.3.1, which stays an explicit hypothesis. -/

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

section Projection

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance inertiaProjectionPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- In an actual inertia category decomposition, every object `W` has a map
`p` to an object `τ` of the inertia block and a map `j` back, such that every
morphism from an object of the block into `W` factors as itself through
`p ≫ j`. Here `p` and `j` are the projection onto and the inclusion of the
block component of `W`. -/
theorem exists_rationalInertiaBlockProjection
    (π : SmoothRep.{0, uF, uV} ℂ (rationalPoints G))
    (h : IsRationalInertiaCategoryDecomposition G π)
    (W : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) :
    ∃ (τ : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) (p : W ⟶ τ) (j : τ ⟶ W),
      rationalInertiaBlockProperty G π τ ∧
        ∀ (Y : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)),
          rationalInertiaBlockProperty G π Y → ∀ f : Y ⟶ W, f ≫ p ≫ j = f := by
  obtain ⟨A, legs, hA, ⟨hc⟩⟩ := h.1 W
  exact ⟨A true, SmoothRep.cofanProjection hc true, legs true, hA true,
    fun Y hY f => SmoothRep.comp_cofanComponent h.2 hA hc f true hY⟩

end Projection

section Bernstein

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance leviProjectionAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance leviProjectionFieldT2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance leviProjectionAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance leviProjectionLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance leviProjectionLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance leviProjectionLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance leviProjectionLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

local instance leviProjectionLeviLocalCompact (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) := by
  have := (isClosed_levi i ν I).locallyCompactSpace
  exact (leviRationalPointHomeomorph i ν I).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance leviProjectionLeviNonarchimedean (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) := by
  let e := leviRationalPointHomeomorph i ν I
  have : IsTopologicalGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMulEquiv.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

/-- Renard VI.3.3.1, applied on the actual standard Levi of a Bernstein
cuspidal datum: the inertia block of the datum's cuspidal representation and
its complement form an actual category decomposition. Cuspidality is moved from
the literal Levi subgroup to the Levi scheme by the published transport. -/
theorem bernsteinLevi_isRationalInertiaCategoryDecomposition
    (hSplit : RationalCuspidalInertiaDecompositionStatement.{uF, max uF uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) :
    IsRationalInertiaCategoryDecomposition (bernsteinLeviScheme i ν a.roots)
      a.representation := by
  let I := a.roots
  let L := bernsteinLeviScheme i ν I
  let : T2Space (rationalPoints L) := rationalPoint_t2Space F L
  let j := bernsteinLeviTorus i ν I
  let fam := bernsteinLeviStandardFamily i ν family I
  have := family.maximalSplitTorus.isSplitSubtorus.mono
  have := fam.maximalSplitTorus.isSplitSubtorus.mono
  let hRoots := relativeRootSystem F L fam.connectedReductive T j fam.maximalSplitTorus
  let := simpleRelativeRootFintype j hRoots fam.maximalSplitTorus.isSplitSubtorus.1 ν
  let e := leviRationalPointHomeomorph i ν I
  have hA : IsCuspidal (parabolic j ν) (levi j ν) (unipotent j ν)
      fam.decomposition fam.closedUnipotent
      (SmoothRep.pullback e (bernsteinLiteralLeviRep i ν I a.representation)) :=
    (rationalLeviCuspidalityTransport dynamicLie standardCocharacter
      F G family.connectedReductive T i family.maximalSplitTorus ν
      family.genericCocharacter I fam.connectedReductive family.closedUnipotent
      fam.closedUnipotent (family.closedLevi I) (family.leviDecomposition I)
      fam.decomposition (bernsteinLiteralLeviRep i ν I a.representation)).mpr a.cuspidal
  have hπ : IsCuspidal (parabolic j ν) (levi j ν) (unipotent j ν)
      fam.decomposition fam.closedUnipotent a.representation :=
    IsCuspidalFor.of_iso hA (SmoothRep.pullbackSymmIso e.symm a.representation).symm
  exact hSplit F L fam.connectedReductive T j fam.maximalSplitTorus ν
    fam.genericCocharacter standardCocharacter hRoots fam.closedUnipotent
    a.representation a.irreducible hπ

/-- The block projection on the literal standard Levi subgroup `levi i ν a.roots`.
Assuming Renard VI.3.3.1, every smooth representation `W` of the literal Levi has
a map `p` to the literal form of an object `τ` of the inertia block of `a`, and a
map `j` back, such that every morphism from the literal form of a block object
into `W` is recovered after composing with `p ≫ j`. -/
theorem bernsteinLeviInertiaProjection
    (hSplit : RationalCuspidalInertiaDecompositionStatement.{uF, max uF uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (W : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν a.roots)) :
    ∃ (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)))
      (p : W ⟶ bernsteinLiteralLeviRep i ν a.roots τ)
      (j : bernsteinLiteralLeviRep i ν a.roots τ ⟶ W),
      rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ ∧
        ∀ (Y : SmoothRep.{0, uF, max uF uV} ℂ
            (rationalPoints (bernsteinLeviScheme i ν a.roots))),
          rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation Y →
            ∀ f : bernsteinLiteralLeviRep i ν a.roots Y ⟶ W, f ≫ p ≫ j = f := by
  let e := leviRationalPointHomeomorph i ν a.roots
  obtain ⟨τ, p', j', hτ, hfac⟩ := exists_rationalInertiaBlockProjection
    (bernsteinLeviScheme i ν a.roots) a.representation
    (bernsteinLevi_isRationalInertiaCategoryDecomposition i ν family hSplit a)
    (SmoothRep.pullback e W)
  refine ⟨τ, (SmoothRep.pullbackSymmIso e W).inv ≫ (SmoothRep.pullbackFunctor e.symm).map p',
    (SmoothRep.pullbackFunctor e.symm).map j' ≫ (SmoothRep.pullbackSymmIso e W).hom,
    hτ, fun Y hY f => ?_⟩
  have hY' : rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation
      (SmoothRep.pullback e (bernsteinLiteralLeviRep i ν a.roots Y)) :=
    rationalInertiaBlockProperty_of_iso hY (SmoothRep.pullbackSymmIso e.symm Y)
  have h' := hfac _ hY' ((SmoothRep.pullbackFunctor e).map f)
  apply SmoothRep.hom_ext'
  ext v
  have hv := congrArg (fun g => (SmoothRep.hom g).toLinearMap) h'
  exact LinearMap.congr_fun hv v

/-- A nonzero morphism from the literal form of a block object stays nonzero
after the block projection of `bernsteinLeviInertiaProjection`. -/
theorem bernsteinLeviInertiaProjection_ne_zero
    (hSplit : RationalCuspidalInertiaDecompositionStatement.{uF, max uF uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (W : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν a.roots)) :
    ∃ (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)))
      (p : W ⟶ bernsteinLiteralLeviRep i ν a.roots τ),
      rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ ∧
        ∀ (Y : SmoothRep.{0, uF, max uF uV} ℂ
            (rationalPoints (bernsteinLeviScheme i ν a.roots))),
          rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation Y →
            ∀ f : bernsteinLiteralLeviRep i ν a.roots Y ⟶ W, f ≠ 0 → f ≫ p ≠ 0 := by
  obtain ⟨τ, p, j, hτ, hfac⟩ := bernsteinLeviInertiaProjection i ν family hSplit a W
  refine ⟨τ, p, hτ, fun Y hY f hf h0 => hf ?_⟩
  rw [← hfac Y hY f, ← Category.assoc, h0, zero_comp]

/-- The Levi-side block projection for every Bernstein cuspidal datum, as one
proposition: assuming Renard VI.3.3.1, for every datum `a` and every smooth
representation `W` of the literal standard Levi of `a` there are an object `τ`
of the inertia block of `a.representation` and a map `p` from `W` to the
literal form of `τ` that is nonzero on every nonzero map from the literal form
of a block object. -/
theorem bernsteinLeviBlockProjection_of_rationalInertiaDecomposition
    (hSplit : RationalCuspidalInertiaDecompositionStatement.{uF, max uF uV}) :
    ∀ (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
      (W : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν a.roots)),
      ∃ (τ : SmoothRep.{0, uF, max uF uV} ℂ
          (rationalPoints (bernsteinLeviScheme i ν a.roots)))
        (p : W ⟶ bernsteinLiteralLeviRep i ν a.roots τ),
        rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ ∧
        ∀ Y : SmoothRep.{0, uF, max uF uV} ℂ
            (rationalPoints (bernsteinLeviScheme i ν a.roots)),
          rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation Y →
          ∀ f : bernsteinLiteralLeviRep i ν a.roots Y ⟶ W, f ≠ 0 → f ≫ p ≠ 0 :=
  fun a W => bernsteinLeviInertiaProjection_ne_zero.{uF, uV} i ν family hSplit a W

set_option linter.defProp false in
/-- The reduction of the Levi-side block projection to Renard VI.3.3.1, as a
declaration whose type is the implication. -/
def bernsteinLeviBlockProjectionOfRationalInertiaDecomposition :
    RationalCuspidalInertiaDecompositionStatement.{uF, max uF uV} →
      ∀ (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
        (W : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν a.roots)),
        ∃ (τ : SmoothRep.{0, uF, max uF uV} ℂ
            (rationalPoints (bernsteinLeviScheme i ν a.roots)))
          (p : W ⟶ bernsteinLiteralLeviRep i ν a.roots τ),
          rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ ∧
          ∀ Y : SmoothRep.{0, uF, max uF uV} ℂ
              (rationalPoints (bernsteinLeviScheme i ν a.roots)),
            rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation Y →
            ∀ f : bernsteinLiteralLeviRep i ν a.roots Y ⟶ W, f ≠ 0 → f ≫ p ≠ 0 :=
  bernsteinLeviBlockProjection_of_rationalInertiaDecomposition.{uF, uV} i ν family

end Bernstein

end Langlands.CuspidalSupport
