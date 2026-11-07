import Langlands.Representation.Plancherel.RationalCuspidalInductionCompression
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetFinitenessStatement
import Langlands.Representation.Exponents.RepresentedCuspidalityComparison
import Langlands.Representation.Aubert.General.IrreducibleAdmissibleStatement
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.GroupScheme.Rational.LeviPreimageSolvableRadical
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Native Jacquet inputs for standard cuspidal inducing objects -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Aubert.General Aubert.General.RationalPointFamily

universe u uV

section Standardization

variable {F : Type u} [Field F]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ H) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  [Fintype (SimpleRoot i ν)]

/-- Standardize the originally supplied proper rational radical without
requiring a chosen Levi in the input. -/
def properRationalRadicalStandardization
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hH : IsConnectedReductive H) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    {Q U : GroupScheme (Spec (CommRingCat.of F))}
    (q : Q ⟶ H) (n : U ⟶ Q) (hq : IsParabolicSubgroup q)
    (hproper : SubgroupFunctor.range q ≠ ⊤)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n) :
    RepresentedParabolic.ProperParabolicUnipotentStandardization i ν q n := by
  apply Classical.choice
  obtain ⟨L, l, hl⟩ :=
    hq.exists_isRationalLeviSubgroup hPD dynamicCentralizerReductive hH
  have hnotiso : ¬ IsIso q := by
    intro hiso
    let := hiso
    have : IsIso q.hom.hom := (Grp.forget (Over _)).map_isIso q
    apply hproper
    apply SubgroupFunctor.ext
    intro S
    apply top_unique
    intro x _
    refine ⟨x ≫ inv q.hom.hom, ?_⟩
    change (x ≫ inv q.hom.hom) ≫ q.hom.hom = x
    simp
  exact ⟨RepresentedParabolic.properParabolicUnipotentStandardization
    i ν hPD hconj hH hi hν hRoots q l n hq hl hn hnotiso⟩

variable [TopologicalSpace F] [T2Space F]

local instance standardNativeGroupAffine : IsAffine H.X.left :=
  isAffine_of_isAffineHom H.X.hom
local instance standardNativePointTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X

variable [LocallyCompactSpace (rationalPoints H)]
  [NonarchimedeanGroup (rationalPoints H)]

omit [T2Space F] in
/-- Proper-standard cuspidality implies the all-proper-rational vanishing
predicate used by the native Jacquet finiteness statement. -/
theorem properRationalJacquetVanishing_of_isCuspidal
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hH : IsConnectedReductive H) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    (h : ∀ I, IsSemidirectDecomposition
      (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints H)))
    (B : SmoothRep.{0, u, uV} ℂ (rationalPoints H))
    (hB : IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU B) :
    ProperRationalJacquetVanishing B.representation := by
  intro Q U q n hq hproper hn
  let s := properRationalRadicalStandardization i ν hPD hconj hH hi hν hRoots
    q n hq hproper hn
  have hvanish := hB ⟨s.face, s.proper⟩
  change Subsingleton (Jacquet.Localization.Coinvariants B.representation
    (unipotent i ν s.face) 1) at hvanish
  change Subsingleton (Jacquet.Localization.Coinvariants B.representation
    (RepresentedParabolic.pointImage (n ≫ q)) 1)
  let := hvanish
  exact (coinvariantsTranslateEquiv s.conjugatingPoint
    s.radicalPoints B.representation).injective.subsingleton

end Standardization

namespace RationalNormalized

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance standardNativeAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance standardNativeAmbientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance standardNativeLeviTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X
local instance standardNativeFieldT2 : T2Space F := BruhatTits.localField_t2Space F

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType M.X.hom] in
/-- Pulling the literal Levi representation back to its original scheme
recovers the exact original action on the unchanged carrier. -/
theorem leviSchemeRepresentation_literalLeviRep
    (B : SmoothRep.{0, u, uV} ℂ (rationalPoints M)) :
    leviSchemeRepresentation r (literalLeviRep r B).representation =
      B.representation := by
  ext m v
  change B.representation
    ((parabolicLeviPointHomeomorph r).symm (parabolicLeviPointHomeomorph r m)) v =
      B.representation m v
  rw [(parabolicLeviPointHomeomorph r).symm_apply_apply]

variable [LocallyCompactSpace (rationalPoints M)]
  [NonarchimedeanGroup (rationalPoints M)]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ M) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  [Fintype (SimpleRoot i ν)]
  (hL : ∀ J, IsSemidirectDecomposition
    (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (hUL : ∀ J, IsClosed (unipotent i ν J : Set (rationalPoints M)))

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType M.X.hom] in
/-- The actual literal inducing representation satisfies the native
supercuspidality predicate when the original object is standard cuspidal. -/
theorem isSupercuspidal_literalLeviRep_of_isCuspidal
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hM : IsConnectedReductive M) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    (B : SmoothRep.{0, u, uV} ℂ (rationalPoints M))
    (hB : IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hL hUL B) :
    IsSupercuspidal r (literalLeviRep r B).representation := by
  refine ⟨(literalLeviRep r B).isSmooth, ?_⟩
  rw [leviSchemeRepresentation_literalLeviRep]
  exact properRationalJacquetVanishing_of_isCuspidal i ν hPD hconj hM hi hν
    hRoots hL hUL B hB

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))

omit [LocallyOfFiniteType M.X.hom] in
/-- The named irreducible-admissibility and native universal-Jacquet
statements supply exactly the native bundle consumed by cuspidal compression. -/
theorem rationalCuspidalNativeJacquetInputs_of_statements
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hM : IsConnectedReductive M) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    (hG : IsConnectedReductive G) (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hr : Continuous h.projection)
    (hCompact : CompactSpace (Induction.LeftQuotient (ParabolicPoints p)))
    (hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, max u uV})
    (hJac : RationalSupercuspidalJacquetFamilyFiniteStatement.{u, max u uV}) :
    RationalCuspidalNativeJacquetInputs.{u, uV} r h hU i ν hL hUL := by
  intro B hB hcB
  have ha : B.IsAdmissible := hAdm F M hM B hB
  refine ⟨ha, ?_⟩
  exact hJac F G hG A M P U p l a r n hn h hU hr hCompact B
    (literalLeviRep r B).representation (literalLeviRep r B).isSmooth
    (isAdmissible_comp_continuousMulEquiv B.representation
      (parabolicLeviPointHomeomorph r).symm ha)
    ((isIrreducible_comp_continuousMulEquiv_iff B.representation
      (parabolicLeviPointHomeomorph r).symm).mpr hB)
    (isSupercuspidal_literalLeviRep_of_isCuspidal r i ν hL hUL hPD hconj hM hi hν
      hRoots B hcB)

end RationalNormalized

end Langlands.Plancherel
