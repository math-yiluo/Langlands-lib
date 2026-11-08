import Langlands.Representation.Plancherel.RegularJacquetMultiplicityStatement
import Langlands.Representation.Plancherel.ParabolicRepresentedComparison
import Langlands.Representation.Aubert.General.JacquetMultiplicityIrreducibility
import Langlands.Representation.Aubert.General.RationalUnitaryInductionIrreducibility
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityStatement
import Langlands.Representation.Aubert.General.SemidirectModularCharacter
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LeftHaarSquareIntegrableUnitarity
import Langlands.Representation.Smooth.IrreducibleRealization

/-! # Irreducibility of actual unramified induction at regular unitary points -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uV

open Aubert.General

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} {n : U ⟶ P}
  (pres : ParabolicRootPresentation p l a)

local instance unitaryPointAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance unitaryPointAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance unitaryPointLeviPointTopology :
    TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
local instance unitaryPointFieldT2 : T2Space F := BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]
  (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (h : IsSemidirectDecomposition
    ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
    (parabolicLeviPointSubgroup p l)
    ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))))
  (hU : IsClosed (((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))) :
    Set (rationalPoints G)))

include pres hn in
/-- Unimodularity of the actual reductive groups gives the modular character
of the literal parabolic as the Haar modulus of conjugation on its radical. -/
theorem parabolic_modularCharacter_eq
    (hunimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : GroupScheme.StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G)
    (hP : IsClosed (((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _))) :
      Set (rationalPoints G)))
    (hr : Continuous h.projection) :
    haveI : LocallyCompactSpace ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _))) :=
      hP.locallyCompactSpace
    ∀ q : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)),
      modularCharacter q =
        (HaarModulus.closedRestrictCharacter _ hU _ h.le_normalizer q : ℝ≥0) := by
  have : LocallyCompactSpace ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _))) :=
    hP.locallyCompactSpace
  have : LocallyCompactSpace (parabolicLeviPointSubgroup p l) :=
    (isClosed_parabolicLeviPointSubgroup pres).locallyCompactSpace
  have : LocallyCompactSpace ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))) :=
    hU.locallyCompactSpace
  have : SecondCountableTopology (rationalPoints G) :=
    Aubert.General.RationalPointFamily.reductiveRationalPoint_secondCountable F G hG
  have hM := pres.isCompatible.levi.isConnectedReductive
  let e := parabolicLeviPointHomeomorph pres
  have : LocallyCompactSpace (rationalPoints M) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : IsTopologicalGroup (rationalPoints M) :=
    e.toHomeomorph.isInducing.isTopologicalGroup e.toMonoidHom
  have : NonarchimedeanGroup (rationalPoints M) :=
    NonarchimedeanGroup.nonarchimedean_of_emb
      e.symm.toMonoidHom e.symm.toHomeomorph.isOpenEmbedding
  have : T2Space (rationalPoints M) := e.toHomeomorph.isEmbedding.t2Space
  have hMunimod (m : parabolicLeviPointSubgroup p l) : modularCharacter m = 1 := by
    have hm := hunimod F M hM hStandard (e.symm m)
    simpa only [e.apply_symm_apply] using
      (modularCharacter_continuousMulEquiv e (e.symm m)).trans hm
  have hδ := parabolicRadical_isUnimodular F G hG A M P U p l a n pres hn hU
  intro q
  simpa only [HaarModulus.closedRestrictCharacter_eq] using
    h.modularCharacter_eq_restrictCharacter_of_unimodular hr hMunimod
      (fun u => by simpa using hδ u) q

include pres hn in
set_option maxHeartbeats 800000 in
/-- At an unramified unitary point where the twisted inducing representation is
regular for the literal normalizer, the actual Levi-normalized induction of an
irreducible representation that is square-integrable modulo the split center
is irreducible, given the multiplicity bound. -/
theorem unramifiedLeviInduction_isIrreducible_of_unitary_regular
    (hmult : RegularSquareIntegrableJacquetMultiplicityStatement.{u, uV})
    (hunimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : GroupScheme.StandardCocharacterStatement.{u})
    (hcompact : RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement.{u})
    (hG : IsConnectedReductive G)
    (hP : IsClosed (((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _))) :
      Set (rationalPoints G)))
    (hr : Continuous h.projection)
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) (hirr : π.IsIrreducible) :
    let C := (parabolicSplitComponentPointHom pres).range
    let hC := parabolicSplitComponentPointHom_range_le_center pres
    letI : C.Normal := C.normal_of_le_center hC
    ∀ [MeasurableSpace (parabolicLeviPointSubgroup p l ⧸ C)]
      [BorelSpace (parabolicLeviPointSubgroup p l ⧸ C)]
      (qMeasure : Measure (parabolicLeviPointSubgroup p l ⧸ C)) [IsHaarMeasure qMeasure],
      IsSquareIntegrableModCentralSubgroup C hC π.representation qMeasure →
      ∀ χ : unramifiedCharacters (parabolicLeviRationalNormCharacters pres),
        (∀ m, ‖(χ.val m : ℂ)‖ = 1) →
        IsNormalizerRegular (π.twist χ.val.toMonoidHom
          (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters pres) χ)) →
        (UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters pres) χ
          π).IsIrreducible := by
  intro C hC _ _ qMeasure _ hsq χ hχu hreg
  have : C.Normal := C.normal_of_le_center hC
  have := hG.smooth
  let ψ := χ.val.toMonoidHom
  have hψ := unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters pres) χ
  let π' := π.twist ψ hψ
  have hirr' : π'.IsIrreducible := (SmoothRep.isIrreducible_twist_iff ψ hψ π).mpr hirr
  have hsq' : IsSquareIntegrableModCentralSubgroup C hC π'.representation qMeasure :=
    isSquareIntegrableModCentralSubgroup_unitaryTwist C hC ψ hψ hχu qMeasure hsq
  have hδ := parabolicRadical_isUnimodular F G hG A M P U p l a n pres hn hU
  have hdimL := hmult F G hG A M P U p l a n pres hn h hU hP hr qMeasure π' hirr' hsq' hreg
  let E := (DynamicNormalization.normalizedInductionLeviTwistIso h hU hδ).app π'
  have hdim : Module.rank ℂ (((jacquetFunctor h hU).obj
      ((normalizedInductionFunctor h hU).obj π')).representation.IntertwiningMap
        π'.representation) ≤ 1 := by
    rw [(intertwiningPrecompLinearEquiv
      (SmoothRep.equivOfIso ((jacquetFunctor h hU).mapIso E)) _).rank_eq]
    exact hdimL
  have : CompactSpace (Induction.LeftQuotient
      ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))) := by
    rw [← RepresentedParabolic.pointImage_eq_range_carrier]
    exact hcompact F G hG P p pres.isCompatible.parabolic
  have : LocallyCompactSpace ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _))) :=
    hP.locallyCompactSpace
  have : LocallyCompactSpace (parabolicLeviPointSubgroup p l) :=
    (isClosed_parabolicLeviPointSubgroup pres).locallyCompactSpace
  have hGmod : ∀ g : rationalPoints G, modularCharacter g = 1 :=
    hunimod F G hG hStandard
  have hmod := parabolic_modularCharacter_eq pres hn h hU hunimod hStandard hG hP hr
  have hπ'unit : IsUnitarizable π'.representation :=
    HarishChandraSchwartz.isUnitarizable_of_irreducible_isSquareIntegrable_leftHaar C hC
      qMeasure (compactOpenCofinal_of_nonarchimedean (parabolicLeviPointSubgroup p l))
      hsq' hirr'
  borelize (rationalPoints G)
  have hunitary := normalizedInductionFunctor_obj_isUnitarizable_of_compactSpace h hU hP
    hGmod hmod π' hπ'unit
  have hadm := normalizedInductionFunctor_obj_isAdmissible h hU hr π' hsq'.1
  have : Nontrivial π' := by
    have : IsSimpleModule (MonoidAlgebra ℂ (parabolicLeviPointSubgroup p l))
        π'.representation.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr'
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (parabolicLeviPointSubgroup p l))
      π'.representation.asModule
  exact SmoothRep.isIrreducible_of_iso E
    (isIrreducible_induction_of_unitary_jacquetHom_rank_le_one h hU hδ π' hr
      (compactOpenCofinal_of_nonarchimedean (rationalPoints G)) hadm hunitary hdim)

/-- Irreducibility of the actual Levi-normalized parabolic induction at every
unitary unramified point where the twisted inducing representation is regular
for the literal normalizer, for irreducible inducing representations that are
square-integrable modulo the split center. The structural context is that of
`ConditionalParabolicGenericIrreducibilityStatement`. -/
def UnitaryRegularParabolicIrreducibilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [T2Space (rationalPoints G)]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (M P U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine M.X.left]
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (n : U ⟶ P)
      (r : ParabolicRootPresentation p l a)
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n),
      let Ppt := (SubgroupFunctor.range p).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))
      let Mpt := parabolicLeviPointSubgroup p l
      let Upt := (SubgroupFunctor.range (n ≫ p)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))
      ∀ (h : IsSemidirectDecomposition Ppt Mpt Upt)
        (hU : IsClosed (Upt : Set (rationalPoints G)))
        (_hP : IsClosed (Ppt : Set (rationalPoints G)))
        (_hr : Continuous h.projection),
        let C := (parabolicSplitComponentPointHom r).range
        let hC := parabolicSplitComponentPointHom_range_le_center r
        letI : C.Normal := C.normal_of_le_center hC
        ∀ [MeasurableSpace (Mpt ⧸ C)] [BorelSpace (Mpt ⧸ C)]
          (qMeasure : Measure (Mpt ⧸ C)) [IsHaarMeasure qMeasure]
          (π : SmoothRep.{0, u, uV} ℂ Mpt),
          π.IsIrreducible →
          IsSquareIntegrableModCentralSubgroup C hC π.representation qMeasure →
          ∀ χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r),
            (∀ m, ‖(χ.val m : ℂ)‖ = 1) →
            IsNormalizerRegular (π.twist χ.val.toMonoidHom
              (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r) χ)) →
            (UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r) χ
              π).IsIrreducible

/-- The reduction: the regular square-integrable Jacquet multiplicity bound,
unimodularity of actual reductive groups, the standard-cocharacter structure
statement and compactness of actual parabolic quotients give irreducibility at
regular unitary points. -/
def UnitaryRegularParabolicIrreducibilityReductionStatement : Prop :=
  RegularSquareIntegrableJacquetMultiplicityStatement.{u, uV} →
    RationalPointFamily.RationalReductiveUnimodularityStatement.{u} →
      GroupScheme.StandardCocharacterStatement.{u} →
        RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement.{u} →
          UnitaryRegularParabolicIrreducibilityStatement.{u, uV}

/-- The reduction holds. -/
theorem unitaryRegularParabolicIrreducibility_of_statements :
    UnitaryRegularParabolicIrreducibilityReductionStatement.{u, uV} := by
  intro hmult hunimod hStandard hcompact F _ _ _ _ G hG _ _ _ A M P U _ p l a n r hn
    Ppt Mpt Upt h hU hP hr C hC _ _ qMeasure _ π hirr hsq χ hχu hreg
  have := hG.isAffineHom
  exact unramifiedLeviInduction_isIrreducible_of_unitary_regular r hn h hU hmult hunimod
    hStandard hcompact hG hP hr π hirr qMeasure hsq χ hχu hreg

end Langlands.Plancherel
