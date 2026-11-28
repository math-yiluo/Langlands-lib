import Langlands.Global.AdelicStandardBruhatConstantTerm
import Langlands.Global.AdelicWeakConstantTermDirectness
import Langlands.Global.AdelicSplitComponentShifts
import Langlands.Analysis.Meromorphic.LinearCoordinates

/-! # The weak constant term of an adelic Eisenstein series -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions
  Langlands.Analysis.Meromorphic

namespace StandardParabolicFamily.StandardBruhatConstantTermData

universe u

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {fam : StandardParabolicFamily F G} {I J : StandardIndex F G fam.i fam.ν}
  (b : StandardBruhatConstantTermData fam I J)

/-- The Levi retraction of the target intersection parabolic itself. -/
def targetLeviRetraction (w : b.Index) : fam.P (b.targetIndex w) ⟶ fam.M (b.targetIndex w) :=
  ((fam.standardNestedLeviParabolic (b.targetIndex w) (b.targetIndex w) le_rfl).some).projection

omit [NumberField F] in
@[simp] theorem targetLeviRetraction_comp (w : b.Index) :
    fam.l (b.targetIndex w) ≫ b.targetLeviRetraction w = 𝟙 (fam.M (b.targetIndex w)) :=
  ((fam.standardNestedLeviParabolic (b.targetIndex w) (b.targetIndex w) le_rfl).some).section_projection

/-- Restrict a source parameter to the source intersection and transport it by the Weyl
conjugation to the target intersection parabolic. -/
def transportedParameter (w : b.Index) :
    ComplexCharacterParameter F (fam.P I) →ₗ[ℂ] ComplexCharacterParameter F (fam.P (b.targetIndex w)) :=
  (weylParameter (fam.l (b.sourceIndex w)) (b.piece w).conjugation (b.targetLeviRetraction w)).comp
    (parameterRestrict (b.piece w).source.inclusion)

/-- The Weyl parameter evaluated on the positive split component of the full target parabolic. -/
def splitWeylCharacter (w : b.Index) (lam : ComplexCharacterParameter F (fam.P I))
    (x : fam.positiveSplitComponent J) : ℂ :=
  parameterPower F (fam.P (b.targetIndex w)) (b.transportedParameter w lam)
    (fam.splitLift (b.targetIndex_le w) x).val

/-- Weyl transport and restriction give a unitary character on the imaginary axis. -/
theorem norm_splitWeylCharacter_imaginary (w : b.Index)
    (lam : RealCharacterParameter F (fam.P I)) (x : fam.positiveSplitComponent J) :
    ‖b.splitWeylCharacter w (imaginaryParameter F (fam.P I) lam) x‖ = 1 := by
  have h : parameterRealPart F (fam.P (b.targetIndex w))
      (b.transportedParameter w (imaginaryParameter F (fam.P I) lam)) = 0 := by
    induction lam using TensorProduct.inductionOn with
    | tmul t χ =>
      simp [transportedParameter, parameterRestrict, imaginaryParameter, AlgebraTensorModule.map_tmul,
        weylParameter_tmul]
    | add u v hu hv => simp only [map_add, hu, hv, add_zero]
  rw [splitWeylCharacter, parameterPower, Complex.norm_exp, complexParameterPairing_re, h]
  simp

end StandardParabolicFamily.StandardBruhatConstantTermData

/-- Delorme (4.3). Continue the relative Eisenstein terms with full source intersection
from the actual convergent Bruhat summands. On the entire imaginary axis each term is
automorphic on the target parabolic quotient and transforms by the normalized Weyl
character there. Their sum is the actual unitary weak constant term of the given
Eisenstein continuation. -/
def EisensteinWeakBruhatConstantTermStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (I J : StandardIndex F G fam.i fam.ν)
    (b : fam.StandardBruhatConstantTermData I J)
    (K : Subgroup (AdelicGroupPoints F G)) (hKI : IsIwasawaCompact (fam.p I) K)
    (hKmin : IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K),
    IsMaximalCompactSubgroup F G K →
    (∀ L, IsMaximalCompactSubgroup F (fam.M L)
      (K.comap (map F (fam.M L) G (fam.l L ≫ fam.p L)).toMonoidHom)) →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom),
      IsClosedSubgroup rho →
    ∀ (φ : AdelicGroupPoints F G → ℂ),
      IsSquareIntegrableInducedForm K hKI.isCompact rho hsmooth
        (adelicDifferentialCommutator_of_smooth F G hsmooth) (fam.p I) (fam.iU I) (fam.l I) φ →
    ∀ [IsClosedImmersion (fam.p I).hom.hom.left]
      (r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I))
      [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
      [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
      (hA : IsSplitTorus (fam.A I).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
      (E : ComplexCharacterParameter F (fam.P I) → AdelicGroupPoints F G → ℂ)
      (DE : Set (ComplexCharacterParameter F (fam.P I))),
      Set.range (imaginaryParameter F (fam.P I)) ⊆ DE →
      (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) DE) →
      (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hKI.eisensteinSeries φ lam) →
    ∃ (term : b.FullSourceIndex → ComplexCharacterParameter F (fam.P I) → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F (fam.P I))),
      Set.range (imaginaryParameter F (fam.P I)) ⊆ D ∧
      (∀ w g, IsMeromorphicInCoordinatesOn (fun lam => term w lam g) D) ∧
      (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
        ∀ w : b.FullSourceIndex, term w lam = b.summand hKmin w.val φ lam) ∧
      ∀ x : RealCharacterParameter F (fam.P I),
        let lam := imaginaryParameter F (fam.P I) x
        let Kinf := K.comap (ofInfinite F G).toMonoidHom
        (∀ w : b.FullSourceIndex, fam.IsAutomorphicOn hsmooth Kinf rho J (term w lam) ∧
          ∀ a : fam.positiveSplitComponent J,
            fam.normalizedAction J a.val (term w lam) = b.splitWeylCharacter w.val lam a • term w lam) ∧
        fam.IsWeakConstantTerm hsmooth Kinf rho J (E lam) (∑ w : b.FullSourceIndex, term w lam)

end Langlands.Global
