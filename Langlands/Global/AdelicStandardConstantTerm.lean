import Langlands.Automorphic.GroupSchemeInvariantFormsSubmodule
import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.EisensteinConstantTerm.Points
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality

/-! # Constant terms of functions on nested standard parabolic quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Index" => StandardIndex F G fam.i fam.ν
local notation "Y" => (AdelicGroupPoints F G → ℂ)

section Nested

variable (P Q : StandardIndex F G fam.i fam.ν)

local notation "UQ" => SubgroupFunctor.range (fam.iU Q ≫ fam.p Q)
local notation "ΓQ" => AdelicSubgroupPoints.rationalSubgroup F G UQ
local notation "μQ" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G UQ
local notation "ΓP" => parabolicQuotientSubgroup F (fam.p P) (fam.iU P) (fam.l P)

private theorem rationalRadicalImage_le_parabolicQuotientSubgroup (hQP : Q ≤ P) :
    rationalImage F (fam.iU Q ≫ fam.p Q) ≤ ΓP := by
  have hle : UQ ≤ SubgroupFunctor.range (fam.p P) :=
    (SubgroupFunctor.range_comp_le _ _).trans ((fam.le_iff_range_le Q P).mp hQP)
  let : IsClosedImmersion (fam.p P).hom.hom.left := (fam.isCompatible P).parabolic.isClosedSubgroup
  have hcomp := SubgroupFunctor.rangeFactor_comp (fam.iU Q ≫ fam.p Q) (fam.p P) hle
  rw [← hcomp]
  exact (rationalImage_comp_le _ _).trans (rationalImage_le_parabolicQuotientSubgroup _ _ _
    (fam.isCompatible P).levi (fam.isUnipotentRadical P))

/-- Continuity and the rational invariance of an inducing function give
absolute integrability over the smaller standard radical quotient. -/
theorem integrable_constantTermIntegrand_of_le (hQP : Q ≤ P) {f : Y} (hcont : Continuous f)
    (hinv : ∀ x ∈ ΓP, ∀ g, f (x * g) = f g) (g : AdelicGroupPoints F G) :
    letI : IsClosed (AdelicSubgroupPoints.adelicPoints F G UQ : Set (AdelicGroupPoints F G)) :=
      AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU Q ≫ fam.p Q)
    Integrable (fun q : AdelicSubgroupPoints.RationalQuotient F G UQ =>
      f (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G UQ) :
        AdelicGroupPoints F G) * g)) μQ := by
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G UQ : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU Q ≫ fam.p Q)
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G UQ) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F
      (fam.iU Q ≫ fam.p Q) (fam.isUnipotentRadical Q).1.smooth
        (fam.isUnipotentRadical Q).1.connectedSpace (fam.isUnipotentRadical Q).1.isUnipotent
  let : IsProbabilityMeasure μQ :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G UQ
  let : BorelSpace (AdelicSubgroupPoints.RationalQuotient F G UQ) :=
    AdelicSubgroupPoints.rationalQuotientBorelSpace F G UQ
  let l := LeftCosetSpace.lift ΓQ
    (fun x : AdelicSubgroupPoints.adelicPoints F G UQ => f ((x : AdelicGroupPoints F G) * g))
    (fun x y => by
      change f (((x.val : AdelicGroupPoints F G) * y.val) * g) = f (y.val * g)
      rw [mul_assoc]
      exact hinv _ (fam.rationalRadicalImage_le_parabolicQuotientSubgroup P Q hQP
        ((mem_rationalSubgroup_range_iff _ x.val).mp x.2)) _)
  have hl : Continuous l :=
    (LeftCosetSpace.continuous_iff ΓQ).mpr (hcont.comp (continuous_subtype_val.mul continuous_const))
  have heq : (fun q : AdelicSubgroupPoints.RationalQuotient F G UQ =>
      f (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G UQ) :
        AdelicGroupPoints F G) * g)) = l := by
    funext q
    exact congrArg l (Quotient.out_eq q)
  rw [heq]
  exact hl.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

variable {N d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

local notation "Aut" => automorphicFunctionsOn (F := F) (G := G) ΓP Kinf rho hsmooth
  (adelicDifferentialCommutator_of_smooth F G hsmooth)

/-- The normalized constant term is linear on the original automorphic
function space of any larger standard parabolic. -/
def constantTermLinear (hQP : Q ≤ P) : Aut →ₗ[ℂ] Y where
  toFun f := fam.constantTerm Q f.val
  map_add' f h := by
    funext g
    have hint (v : Aut) := fam.integrable_constantTermIntegrand_of_le P Q hQP v.2.2.1.1 v.2.1 g
    change fam.constantTerm Q (f.val + h.val) g =
      fam.constantTerm Q f.val g + fam.constantTerm Q h.val g
    unfold constantTerm subgroupConstantTerm
    simpa only [Pi.add_apply] using integral_add (hint f) (hint h)
  map_smul' c f := by
    funext g
    change fam.constantTerm Q (c • f.val) g = c • fam.constantTerm Q f.val g
    unfold constantTerm subgroupConstantTerm
    simpa only [Pi.smul_apply] using integral_smul c
      (fun q : AdelicSubgroupPoints.RationalQuotient F G UQ =>
        f.val (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G UQ) :
          AdelicGroupPoints F G) * g))

end Nested

section Cuspidality

variable {N d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

theorem isAutomorphicOn_zero (P : Index) : fam.IsAutomorphicOn hsmooth Kinf rho P 0 :=
  (automorphicFunctionsOn (parabolicQuotientSubgroup F (fam.p P) (fam.iU P) (fam.l P))
    Kinf rho hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)).zero_mem

theorem isCuspidalAlong_zero (P : Index) : fam.IsCuspidalAlong P 0 := by
  intro Q _
  funext g
  unfold constantTerm subgroupConstantTerm
  exact integral_zero _ _

/-- The difference of two cuspidal inducing forms remains cuspidal. -/
theorem isCuspidalAlong_sub (P : Index) {f h : Y}
    (hf : fam.IsAutomorphicOn hsmooth Kinf rho P f)
    (hh : fam.IsAutomorphicOn hsmooth Kinf rho P h)
    (hfC : fam.IsCuspidalAlong P f) (hhC : fam.IsCuspidalAlong P h) :
    fam.IsCuspidalAlong P (f - h) := by
  intro Q hQ
  let L := fam.constantTermLinear P Q hsmooth Kinf rho hQ.le
  calc
    fam.constantTerm Q (f - h) = L (⟨f, hf⟩ - ⟨h, hh⟩) := rfl
    _ = L ⟨f, hf⟩ - L ⟨h, hh⟩ := map_sub _ _ _
    _ = 0 := by
      change fam.constantTerm Q f - fam.constantTerm Q h = 0
      rw [hfC Q hQ, hhC Q hQ, sub_zero]

end Cuspidality

/-- Averaging a function already invariant under the radical leaves it unchanged. -/
theorem constantTerm_eq_self_of_unipotent_invariant (J : Index) {f : Y}
    (hinv : ∀ x ∈ parabolicUnipotentImage F (fam.p J) (fam.iU J), ∀ g, f (x * g) = f g) :
    fam.constantTerm J f = f := by
  let V := SubgroupFunctor.range (fam.iU J ≫ fam.p J)
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU J ≫ fam.p J)
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G V) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (fam.iU J ≫ fam.p J)
      (fam.isUnipotentRadical J).1.smooth (fam.isUnipotentRadical J).1.connectedSpace
        (fam.isUnipotentRadical J).1.isUnipotent
  let : IsProbabilityMeasure (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V) :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  funext g
  unfold constantTerm subgroupConstantTerm
  have heq : (fun q : AdelicSubgroupPoints.RationalQuotient F G V =>
      f (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G V) :
        AdelicGroupPoints F G) * g)) = fun _ => f g := by
    funext q
    exact hinv _ (Quotient.out q : AdelicSubgroupPoints.adelicPoints F G V).2 g
  rw [heq, integral_const]
  simp only [Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul]

/-- An automorphic function on a standard parabolic quotient is fixed by
the constant term of that parabolic. -/
theorem constantTerm_eq_self_of_automorphicOn {N d : ℕ}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)} {rho : MatrixRepresentation G (Fin N)}
    (J : Index) {f : Y} (hf : fam.IsAutomorphicOn hsmooth Kinf rho J f) :
    fam.constantTerm J f = f :=
  fam.constantTerm_eq_self_of_unipotent_invariant J
    (fun x hx => hf.1 x (Subgroup.mem_sup_left hx))

end Langlands.Global.StandardParabolicFamily
