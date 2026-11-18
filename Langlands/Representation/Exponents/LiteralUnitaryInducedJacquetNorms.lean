import Langlands.Representation.Exponents.UnitaryInducedJacquetNorms
import Langlands.Representation.Aubert.General.InductionCarrierTransport
import Langlands.Representation.Plancherel.UnramifiedCharacterTransport
import Langlands.Representation.Smooth.IrreducibleRealization

/-! # Full unitary induced Jacquet exponent norms on literal point subgroups -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Plancherel

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U Q L V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance literalUnitaryInducedNormAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
  (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))

/-- Pulling a literal Levi action to its actual scheme and twisting there,
then inducing, is equivalent to twisting the original literal action by the
transported actual unramified character and inducing from that same subgroup. -/
def literalLeviUnramifiedInductionEquiv
    (τ : SmoothRep.{0, u, v} ℂ (pointImage (l ≫ p))) :
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ ψ : unramifiedCharacters
        (fun c : rationalCharacters M => (rationalNormCharacters M c).toMul),
      ((leviInductionFunctor p l r hp hr hl hmul).obj
        ((SmoothRep.pullback (leviPointsEquiv p l hp hl) τ).twist ψ.val.toMonoidHom
          (unramifiedCharacter_isOpen_ker _ ψ))).representation.Equiv
        (((inductionFunctor p l r hp hr hl hmul).obj
          (τ.twist
            (unramifiedCharactersHomeomorph (leviPointsEquiv p l hp hl)
              (fun c : rationalCharacters M => (rationalNormCharacters M c).toMul) ψ).val.toMonoidHom
            (unramifiedCharacter_isOpen_ker _ _))).representation) := by
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro ψ
  let e := leviPointsEquiv p l hp hl
  let χ := unramifiedCharactersHomeomorph e
    (fun c : rationalCharacters M => (rationalNormCharacters M c).toMul) ψ
  apply normalizedInductionEquivOfEquiv _ _
  refine Representation.Equiv.mk (LinearEquiv.refl ℂ τ) ?_
  intro m
  ext v
  change (ψ.val (e.symm m) : ℂ) • τ.representation (e (e.symm m)) v =
    (χ.val m : ℂ) • τ.representation m v
  rw [e.apply_symm_apply]
  rfl

variable (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : V ⟶ Q) (hq : IsParabolicSubgroup q)
  (hlQ : IsRationalLeviSubgroup lQ) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ L)

set_option maxHeartbeats 1200000 in
/-- The same comparison after actual normalized Jacquet restriction, read on
the unchanged component point group and its literal point-image map. -/
def literalJacquetInductionComponentTwistEquiv
    (τ : SmoothRep.{0, u, v} ℂ (pointImage (l ≫ p))) :
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ ψ : unramifiedCharacters
        (fun c : rationalCharacters M => (rationalNormCharacters M c).toMul),
      Representation.Equiv
        ((((leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj
          ((SmoothRep.pullback (leviPointsEquiv p l hp hl) τ).twist ψ.val.toMonoidHom
            (unramifiedCharacter_isOpen_ker _ ψ))).ρ).comp (rationalPoints.map a))
        ((((jacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj
          ((inductionFunctor p l r hp hr hl hmul).obj
            (τ.twist
              (unramifiedCharactersHomeomorph (leviPointsEquiv p l hp hl)
                (fun c : rationalCharacters M => (rationalNormCharacters M c).toMul) ψ).val.toMonoidHom
              (unramifiedCharacter_isOpen_ker _ _)))).representation).comp
                (splitComponentPointsMap (lQ ≫ q) a)) := by
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro ψ
  let iE := SmoothRep.mkIso (literalLeviUnramifiedInductionEquiv p l r hp hl hr hmul τ ψ)
  let E := SmoothRep.equivOfIso ((jacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).mapIso iE)
  let V₀ := (leviInductionFunctor p l r hp hr hl hmul).obj
    ((SmoothRep.pullback (leviPointsEquiv p l hp hl) τ).twist ψ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker _ ψ))
  refine Representation.Equiv.mk E.toLinearEquiv ?_
  intro t
  have ht := DFunLike.congr_fun (leviPointsEquiv_comp_map q lQ hq hlQ a) t
  change (leviPointsEquiv q lQ hq hlQ) (rationalPoints.map a t) =
    splitComponentPointsMap (lQ ≫ q) a t at ht
  change E.toIntertwiningMap.toLinearMap.comp
      (((jacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj V₀).representation
        ((leviPointsEquiv q lQ hq hlQ) (rationalPoints.map a t))) = _
  rw [ht]
  exact E.isIntertwining' (splitComponentPointsMap (lQ ≫ q) a t)

/-- A fixed finite set contains all exponent norms for the actual full literal
normalized induction/Jacquet family over every unitary unramified source twist,
with the norm family transported through its canonical point homeomorphism. -/
theorem exists_finite_literalUnitaryInducedJacquet_exponentNorms
    (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
    (τ : SmoothRep.{0, u, v} ℂ (pointImage (l ≫ p)))
    (hτirr : τ.IsIrreducible) (hτadm : τ.IsAdmissible) (t : rationalPoints A.toGrp) :
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∃ R : Set ℝ≥0, R.Finite ∧
      ∀ ψ : unramifiedCharacters (fun c : rationalCharacters M =>
          ((rationalNormCharacters M c).toMul).comp
            (leviPointsEquiv p l hp hl).symm.toMulEquiv.toMonoidHom),
        (∀ m, ‖(ψ.val m : ℂ)‖ = 1) → ∀ χ : rationalPoints A.toGrp →* ℂˣ,
          IsGeneralizedEigencharacter
            ((((jacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj
              ((inductionFunctor p l r hp hr hl hmul).obj
                (τ.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ)))).representation).comp
                  (splitComponentPointsMap (lQ ≫ q) a)) χ → ‖(χ t : ℂ)‖₊ ∈ R := by
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let e := leviPointsEquiv p l hp hl
  let σ := SmoothRep.pullback e τ
  have hσadm : σ.IsAdmissible := isAdmissible_comp_continuousMulEquiv τ.representation e hτadm
  have hσirr : σ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff τ.representation e).mpr hτirr
  have hσfinite := SmoothRep.hasFiniteLength_of_isIrreducible hσirr
  let R := unitaryInducedJacquetExponentNormSet p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
    (a := a) σ t
  have hR : R.Finite := unitaryInducedJacquetExponentNormSet_finite
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hG ha σ hσadm hσfinite t
  refine ⟨R, hR, ?_⟩
  intro ψ hψ χ hχ
  let ψ₀ := (unramifiedCharactersHomeomorph e
    (fun c : rationalCharacters M => (rationalNormCharacters M c).toMul)).symm ψ
  have hψ₀ : ∀ m, ‖(ψ₀.val m : ℂ)‖ = 1 := fun m => hψ (e m)
  have hψeq : unramifiedCharactersHomeomorph e
      (fun c : rationalCharacters M => (rationalNormCharacters M c).toMul) ψ₀ = ψ :=
    (unramifiedCharactersHomeomorph e _).apply_symm_apply ψ
  dsimp only [e] at hψeq
  have he := literalJacquetInductionComponentTwistEquiv
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ a τ ψ₀
  have hχ₀ : IsGeneralizedEigencharacter
      (((leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj
        (σ.twist ψ₀.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ₀))).ρ.comp
          (rationalPoints.map a)) χ := by
    apply (isGeneralizedEigencharacter_iff_of_equiv he χ).mpr
    rw [hψeq]
    exact hχ
  exact ⟨ψ₀, hψ₀, χ, hχ₀, rfl⟩

end Langlands.Aubert.General.RepresentedParabolic
