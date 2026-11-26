import Langlands.Global.AdelicRelativeCuspidalConstantTerm
import Langlands.Global.AdelicPositiveTorusSplitComponentProof
import Langlands.Global.AdelicNestedSplitComponents
import Langlands.Global.AdelicLocalFinitenessGroupData
import Langlands.Global.AdelicGroupParabolicSpectrumReduction
import Langlands.Global.AdelicEisensteinPositiveParametersProof
import Langlands.Global.AdelicSiegelMeasureReduction
import Langlands.GroupScheme.Dynamic.LieProof

/-! # Testing unitarity on a split component enlarged by one simple root -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints PositiveRealTorus

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν

omit [NumberField F] in
/-- Each selected Levi root is trivial on the torus map of its split component. -/
theorem selectedRoot_restrict_splitComponent_eq_zero (J : Idx)
    {β : characterLattice fam.T} (hβ : β ∈ J.val) : fam.f J ≫ β = 0 := by
  have hC := fam.isCompatible J
  have hClosed : IsClosedSubgroup (fam.l J ≫ fam.p J) :=
    hC.levi.isClosedSubgroup.comp hC.parabolic.isClosedSubgroup
  have hRep : (standardLevi fam.i fam.ν J.val).IsRepresentedBy (fam.l J ≫ fam.p J) := by
    let : Mono (fam.l J ≫ fam.p J).hom.hom.left := hClosed.mono
    exact ⟨Over.mono_of_mono_left _, hC.levi_eq⟩
  exact selectedRoot_restrict_eq_zero_standardLevi dynamicLie fam.i fam.ν J.val J.property
    hClosed hRep (fam.a J) hC.splitComponent.1 (fam.f J) hC.factor_comp hβ

/-- The root logarithm of a split point can be read at any torus point with the same
ambient adelic image. -/
theorem characterLog_splitComponent_restrict_of_same_image (J : Idx)
    (x : AdelicGroupPoints F (fam.A J).toGrp) (t : AdelicGroupPoints F fam.T.toGrp)
    (h : map F (fam.A J).toGrp G (fam.a J ≫ fam.l J ≫ fam.p J) x =
      map F fam.T.toGrp G fam.i t) (β : characterLattice fam.T) :
    characterLog F (fam.A J).toGrp x (fam.f J ≫ β) = characterLog F fam.T.toGrp t β := by
  have : IsAffineHom fam.T.X.hom := fam.maximalSplit.isSplitSubtorus.1.isAffineHom
  have : IsAffine fam.T.X.left := isAffine_of_isAffineHom fam.T.X.hom
  rw [← (fam.isCompatible J).factor_comp, map_comp_apply_of_hom] at h
  have he := (isClosedEmbedding_map_of_isClosedSubgroup F fam.i fam.maximalSplit.isSplitSubtorus.2).injective h
  rw [← he, characterLog_map]
  rfl

/-- When one simple root is removed from a Levi index, a parameter on the enlarged
positive split component is unitary if it is unitary on the old component and on
one point with nonzero logarithm in the direction of that root. -/
theorem parameterRealPart_eq_zero_of_unitary_on_relativeAxis (J : Idx)
    {α : characterLattice fam.T}
    (lam : ComplexCharacterParameter F (fam.P (fam.removeSimpleRoot J α)))
    (x : intrinsicSubgroup F (fam.A (fam.removeSimpleRoot J α)))
    (hAxis : characterLog F (fam.A (fam.removeSimpleRoot J α)).toGrp x.val
      (fam.f (fam.removeSimpleRoot J α) ≫ α) ≠ 0)
    (hUnit : ∀ (a : fam.positiveSplitComponent J)
      (b : fam.positiveSplitComponent (fam.removeSimpleRoot J α)),
      map F (fam.P (fam.removeSimpleRoot J α)) G (fam.p (fam.removeSimpleRoot J α)) b.val =
        map F (fam.P J) G (fam.p J) a.val →
      ‖parameterPower F (fam.P (fam.removeSimpleRoot J α)) lam b.val‖ = 1)
    (hAxisUnit : ‖parameterPower F (fam.P (fam.removeSimpleRoot J α)) lam
      (map F (fam.A (fam.removeSimpleRoot J α)).toGrp (fam.P (fam.removeSimpleRoot J α))
        (fam.a _ ≫ fam.l _) x.val)‖ = 1) :
    parameterRealPart F (fam.P (fam.removeSimpleRoot J α)) lam = 0 := by
  let Q := fam.removeSimpleRoot J α
  let P := fam.P Q
  let A₀ := fam.A Q
  let p := fam.p Q
  let e := fam.a Q ≫ fam.l Q
  have hAQ : IsSplitTorus A₀.toGrp := (fam.isCompatible Q).splitComponent.1.1.1
  let r : ParabolicRootPresentation (fam.p Q) (fam.l Q) (fam.a Q) :=
    ⟨⟨fam.T, fam.i, fam.ν, Q.val, fam.f Q⟩, fam.isCompatible Q⟩
  have := (r.rationalCharacters_free_finite fam.connectedReductive).1
  let L : RealCharacterDual F A₀.toGrp →ₗ[ℝ] ℝ :=
    (realParameterPairing F P (parameterRealPart F P lam)).comp (realCharacterDualMap F A₀.toGrp P e)
  have hEval (z : AdelicGroupPoints F A₀.toGrp) :
      ‖parameterPower F P lam (map F A₀.toGrp P e z)‖ =
        Real.exp (L (characterLog F A₀.toGrp z)) := by
    rw [parameterPower, Complex.norm_exp, complexParameterPairing_re, characterLog_map]
    rfl
  let v := characterLog F A₀.toGrp x.val
  have hLx : L v = 0 := by
    have hx := (hEval x.val).symm.trans hAxisUnit
    rw [Real.exp_eq_one_iff] at hx
    exact hx
  apply realParameterPairing_left_eq_zero
  intro H
  obtain ⟨u, hu⟩ := (eisensteinPositiveParameters F G P (fam.M Q) A₀ p (fam.l Q)
    (fam.a Q) r).1 H
  change characterLog F P u.val = H at hu
  obtain ⟨z, hz, hez⟩ := u.property
  change map F A₀.toGrp P e z = u.val at hez
  let l := characterLog F A₀.toGrp z
  let c := l (fam.f Q ≫ α) / v (fam.f Q ≫ α)
  obtain ⟨z', hz', hLog⟩ := exists_characterLog_eq hAQ (l - c • v)
  let t := map F A₀.toGrp fam.T.toGrp (CommGroupScheme.groupHom (fam.f Q)) z'
  have ht : t ∈ intrinsicSubgroup F fam.T :=
    map_intrinsicSubgroup_le F A₀ fam.T (fam.f Q) ⟨z', hz', rfl⟩
  have hZer (β : characterLattice fam.T) (hβ : β ∈ J.val) :
      Lie.characterValue β t = 1 := by
    apply characterValue_eq_one_of_characterLog_eq_zero ht
    have heval : characterLog F fam.T.toGrp t β = characterLog F A₀.toGrp z' (fam.f Q ≫ β) := by
      rw [characterLog_map]
      rfl
    rw [heval, hLog]
    by_cases hβα : β = α
    · subst β
      change l (fam.f Q ≫ α) - c * v (fam.f Q ≫ α) = 0
      rw [div_mul_cancel₀ _ hAxis]
      exact sub_self _
    · have hβQ : β ∈ Q.val := ⟨hβ, J.property hβ, hβα⟩
      exact (congrArg (fun χ : characterLattice A₀ => (l - c • v) χ)
        (fam.selectedRoot_restrict_splitComponent_eq_zero Q hβQ)).trans
        (map_zero (show rationalCharacters A₀.toGrp →+ ℝ from l - c • v))
  obtain ⟨a, ha, hAmbient⟩ := positiveTorusSplitComponent F G fam J t ht hZer
  let b : fam.positiveSplitComponent Q := ⟨map F A₀.toGrp P e z', ⟨z', hz', rfl⟩⟩
  have hb : map F P G p b.val = map F (fam.P J) G (fam.p J) a := by
    change map F P G p (map F A₀.toGrp P e z') = _
    rw [← map_comp_apply_of_hom, hAmbient]
    dsimp only [e, p, t]
    rw [Category.assoc, ← (fam.isCompatible Q).factor_comp, map_comp_apply_of_hom]
  have hZ := hUnit ⟨a, ha⟩ b hb
  change ‖parameterPower F P lam (map F A₀.toGrp P e z')‖ = 1 at hZ
  rw [hEval, Real.exp_eq_one_iff, hLog, map_sub, map_smul, hLx, smul_zero, sub_zero] at hZ
  rw [← hu, ← hez, characterLog_map]
  exact hZ

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints PositiveRealTorus

/-- For an index obtained by removing one simple root, a nonunitary parameter whose
restriction to the larger parabolic is unitary has strict character norm below one
at any relative axis point where its character norm is at most one. -/
def AdelicRelativeExponentAxisStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    ∀ (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν) (α : J.val),
      let Q := fam.removeSimpleRoot J α.val
      ∀ (lam : ComplexCharacterParameter F (fam.P Q)) (x : intrinsicSubgroup F (fam.A Q)),
        characterLog F (fam.A Q).toGrp x.val (fam.f Q ≫ α.val) ≠ 0 →
        (∀ (a : fam.positiveSplitComponent J) (b : fam.positiveSplitComponent Q),
          map F (fam.P Q) G (fam.p Q) b.val = map F (fam.P J) G (fam.p J) a.val →
            ‖parameterPower F (fam.P Q) lam b.val‖ = 1) →
        parameterRealPart F (fam.P Q) lam ≠ 0 →
        ‖parameterPower F (fam.P Q) lam
          (map F (fam.A Q).toGrp (fam.P Q) (fam.a Q ≫ fam.l Q) x.val)‖ ≤ 1 →
        ‖parameterPower F (fam.P Q) lam
          (map F (fam.A Q).toGrp (fam.P Q) (fam.a Q ≫ fam.l Q) x.val)‖ < 1

theorem adelicRelativeExponentAxis : AdelicRelativeExponentAxisStatement := by
  intro F _ _ G _ _ _ fam J α
  dsimp only
  intro lam x hAxis hUnit hNon hle
  exact lt_of_le_of_ne hle (fun hEq => hNon
    (fam.parameterRealPart_eq_zero_of_unitary_on_relativeAxis J lam x hAxis hUnit hEq))

end Langlands.Global
