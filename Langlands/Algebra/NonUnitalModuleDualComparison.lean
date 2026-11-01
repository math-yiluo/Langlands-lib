import Langlands.Algebra.NonUnitalModuleDualComparisonFull

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualComparison

open CategoryTheory MulOpposite NonUnitalModuleDual

universe uA uM uN

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M]

section Actions

variable (hA : IsIdempotented A) (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M)

/-- Restriction to the actual raw and transported nondegenerate subtypes. -/
def dualComparison :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    Dual hA.op.op hM ≃+ Dual hA (fromDoubleOpposite_isNondegenerate hM) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let forward : Dual hA.op.op hM →
      Dual hA (fromDoubleOpposite_isNondegenerate hM) := fun Φ =>
    ⟨fullComparison hA hM Φ.val, by
      obtain ⟨e, he⟩ := Φ.property
      let eT : Idempotent Aᵐᵒᵖ := ⟨e.val.unop.unop, by
        have hh := congrArg (fun a : Aᵐᵒᵖᵐᵒᵖᵐᵒᵖ => a.unop.unop) e.property.eq
        simpa only [IsIdempotentElem, unop_mul] using hh⟩
      refine ⟨eT, ?_⟩
      apply fullDual_ext hA (fromDoubleOpposite_isNondegenerate hM)
      intro m
      exact congrArg (fun ψ : FullDual hA.op.op hM => ψ m) he⟩
  let backward : Dual hA (fromDoubleOpposite_isNondegenerate hM) →
      Dual hA.op.op hM := fun Φ =>
    ⟨(fullComparison hA hM).symm Φ.val, by
      obtain ⟨e, he⟩ := Φ.property
      let eT : Idempotent Aᵐᵒᵖᵐᵒᵖᵐᵒᵖ := ⟨op (op e.val), by
        change op (op (e.val * e.val)) = op (op e.val)
        exact congrArg (fun a : Aᵐᵒᵖ => op (op a)) e.property.eq⟩
      refine ⟨eT, ?_⟩
      apply fullDual_ext hA.op.op hM
      intro m
      exact congrArg
        (fun ψ : FullDual hA (fromDoubleOpposite_isNondegenerate hM) => ψ m) he⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv Φ := dual_ext hA.op.op hM (fun _ => rfl)
      right_inv Φ := dual_ext hA (fromDoubleOpposite_isNondegenerate hM)
        (fun _ => rfl)
      map_add' Φ Ψ := dual_ext hA (fromDoubleOpposite_isNondegenerate hM)
        (fun _ => rfl) }

theorem dualComparison_val (Φ : Dual hA.op.op hM) :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    (dualComparison hA hM Φ).val = fullComparison hA hM Φ.val := rfl

theorem dualComparison_val_coe (Φ : Dual hA.op.op hM) :
    ⇑(dualComparison hA hM Φ).val = ⇑Φ.val := rfl

theorem dualComparison_symm_val :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    ∀ Φ : Dual hA (fromDoubleOpposite_isNondegenerate hM),
      ((dualComparison hA hM).symm Φ).val = (fullComparison hA hM).symm Φ.val := by
  intro Φ
  rfl

theorem dualComparison_symm_val_coe :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    ∀ Φ : Dual hA (fromDoubleOpposite_isNondegenerate hM),
      ⇑((dualComparison hA hM).symm Φ).val = ⇑Φ.val := by
  intro Φ
  rfl

/-- The entire subtype comparison is an original right intertwiner. -/
def dualComparisonHom :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fullAction hA.op.op hM
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    NonUnitalModuleHom Aᵐᵒᵖ (Dual hA.op.op hM)
      (Dual hA (fromDoubleOpposite_isNondegenerate hM)) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := fullAction hA.op.op hM
  let _ := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
  exact
    { toAddMonoidHom := (dualComparison hA hM).toAddMonoidHom
      map_smul' a Φ := by
        apply dual_ext hA (fromDoubleOpposite_isNondegenerate hM)
        intro m
        rfl }

/-- The inverse also intertwines the complete specified right actions. -/
def dualComparisonInvHom :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fullAction hA.op.op hM
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    NonUnitalModuleHom Aᵐᵒᵖ (Dual hA (fromDoubleOpposite_isNondegenerate hM))
      (Dual hA.op.op hM) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := fullAction hA.op.op hM
  let _ := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
  exact
    { toAddMonoidHom := (dualComparison hA hM).symm.toAddMonoidHom
      map_smul' a Φ := by
        apply dual_ext hA.op.op hM
        intro m
        rfl }

theorem dualComparison_inverse_left :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fullAction hA.op.op hM
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    (dualComparisonInvHom hA hM).comp (dualComparisonHom hA hM) =
      NonUnitalModuleHom.id Aᵐᵒᵖ (Dual hA.op.op hM) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := fullAction hA.op.op hM
  let _ := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
  apply NonUnitalModuleHom.ext
  intro Φ
  exact (dualComparison hA hM).left_inv Φ

theorem dualComparison_inverse_right :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fullAction hA.op.op hM
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    (dualComparisonHom hA hM).comp (dualComparisonInvHom hA hM) =
      NonUnitalModuleHom.id Aᵐᵒᵖ (Dual hA (fromDoubleOpposite_isNondegenerate hM)) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := fullAction hA.op.op hM
  let _ := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
  apply NonUnitalModuleHom.ext
  intro Φ
  exact (dualComparison hA hM).right_inv Φ

theorem dualComparisonHom_toAddMonoidHom :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    (dualComparisonHom hA hM).toAddMonoidHom =
      (dualComparison hA hM).toAddMonoidHom := rfl

theorem dualComparisonInvHom_toAddMonoidHom :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    (dualComparisonInvHom hA hM).toAddMonoidHom =
      (dualComparison hA hM).symm.toAddMonoidHom := rfl

/-- The same comparison for the precise inherited pointwise complex modules. -/
def dualComparisonLinear :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := dualModule hA.op.op hM
    letI := dualModule hA (fromDoubleOpposite_isNondegenerate hM)
    Dual hA.op.op hM ≃ₗ[ℂ] Dual hA (fromDoubleOpposite_isNondegenerate hM) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := dualModule hA.op.op hM
  let _ := dualModule hA (fromDoubleOpposite_isNondegenerate hM)
  exact
    { dualComparison hA hM with
      map_smul' c Φ := dual_ext hA (fromDoubleOpposite_isNondegenerate hM)
        (fun _ => rfl) }

/-- Canonical scalars for the comparison's transported original source action. -/
abbrev comparisonSourceModule : Module ℂ (Dual hA.op.op hM) :=
  letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
  NondegenerateScalars.complexModule hA.op
    (fromDoubleOpposite_isNondegenerate (isNondegenerate hA.op.op hM))

/-- Canonical scalars for the comparison's target original action. -/
abbrev comparisonTargetModule :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    Module ℂ (Dual hA (fromDoubleOpposite_isNondegenerate hM)) :=
  letI := fromDoubleOppositeAction (A := A) (M := M)
  NondegenerateScalars.complexModule hA.op
    (isNondegenerate hA (fromDoubleOpposite_isNondegenerate hM))

theorem comparisonSourceModule_eq_dualModule :
    comparisonSourceModule hA hM = dualModule hA.op.op hM :=
  (transportedCanonicalModule_eq_raw hA.op (isNondegenerate hA.op.op hM)).trans
    (canonicalModule_eq_dualModule hA.op.op hM)

theorem comparisonTargetModule_eq_dualModule :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    comparisonTargetModule hA hM =
      dualModule hA (fromDoubleOpposite_isNondegenerate hM) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  exact canonicalModule_eq_dualModule hA (fromDoubleOpposite_isNondegenerate hM)

/-- The identical equivalence for the complete recovered source and target modules. -/
def dualComparisonCanonicalLinear :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := comparisonSourceModule hA hM
    letI := comparisonTargetModule hA hM
    Dual hA.op.op hM ≃ₗ[ℂ] Dual hA (fromDoubleOpposite_isNondegenerate hM) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := comparisonSourceModule hA hM
  let _ := comparisonTargetModule hA hM
  refine { dualComparison hA hM with map_smul' := ?_ }
  intro c Φ
  change dualComparison hA hM
      (@SMul.smul ℂ _ (comparisonSourceModule hA hM).toSMul c Φ) =
    @SMul.smul ℂ _ (comparisonTargetModule hA hM).toSMul c (dualComparison hA hM Φ)
  rw [comparisonSourceModule_eq_dualModule, comparisonTargetModule_eq_dualModule]
  exact (dualComparisonLinear hA hM).map_smul c Φ

theorem dualComparisonLinear_toAddMonoidHom :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    letI := dualModule hA.op.op hM
    letI := dualModule hA (fromDoubleOpposite_isNondegenerate hM)
    (dualComparisonLinear hA hM).toAddMonoidHom =
      (dualComparisonHom hA hM).toAddMonoidHom := rfl

theorem dualComparisonCanonicalLinear_toAddMonoidHom :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    letI := comparisonSourceModule hA hM
    letI := comparisonTargetModule hA hM
    (dualComparisonCanonicalLinear hA hM).toAddMonoidHom =
      (dualComparisonHom hA hM).toAddMonoidHom := rfl

theorem dualComparisonCanonicalLinear_eq_complexToLinearMap :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    letI := comparisonSourceModule hA hM
    letI := comparisonTargetModule hA hM
    (dualComparisonCanonicalLinear hA hM).toLinearMap =
      NondegenerateScalars.complexToLinearMap hA.op
        (fromDoubleOpposite_isNondegenerate (isNondegenerate hA.op.op hM))
        (isNondegenerate hA (fromDoubleOpposite_isNondegenerate hM))
        (dualComparisonHom hA hM) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := comparisonSourceModule hA hM
  let _ := comparisonTargetModule hA hM
  exact LinearMap.ext (fun _ => rfl)

end Actions

variable {N : Type uN} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ N]

/-- Cross-universe naturality of the entire original-action comparison. -/
theorem dualComparison_cross_naturality (hA : IsIdempotented A)
    (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) (hN : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ N)
    (f : NonUnitalModuleHom Aᵐᵒᵖᵐᵒᵖ M N) :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := A) (M := N)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hN)
    (dualComparisonHom hA hM).comp
        (fromDoubleOppositeMap (pullback hA.op.op hM hN f)) =
      (pullback hA (fromDoubleOpposite_isNondegenerate hM)
        (fromDoubleOpposite_isNondegenerate hN) (fromDoubleOppositeMap f)).comp
          (dualComparisonHom hA hN) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := fromDoubleOppositeAction (A := A) (M := N)
  let _ := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
  let _ := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hN)
  apply NonUnitalModuleHom.ext
  intro Φ
  exact dual_ext hA (fromDoubleOpposite_isNondegenerate hM) (fun _ => rfl)

/-- The same naturality equation as entire complex-linear maps for recovered scalars. -/
theorem dualComparison_linear_naturality (hA : IsIdempotented A)
    (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) (hN : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ N)
    (f : NonUnitalModuleHom Aᵐᵒᵖᵐᵒᵖ M N) :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := A) (M := N)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hN)
    letI := comparisonSourceModule hA hM
    letI := comparisonSourceModule hA hN
    letI := comparisonTargetModule hA hM
    letI := comparisonTargetModule hA hN
    (dualComparisonCanonicalLinear hA hM).toLinearMap.comp
        (NondegenerateScalars.complexToLinearMap hA.op
          (fromDoubleOpposite_isNondegenerate (isNondegenerate hA.op.op hN))
          (fromDoubleOpposite_isNondegenerate (isNondegenerate hA.op.op hM))
          (fromDoubleOppositeMap (pullback hA.op.op hM hN f))) =
      (NondegenerateScalars.complexToLinearMap hA.op
        (isNondegenerate hA (fromDoubleOpposite_isNondegenerate hN))
        (isNondegenerate hA (fromDoubleOpposite_isNondegenerate hM))
        (pullback hA (fromDoubleOpposite_isNondegenerate hM)
          (fromDoubleOpposite_isNondegenerate hN) (fromDoubleOppositeMap f))).comp
            (dualComparisonCanonicalLinear hA hN).toLinearMap := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := fromDoubleOppositeAction (A := A) (M := N)
  let _ := comparisonSourceModule hA hM
  let _ := comparisonSourceModule hA hN
  let _ := comparisonTargetModule hA hM
  let _ := comparisonTargetModule hA hN
  apply LinearMap.ext
  intro Φ
  exact dual_ext hA (fromDoubleOpposite_isNondegenerate hM) (fun _ => rfl)


end Langlands.Algebra.NonUnitalModuleDualComparison
