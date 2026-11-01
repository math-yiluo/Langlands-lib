import Langlands.Algebra.NonUnitalModuleDualFunctor

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualComparison

open CategoryTheory MulOpposite NonUnitalModuleDual

universe uA uM uN

section ScalarTransport

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M]

/-- Canonical scalars recovered for the specified original double-opposite action. -/
abbrev rawCanonicalModule (hA : IsIdempotented A)
    (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) : Module ℂ M :=
  NondegenerateScalars.complexModule hA.op.op hM

/-- Canonical scalars recovered after transporting the original action to `A`. -/
abbrev transportedCanonicalModule (hA : IsIdempotented A)
    (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) : Module ℂ M :=
  letI := fromDoubleOppositeAction (A := A) (M := M)
  NondegenerateScalars.complexModule hA (fromDoubleOpposite_isNondegenerate hM)

/-- Transport preserves the complete recovered scalar structure. -/
theorem transportedCanonicalModule_eq_raw (hA : IsIdempotented A)
    (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    NondegenerateScalars.complexModule hA (fromDoubleOpposite_isNondegenerate hM) =
      NondegenerateScalars.complexModule hA.op.op hM := by
  let _ := NondegenerateScalars.complexModule hA.op.op hM
  let _ := NondegenerateScalars.isScalarTower ℂ hA.op.op hM
  let _ := fromDoubleOpposite_isScalarTower (A := A) (M := M)
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  exact NondegenerateScalars.module_eq_of_compatible ℂ hA
    (fromDoubleOpposite_isNondegenerate hM)


theorem canonicalModule_names (hA : IsIdempotented A)
    (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) :
    transportedCanonicalModule hA hM = rawCanonicalModule hA hM :=
  transportedCanonicalModule_eq_raw hA hM

/-- The comparison preserves the entire functional, rather than just its values. -/
def fullComparison (hA : IsIdempotented A)
    (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    FullDual hA.op.op hM ≃ₗ[ℂ]
      FullDual hA (fromDoubleOpposite_isNondegenerate hM) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  have hsc := transportedCanonicalModule_eq_raw hA hM
  let forward : FullDual hA.op.op hM →
      FullDual hA (fromDoubleOpposite_isNondegenerate hM) := fun φ => by
    let _ := NondegenerateScalars.complexModule hA
      (fromDoubleOpposite_isNondegenerate hM)
    exact
    { toFun := φ
      map_add' m n := by
        let _ := NondegenerateScalars.complexModule hA.op.op hM
        exact φ.map_add m n
      map_smul' c m := by
        change φ
          (@SMul.smul ℂ M
            (NondegenerateScalars.complexModule hA
              (fromDoubleOpposite_isNondegenerate hM)).toSMul c m) = c • φ m
        rw [hsc]
        let _ := NondegenerateScalars.complexModule hA.op.op hM
        exact φ.map_smul c m }
  let backward : FullDual hA (fromDoubleOpposite_isNondegenerate hM) →
      FullDual hA.op.op hM := fun φ => by
    let _ := NondegenerateScalars.complexModule hA.op.op hM
    exact
    { toFun := φ
      map_add' m n := by
        let _ := NondegenerateScalars.complexModule hA
          (fromDoubleOpposite_isNondegenerate hM)
        exact φ.map_add m n
      map_smul' c m := by
        change φ
          (@SMul.smul ℂ M
            (NondegenerateScalars.complexModule hA.op.op hM).toSMul c m) = c • φ m
        rw [← hsc]
        let _ := NondegenerateScalars.complexModule hA
          (fromDoubleOpposite_isNondegenerate hM)
        exact φ.map_smul c m }
  exact
    { toFun := forward
      invFun := backward
      left_inv φ := fullDual_ext hA.op.op hM (fun _ => rfl)
      right_inv φ := fullDual_ext hA (fromDoubleOpposite_isNondegenerate hM)
        (fun _ => rfl)
      map_add' φ ψ := fullDual_ext hA (fromDoubleOpposite_isNondegenerate hM)
        (fun _ => rfl)
      map_smul' c φ := fullDual_ext hA (fromDoubleOpposite_isNondegenerate hM)
        (fun _ => rfl) }

theorem fullComparison_coe (hA : IsIdempotented A)
    (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) (φ : FullDual hA.op.op hM) :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    ⇑(fullComparison hA hM φ) = ⇑φ := rfl

theorem fullComparison_symm_coe (hA : IsIdempotented A)
    (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    ∀ φ : FullDual hA (fromDoubleOpposite_isNondegenerate hM),
      ⇑((fullComparison hA hM).symm φ) = ⇑φ := by
  intro φ
  rfl

section Actions

variable (hA : IsIdempotented A) (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M)

/-- The complete functional comparison intertwines the specified original actions. -/
def fullComparisonHom :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fullAction hA.op.op hM
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := FullDual hA.op.op hM)
    letI := fullAction hA (fromDoubleOpposite_isNondegenerate hM)
    NonUnitalModuleHom Aᵐᵒᵖ (FullDual hA.op.op hM)
      (FullDual hA (fromDoubleOpposite_isNondegenerate hM)) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := fullAction hA.op.op hM
  let _ := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := FullDual hA.op.op hM)
  let _ := fullAction hA (fromDoubleOpposite_isNondegenerate hM)
  exact
    { toAddMonoidHom := (fullComparison hA hM).toAddMonoidHom
      map_smul' a φ := by
        apply fullDual_ext hA (fromDoubleOpposite_isNondegenerate hM)
        intro m
        rfl }

theorem fullComparisonHom_toAddMonoidHom :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fullAction hA.op.op hM
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := FullDual hA.op.op hM)
    letI := fullAction hA (fromDoubleOpposite_isNondegenerate hM)
    (fullComparisonHom hA hM).toAddMonoidHom =
      (fullComparison hA hM).toAddMonoidHom := rfl

/-- The inverse full-functional comparison also preserves the original actions. -/
def fullComparisonInvHom :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fullAction hA.op.op hM
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := FullDual hA.op.op hM)
    letI := fullAction hA (fromDoubleOpposite_isNondegenerate hM)
    NonUnitalModuleHom Aᵐᵒᵖ (FullDual hA (fromDoubleOpposite_isNondegenerate hM))
      (FullDual hA.op.op hM) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := fullAction hA.op.op hM
  let _ := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := FullDual hA.op.op hM)
  let _ := fullAction hA (fromDoubleOpposite_isNondegenerate hM)
  exact
    { toAddMonoidHom := (fullComparison hA hM).symm.toAddMonoidHom
      map_smul' a φ := fullDual_ext hA.op.op hM (fun _ => rfl) }

theorem fullComparisonInvHom_toAddMonoidHom :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fullAction hA.op.op hM
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := FullDual hA.op.op hM)
    letI := fullAction hA (fromDoubleOpposite_isNondegenerate hM)
    (fullComparisonInvHom hA hM).toAddMonoidHom =
      (fullComparison hA hM).symm.toAddMonoidHom := rfl

theorem fullComparison_inverse_left :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fullAction hA.op.op hM
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := FullDual hA.op.op hM)
    letI := fullAction hA (fromDoubleOpposite_isNondegenerate hM)
    (fullComparisonInvHom hA hM).comp (fullComparisonHom hA hM) =
      NonUnitalModuleHom.id Aᵐᵒᵖ (FullDual hA.op.op hM) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := fullAction hA.op.op hM
  let _ := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := FullDual hA.op.op hM)
  let _ := fullAction hA (fromDoubleOpposite_isNondegenerate hM)
  apply NonUnitalModuleHom.ext
  exact (fullComparison hA hM).left_inv

theorem fullComparison_inverse_right :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fullAction hA.op.op hM
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := FullDual hA.op.op hM)
    letI := fullAction hA (fromDoubleOpposite_isNondegenerate hM)
    (fullComparisonHom hA hM).comp (fullComparisonInvHom hA hM) =
      NonUnitalModuleHom.id Aᵐᵒᵖ
        (FullDual hA (fromDoubleOpposite_isNondegenerate hM)) := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := fullAction hA.op.op hM
  let _ := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := FullDual hA.op.op hM)
  let _ := fullAction hA (fromDoubleOpposite_isNondegenerate hM)
  apply NonUnitalModuleHom.ext
  exact (fullComparison hA hM).right_inv

end Actions
end ScalarTransport

/-! Complete unapplied interfaces retain independent algebra and carrier universes. -/
example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    FullDual hA.op.op hM ≃ₗ[ℂ]
      FullDual hA (fromDoubleOpposite_isNondegenerate hM) := @fullComparison.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fullAction hA.op.op hM
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := FullDual hA.op.op hM)
    letI := fullAction hA (fromDoubleOpposite_isNondegenerate hM)
    NonUnitalModuleHom Aᵐᵒᵖ (FullDual hA.op.op hM)
      (FullDual hA (fromDoubleOpposite_isNondegenerate hM)) := @fullComparisonHom.{uA,uM}

end Langlands.Algebra.NonUnitalModuleDualComparison
