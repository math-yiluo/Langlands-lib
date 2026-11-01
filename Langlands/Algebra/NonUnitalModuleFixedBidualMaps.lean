import Langlands.Algebra.NonUnitalModuleBidualEvaluation
import Langlands.Algebra.NonUnitalModuleDualFixedPartMaps

/-!
# Fixed spaces of the actual bidual and the ordinary fixed-space bidual

Internal comparison maps for Renard (9 July 2026), I.5.1, printed p.26 / PDF32.
The inverse and evaluation-square assertions are separate proof obligations.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleFixedBidualMaps

open MulOpposite NonUnitalModuleDual NonUnitalModuleDualFixedPartMaps
open NonUnitalModuleCorner (FixedPart)

universe uA uM

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

local instance : NonUnitalModule Aᵐᵒᵖ (Dual hA hM) := dualAction hA hM
local instance : NonUnitalModule A (Bidual hA hM) := bidualAction hA hM

/-- Double-opposite transport preserves the exact pointwise coefficient module. -/
theorem canonicalBidualModule_eq :
    NondegenerateScalars.complexModule hA (bidual_isNondegenerate hA hM) =
      dualModule hA.op (isNondegenerate hA hM) := by
  let _ := dualModule hA.op (isNondegenerate hA hM)
  let _ := dual_isScalarTower hA.op (isNondegenerate hA hM)
  let _ := fromDoubleOpposite_isScalarTower
    (A := A) (M := Bidual hA hM)
  exact NondegenerateScalars.module_eq_of_compatible ℂ hA
    (bidual_isNondegenerate hA hM)

theorem canonicalBidual_smul_val (c : ℂ) (Φ : Bidual hA hM) :
    letI := NondegenerateScalars.complexModule hA (bidual_isNondegenerate hA hM)
    (c • Φ).val = c • Φ.val := by
  rw [canonicalBidualModule_eq hA hM]
  rfl

/-- The source is the published fixed subgroup for the unchanged original A-action. -/
abbrev FixedBidual (e : Idempotent A) := FixedPart e (Bidual hA hM)

/-- The ordinary algebraic bidual of the actual fixed subgroup with canonical scalars. -/
abbrev OrdinaryBidual (e : Idempotent A) :=
  letI := NonUnitalModuleCorner.complexModule hA hM e
  Module.Dual ℂ (Module.Dual ℂ (FixedPart e M))

/-- Extension to the actual dual, with that dual's recovered coefficient module. -/
def extendToDual (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)
    Module.Dual ℂ (FixedPart e M) →ₗ[ℂ] Dual hA hM := by
  letI := NondegenerateScalars.complexModule hA hM
  letI := NonUnitalModuleCorner.complexModule hA hM e
  letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)
  exact
    { toFun := fun ell => (extension hA hM e ell).val
      map_add' _ _ := Subtype.ext (by ext m; rfl)
      map_smul' c ell := by
        apply Subtype.ext
        apply LinearMap.ext
        intro m
        exact (canonical_smul_apply hA hM c (extension hA hM e ell).val m).symm }

/-- Restriction of any actual dual functional to the original fixed subgroup. -/
def restrictFromDual (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)
    Dual hA hM →ₗ[ℂ] Module.Dual ℂ (FixedPart e M) := by
  letI := NondegenerateScalars.complexModule hA hM
  letI := NonUnitalModuleCorner.complexModule hA hM e
  letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)
  exact
    { toFun := fun φ => φ.val.comp (NonUnitalModuleCorner.inclusionLinear hA hM e)
      map_add' _ _ := by ext x; rfl
      map_smul' c φ := by
        ext x
        exact canonical_smul_apply hA hM c φ x.val }

@[simp] theorem extendToDual_apply (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ∀ (ell : Module.Dual ℂ (FixedPart e M)) (m : M),
      (extendToDual hA hM e ell).val m =
        ell (NonUnitalModuleCorner.projection e m) := fun _ _ => rfl

@[simp] theorem restrictFromDual_apply (e : Idempotent A) (φ : Dual hA hM)
    (x : FixedPart e M) :
    restrictFromDual hA hM e φ x = φ.val x.val := rfl

/-- Precompose a fixed actual bidual functional with the published extension. -/
def toOrdinaryBidual (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := NonUnitalModuleCorner.complexModule hA (bidual_isNondegenerate hA hM) e
    FixedBidual hA hM e →ₗ[ℂ] OrdinaryBidual hA hM e := by
  letI := NonUnitalModuleCorner.complexModule hA hM e
  letI := NonUnitalModuleCorner.complexModule hA (bidual_isNondegenerate hA hM) e
  letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)
  exact
    { toFun := fun Φ => Φ.val.val.comp (extendToDual hA hM e)
      map_add' _ _ := by ext ell; rfl
      map_smul' c Φ := by
        ext ell
        exact congrArg (fun Ψ : FullDual hA.op (isNondegenerate hA hM) =>
          Ψ (extendToDual hA hM e ell)) (canonicalBidual_smul_val hA hM c Φ.val) }

/-- Precompose an ordinary bidual functional with the actual restriction map. -/
def ordinaryToFull (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    OrdinaryBidual hA hM e →ₗ[ℂ] FullDual hA.op (isNondegenerate hA hM) := by
  letI := NonUnitalModuleCorner.complexModule hA hM e
  letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)
  exact
    { toFun := fun Ψ => Ψ.comp (restrictFromDual hA hM e)
      map_add' _ _ := by ext φ; rfl
      map_smul' _ _ := by ext φ; rfl }

/-- The same original idempotent fixes the entire extended full functional. -/
theorem ordinaryToFull_fixed (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fullAction hA.op (isNondegenerate hA hM)
    ∀ Ψ : OrdinaryBidual hA hM e,
      op (op (e : A)) • ordinaryToFull hA hM e Ψ = ordinaryToFull hA hM e Ψ := by
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := NonUnitalModuleCorner.complexModule hA hM e
  let _ := fullAction hA.op (isNondegenerate hA hM)
  intro Ψ
  apply fullDual_ext hA.op (isNondegenerate hA hM)
  intro φ
  change Ψ (restrictFromDual hA hM e (op (e : A) • φ)) =
    Ψ (restrictFromDual hA hM e φ)
  apply congrArg Ψ
  ext x
  change φ.val ((e : A) • x.val) = φ.val x.val
  exact congrArg φ.val (show (e : A) • x.val = x.val from x.property)

/-- The original idempotent gives both actual subtype witnesses. -/
def fromOrdinaryBidual (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := NonUnitalModuleCorner.complexModule hA (bidual_isNondegenerate hA hM) e
    OrdinaryBidual hA hM e →ₗ[ℂ] FixedBidual hA hM e := by
  letI := NonUnitalModuleCorner.complexModule hA hM e
  letI := NonUnitalModuleCorner.complexModule hA (bidual_isNondegenerate hA hM) e
  letI := fullAction hA.op (isNondegenerate hA hM)
  exact
    { toFun := fun Ψ =>
        ⟨⟨ordinaryToFull hA hM e Ψ,
            ⟨oppositeIdempotent (oppositeIdempotent e), ordinaryToFull_fixed hA hM e Ψ⟩⟩,
          Subtype.ext (ordinaryToFull_fixed hA hM e Ψ)⟩
      map_add' _ _ := Subtype.ext (Subtype.ext (by ext φ; rfl))
      map_smul' c Ψ := by
        apply Subtype.ext
        apply Subtype.ext
        exact (canonicalBidual_smul_val hA hM c
          ⟨ordinaryToFull hA hM e Ψ,
            ⟨oppositeIdempotent (oppositeIdempotent e), ordinaryToFull_fixed hA hM e Ψ⟩⟩).symm }

theorem toOrdinaryBidual_apply (e : Idempotent A) (Φ : FixedBidual hA hM e) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ∀ ell : Module.Dual ℂ (FixedPart e M),
      toOrdinaryBidual hA hM e Φ ell =
        Φ.val.val (extendToDual hA hM e ell) := fun _ => rfl

theorem fromOrdinaryBidual_functional (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ∀ Ψ : OrdinaryBidual hA hM e,
      (fromOrdinaryBidual hA hM e Ψ).val.val =
        Ψ.comp (restrictFromDual hA hM e) := fun _ => rfl

/-- The two maps retain the entire original interface and independent universes. -/
example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) → (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := NonUnitalModuleCorner.complexModule hA (bidual_isNondegenerate hA hM) e
    FixedBidual hA hM e →ₗ[ℂ] OrdinaryBidual hA hM e :=
  @toOrdinaryBidual.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) → (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := NonUnitalModuleCorner.complexModule hA (bidual_isNondegenerate hA hM) e
    OrdinaryBidual hA hM e →ₗ[ℂ] FixedBidual hA hM e :=
  @fromOrdinaryBidual.{uA, uM}

end Langlands.Algebra.NonUnitalModuleFixedBidualMaps
