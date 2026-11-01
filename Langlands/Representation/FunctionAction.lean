import Langlands.Representation.Induction.PermutationDual
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Basic.Complex.Basic

/-!
# Inverse pullback on stable function spaces and paired carriers

Renard, French version of 9 July 2026, II.3.1, printed p.43 / PDF p.49,
opening two paragraphs. Stability of the actual function submodule and
injectivity and invariant range of the actual pairing map make explicit
the existence and separation data needed for the source's conventions.
-/

noncomputable section

namespace Langlands.FunctionAction

universe uG uX uD uV

variable {G : Type uG} [Group G]

/-- Invariance of an actual submodule under an actual representation. -/
def IsStable {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (E : Submodule ℂ V) : Prop :=
  ∀ g, E ≤ E.comap (ρ g)

/-- Renard's action on all complex-valued functions, reusing the published
function representation with trivial action on the coefficients. -/
abbrev functionRepresentation (G : Type uG) [Group G]
    (X : Type uX) [MulAction G X] : Representation ℂ G (X → ℂ) :=
  Langlands.Induction.functionRepresentation (Representation.trivial ℂ G ℂ) X

@[simp] theorem functionRepresentation_apply {X : Type uX} [MulAction G X]
    (g : G) (f : X → ℂ) (x : X) :
    functionRepresentation G X g f x = f (g⁻¹ • x) :=
  rfl

variable {X : Type uX} [MulAction G X]
variable (E : Submodule ℂ (X → ℂ)) (hE : IsStable (functionRepresentation G X) E)

/-- The inverse-pullback representation on the given stable function submodule. -/
abbrev stableFunctionRepresentation : Representation ℂ G E :=
  (functionRepresentation G X).subrepresentation E hE

@[simp] theorem stableFunctionRepresentation_apply (g : G) (f : E) (x : X) :
    (stableFunctionRepresentation E hE g f : X → ℂ) x = (f : X → ℂ) (g⁻¹ • x) :=
  rfl

/-- The actual subtype inclusion of the function space is equivariant. -/
theorem stableFunctionRepresentation_subtype (g : G) :
    E.subtype.comp (stableFunctionRepresentation E hE g) =
      (functionRepresentation G X g).comp E.subtype := by
  apply LinearMap.ext
  intro f
  rfl

/-- The full algebraic dual action, with no topology on the function space. -/
abbrev dualRepresentation : Representation ℂ G (Module.Dual ℂ E) :=
  (stableFunctionRepresentation E hE).dual

@[simp] theorem dualRepresentation_apply (g : G) (T : Module.Dual ℂ E) (f : E) :
    dualRepresentation E hE g T f = T (stableFunctionRepresentation E hE g⁻¹ f) :=
  rfl

variable {D : Type uD} [AddCommGroup D] [Module ℂ D]
variable (j : D →ₗ[ℂ] Module.Dual ℂ E) (hinj : Function.Injective j)
variable (hRange : IsStable (dualRepresentation E hE) j.range)

/-- Restrict the dual action to the actual range of the injective pairing map,
then transport it to the given carrier. No action on that carrier is an input. -/
def pairedRepresentation : Representation ℂ G D :=
  (LinearEquiv.ofInjective j hinj).symm.conjRingEquiv.toMonoidHom.comp
    ((dualRepresentation E hE).subrepresentation j.range hRange)

/-- The original pairing map intertwines the constructed and full dual actions. -/
theorem pairedRepresentation_intertwines (g : G) (T : D) :
    j (pairedRepresentation E hE j hinj hRange g T) =
      dualRepresentation E hE g (j T) := by
  change j ((LinearEquiv.ofInjective j hinj).symm
    (((dualRepresentation E hE).subrepresentation j.range hRange) g
      ((LinearEquiv.ofInjective j hinj) T))) = _
  rw [LinearEquiv.ofInjective_symm_apply]
  rfl

/-- Renard's pairing formula for the constructed action. -/
@[simp] theorem pairedRepresentation_pairing (g : G) (T : D) (f : E) :
    j (pairedRepresentation E hE j hinj hRange g T) f =
      j T (stableFunctionRepresentation E hE g⁻¹ f) := by
  rw [pairedRepresentation_intertwines]
  rfl

/-- Separation in the paired-carrier variable gives uniqueness on that same carrier. -/
theorem pairedRepresentation_unique (σ : Representation ℂ G D)
    (hσ : ∀ (g : G) (T : D) (f : E),
      j (σ g T) f = j T (stableFunctionRepresentation E hE g⁻¹ f)) :
    σ = pairedRepresentation E hE j hinj hRange := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro T
  apply hinj
  apply LinearMap.ext
  intro f
  exact (hσ g T f).trans (pairedRepresentation_pairing E hE j hinj hRange g T f).symm

/-- For the identity pairing, the range is the whole algebraic dual and is stable. -/
theorem fullDualRange_stable : IsStable (dualRepresentation E hE)
    (LinearMap.id : Module.Dual ℂ E →ₗ[ℂ] Module.Dual ℂ E).range := by
  intro g T _
  exact ⟨_, rfl⟩

/-- The full algebraic dual as a transparent instance of the paired construction. -/
abbrev fullDualRepresentation : Representation ℂ G (Module.Dual ℂ E) :=
  pairedRepresentation E hE LinearMap.id Function.injective_id (fullDualRange_stable E hE)

/-- The identity-pairing construction is exactly Mathlib's dual representation. -/
@[simp] theorem fullDualRepresentation_eq_dual :
    fullDualRepresentation E hE = dualRepresentation E hE := by
  symm
  apply pairedRepresentation_unique E hE LinearMap.id Function.injective_id
    (fullDualRange_stable E hE)
  intro g T f
  rfl

@[simp] theorem fullDualRepresentation_apply (g : G) (T : Module.Dual ℂ E) (f : E) :
    fullDualRepresentation E hE g T f = T (stableFunctionRepresentation E hE g⁻¹ f) := by
  rw [fullDualRepresentation_eq_dual]
  rfl

variable (F : Submodule ℂ (Module.Dual ℂ E)) (hF : IsStable (dualRepresentation E hE) F)

include hF in
/-- The actual subtype pairing has range the given stable dual submodule. -/
theorem dualSubmoduleRange_stable : IsStable (dualRepresentation E hE) F.subtype.range := by
  simpa only [Submodule.range_subtype] using hF

/-- An invariant submodule of the full dual, using its actual subtype pairing. -/
abbrev dualSubmoduleRepresentation : Representation ℂ G F :=
  pairedRepresentation E hE F.subtype F.subtype_injective
    (dualSubmoduleRange_stable E hE F hF)

/-- The pairing construction on a dual submodule agrees with direct restriction. -/
theorem dualSubmoduleRepresentation_eq_subrepresentation :
    dualSubmoduleRepresentation E hE F hF =
      (dualRepresentation E hE).subrepresentation F hF := by
  symm
  apply pairedRepresentation_unique E hE F.subtype F.subtype_injective
    (dualSubmoduleRange_stable E hE F hF)
  intro g T f
  rfl

@[simp] theorem dualSubmoduleRepresentation_apply (g : G) (T : F) (f : E) :
    (dualSubmoduleRepresentation E hE F hF g T : Module.Dual ℂ E) f =
      (T : Module.Dual ℂ E) (stableFunctionRepresentation E hE g⁻¹ f) :=
  pairedRepresentation_pairing E hE F.subtype F.subtype_injective
    (dualSubmoduleRange_stable E hE F hF) g T f

end Langlands.FunctionAction
