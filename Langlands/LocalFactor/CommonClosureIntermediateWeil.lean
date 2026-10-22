import Langlands.Weil.Local.IntermediateWeil
import Langlands.LocalFactor.CommonClosureWeilDeligne

/-!
# Standalone Weil groups in the prescribed common closure
-/

noncomputable section

namespace Langlands.LocalFactor.CommonClosure

open Weil.Local

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : Extension F)

/-- The standalone Weil group of this very intermediate field, in the common closure. -/
abbrev standaloneWeilEquiv : localWeilGroup (E.asPadicField (p := p)) ≃ₜ* weilSubgroup F E :=
  intermediateWeilEquiv F E

/-- Base degree is relative residue degree times standalone degree, in multiplicative notation. -/
theorem standaloneWeilEquiv_baseDegree (w : localWeilGroup (E.asPadicField (p := p))) :
    CommonClosureSpectral.baseDegree F E (standaloneWeilEquiv F E w) =
      localDegree (E.asPadicField (p := p)) w ^
        extensionResidueDegree F (E.asPadicField (p := p)) (intermediateEmbedding F E) := rfl

/-- Integer geometric degree uses the actual residue-degree factor. -/
theorem standaloneWeilEquiv_degree (w : localWeilGroup (E.asPadicField (p := p))) :
    (CommonClosureSpectral.baseDegree F E (standaloneWeilEquiv F E w)).toAdd =
      extensionResidueDegree F (E.asPadicField (p := p)) (intermediateEmbedding F E) *
        localDegreeInt (E.asPadicField (p := p)) w :=
  intermediateWeilEquiv_degree F E w

/-- The existing restricted norm is exactly the standalone norm. -/
theorem standaloneWeilEquiv_normCharacter (w : localWeilGroup (E.asPadicField (p := p))) :
    CommonClosureWeilDeligne.normCharacter F E (standaloneWeilEquiv F E w) =
      localNormCharacter (E.asPadicField (p := p)) w :=
  intermediateWeilEquiv_normCharacter F E w

/-- In the inverse direction the existing restricted norm remains unchanged. -/
theorem standaloneWeilEquiv_symm_normCharacter (x : weilSubgroup F E) :
    localNormCharacter (E.asPadicField (p := p)) ((standaloneWeilEquiv F E).symm x) =
      CommonClosureWeilDeligne.normCharacter F E x :=
  intermediateWeilEquiv_symm_normCharacter F E x

/-- The kernel-of-base-degree convention agrees with the constructed subgroup inertia. -/
theorem commonClosureInertia_eq :
    CommonClosureWeilDeligne.inertia F E = intermediateInertia F E := rfl

@[simp] theorem standaloneWeilEquiv_mem_inertia (w : localWeilGroup (E.asPadicField (p := p))) :
    standaloneWeilEquiv F E w ∈ CommonClosureWeilDeligne.inertia F E ↔
      w ∈ localInertia (E.asPadicField (p := p)) :=
  intermediateWeilEquiv_mem_inertia F E w

@[simp] theorem standaloneWeilEquiv_symm_mem_inertia (x : weilSubgroup F E) :
    (standaloneWeilEquiv F E).symm x ∈ localInertia (E.asPadicField (p := p)) ↔
      x ∈ CommonClosureWeilDeligne.inertia F E :=
  intermediateWeilEquiv_symm_mem_inertia F E x

/-- Continuous identification with the exact inertia subgroup used by the existing wrappers. -/
abbrev standaloneInertiaEquiv : localInertia (E.asPadicField (p := p)) ≃ₜ*
    CommonClosureWeilDeligne.inertia F E :=
  intermediateInertiaEquiv F E

end Langlands.LocalFactor.CommonClosure
