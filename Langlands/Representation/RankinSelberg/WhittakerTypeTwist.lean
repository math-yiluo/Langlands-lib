import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Twist.SubquotientDefinitions
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Whittaker.AlgebraicTwist

/-! Full Whittaker type under scalar twists trivial on the unipotent subgroup. -/

namespace Langlands

universe uR uG uV uF

private theorem compactElement_map {A B : Type*} [PartialOrder A] [PartialOrder B]
    (e : A ≃o B) {a : A} (ha : IsCompactElement a) : IsCompactElement (e a) := by
  intro s u hs hd hl hau
  have hd' : DirectedOn (· ≤ ·) (e.symm '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hd x hx y hy
    exact ⟨e.symm z, ⟨z, hz, rfl⟩, e.symm.monotone hxz, e.symm.monotone hyz⟩
  obtain ⟨_, ⟨x, hx, rfl⟩, hax⟩ := ha (e.symm '' s) (e.symm u)
    (hs.image e.symm) hd' ((e.symm.isLUB_image').mpr hl)
    (by simpa using e.symm.monotone hau)
  exact ⟨x, hx, by simpa using e.monotone hax⟩

section Algebraic

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- Twisting retains the ordered lattice of submodules over the group algebra. -/
noncomputable def twistAsModuleSubmoduleOrderIso (χ : G →* Rˣ) (ρ : Representation R G V) :
    Submodule (MonoidAlgebra R G) ρ.asModule ≃o
      Submodule (MonoidAlgebra R G) (twist χ ρ).asModule :=
  (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm.trans
    ((twistSubrepresentationOrderIso χ ρ).trans
      (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := twist χ ρ)))

/-- Scalar twists preserve finite generation over the actual group algebra. -/
theorem finite_asModule_twist_iff (χ : G →* Rˣ) (ρ : Representation R G V) :
    Module.Finite (MonoidAlgebra R G) (twist χ ρ).asModule ↔
      Module.Finite (MonoidAlgebra R G) ρ.asModule := by
  rw [Module.finite_def, Module.finite_def, Submodule.fg_iff_compact,
    Submodule.fg_iff_compact]
  constructor
  · intro h
    simpa using compactElement_map (twistAsModuleSubmoduleOrderIso χ ρ).symm h
  · intro h
    simpa using compactElement_map (twistAsModuleSubmoduleOrderIso χ ρ) h

end Algebraic

namespace RankinSelberg

open Whittaker GeneralLinear

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (θ : upperUnipotent (n + 1) F →* ℂˣ)
  (χ : Langlands.GeneralLinear (n + 1) F →* ℂˣ)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- An open-kernel twist trivial on the Whittaker subgroup preserves full type. -/
theorem isOfWhittakerType_twist_iff
    (hopen : IsOpen (χ.ker : Set (Langlands.GeneralLinear (n + 1) F)))
    (hχ : ∀ u : upperUnipotent (n + 1) F, χ u.val = 1) :
    IsOfWhittakerType n θ (twist χ π) ↔ IsOfWhittakerType n θ π := by
  unfold IsOfWhittakerType
  rw [isAdmissible_twist_iff χ π hopen, finite_asModule_twist_iff χ π]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  let e := twistFunctionalEquiv (upperUnipotent (n + 1) F) θ χ hχ π
  exact ⟨fun ⟨l⟩ => ⟨e.trans l⟩, fun ⟨l⟩ => ⟨e.symm.trans l⟩⟩

end RankinSelberg
end Langlands
