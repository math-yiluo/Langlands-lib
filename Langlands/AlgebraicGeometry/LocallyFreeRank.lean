import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Scheme.Modules

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- An actual module sheaf is locally free of rank `n` if it has a covering family
of local bases, each indexed by a type equivalent to `Fin n`. -/
def IsLocallyFreeOfRank (M : S.Modules) (n : ℕ) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
    q.IsLocallyFreeData ∧ ∀ i, Nonempty ((q.generators i).I ≃ Fin n)

/-- Forgetting the prescribed size of the local bases gives Mathlib local freeness. -/
lemma IsLocallyFreeOfRank.isLocallyFree {M : S.Modules} {n : ℕ}
    (h : IsLocallyFreeOfRank M n) :
    SheafOfModules.IsLocallyFree (R := S.ringCatSheaf) M := by
  obtain ⟨q, hq, _⟩ := h
  exact { exists_isLocallyFreeData := ⟨q, hq⟩ }

/-- A fixed finite local rank also gives Mathlib finite type. -/
lemma IsLocallyFreeOfRank.isFiniteType {M : S.Modules} {n : ℕ}
    (h : IsLocallyFreeOfRank M n) :
    SheafOfModules.IsFiniteType (R := S.ringCatSheaf) M := by
  obtain ⟨q, _, hn⟩ := h
  refine { exists_localGeneratorsData := ⟨q, ?_⟩ }
  refine { isFiniteType := fun i => ?_ }
  exact { finite := Finite.of_equiv (Fin n) (hn i).some.symm }

/-- A free sheaf on `n` generators has the prescribed local rank. -/
lemma isLocallyFreeOfRank_free (n : ℕ) :
    IsLocallyFreeOfRank
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) n := by
  refine ⟨(SheafOfModules.free.generatingSections (ULift.{u} (Fin n))).localGeneratorsData,
    inferInstance, ?_⟩
  intro i
  exact ⟨Equiv.ulift⟩

end Langlands.Scheme.Modules
