import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficientAlgebra
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Actual semisimplicity and the affine operator module -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation.AffineSemisimpleModules

open AffineCoefficientAlgebra

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n)

local instance operatorRing : Ring (operatorAlgebra ρ) := inferInstance

/-- A stable ground-field subspace with its action by the affine operator algebra. -/
def operatorSubmodule (W : Submodule k (n → k)) (hW : ρ.IsStableSubspace W) :
    Submodule (operatorAlgebra ρ) (n → k) where
  __ := W.toAddSubmonoid
  smul_mem' a _ hv := (isStableSubspace_iff ρ W).mp hW a.property _ hv

@[simp]
theorem operatorSubmodule_restrictScalars
    (W : Submodule k (n → k)) (hW : ρ.IsStableSubspace W) :
    (operatorSubmodule ρ W hW).restrictScalars k = W := rfl

@[simp]
theorem operatorSubmodule_restrictScalars'
    (S : Submodule (operatorAlgebra ρ) (n → k)) :
    operatorSubmodule ρ (S.restrictScalars k) (stable_restrictScalars ρ S) = S := by
  ext
  rfl

/-- A simple operator submodule is precisely a simple actual stable subspace. -/
theorem isSimpleModule_iff (S : Submodule (operatorAlgebra ρ) (n → k)) :
    IsSimpleModule (operatorAlgebra ρ) S ↔
      ρ.IsStableSubspace (S.restrictScalars k) ∧ S.restrictScalars k ≠ ⊥ ∧
        ∀ U : Submodule k (n → k), ρ.IsStableSubspace U →
          U ≤ S.restrictScalars k → U = ⊥ ∨ U = S.restrictScalars k := by
  rw [isSimpleModule_iff_isAtom]
  constructor
  · intro hAtom
    refine ⟨stable_restrictScalars ρ S, ?_, ?_⟩
    · exact fun h0 => hAtom.1 ((Submodule.restrictScalars_eq_bot_iff k _ _).mp h0)
    · intro U hU hle
      let V := operatorSubmodule ρ U hU
      have hVS : V ≤ S := hle
      rcases eq_or_lt_of_le hVS with h | h
      · right
        exact congrArg (Submodule.restrictScalars k) h
      · left
        exact congrArg (Submodule.restrictScalars k) (hAtom.2 V h)
  · rintro ⟨_, hne, hmin⟩
    refine ⟨fun h0 => hne (by simp [h0]), fun V hVS => ?_⟩
    rcases hmin (V.restrictScalars k) (stable_restrictScalars ρ V) hVS.le with h | h
    · exact (Submodule.restrictScalars_eq_bot_iff k _ _).mp h
    · exact (hVS.ne ((Submodule.restrictScalars_inj k _ _).mp h)).elim

/-- The raw simple-subspace sum in Milne 4.19 is the semisimplicity of the
operator module. -/
theorem isSemisimpleModule_iff :
    IsSemisimpleModule (operatorAlgebra ρ) (n → k) ↔
      sSup {W : Submodule k (n → k) |
        ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
          ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W →
            U = ⊥ ∨ U = W} = ⊤ := by
  have hs : Submodule.restrictScalars k ''
      {S : Submodule (operatorAlgebra ρ) (n → k) | IsSimpleModule (operatorAlgebra ρ) S} =
      {W : Submodule k (n → k) |
        ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
          ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W →
            U = ⊥ ∨ U = W} := by
    ext W
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact (isSimpleModule_iff ρ S).mp hS
    · intro hW
      refine ⟨operatorSubmodule ρ W hW.1, ?_, rfl⟩
      exact (isSimpleModule_iff ρ _).mpr hW
  rw [← hs, ← Submodule.restrictScalars_sSup,
    Submodule.restrictScalars_eq_top_iff]
  exact sSup_simples_eq_top_iff_isSemisimpleModule.symm

/-- A semisimple actual representation has a finite independent family of
simple stable subspaces spanning the full coordinate space. -/
theorem exists_finite_simple_decomposition
    (hρ : sSup {W : Submodule k (n → k) |
      ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W →
          U = ⊥ ∨ U = W} = ⊤) :
    ∃ (r : ℕ) (W : Fin r → Submodule k (n → k)),
      (∀ i, ρ.IsStableSubspace (W i) ∧ W i ≠ ⊥ ∧
        ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W i →
          U = ⊥ ∨ U = W i) ∧ iSupIndep W ∧ iSup W = ⊤ := by
  classical
  let : IsSemisimpleModule (operatorAlgebra ρ) (n → k) :=
    (isSemisimpleModule_iff ρ).mpr hρ
  obtain ⟨s, hind, hsup, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (operatorAlgebra ρ) (n → k)
  have hind' := (sSupIndep_iff _).mp hind
  have hres : iSupIndep (fun S : s => S.1.restrictScalars k) := by
    intro i
    simpa only [Submodule.restrictScalars_iSup] using
      (Submodule.disjoint_restrictScalars_iff k).mpr (hind' i)
  have hne (S : s) : S.1.restrictScalars k ≠ ⊥ :=
    ((isSimpleModule_iff ρ S.1).mp (hsimple S.1 S.2)).2.1
  let : Finite s := WellFoundedGT.finite_of_iSupIndep hres hne
  let e := (Finite.equivFin s).symm
  refine ⟨Nat.card s, (fun i => (e i).1.restrictScalars k), ?_,
    hres.comp e.injective, ?_⟩
  · intro i
    exact (isSimpleModule_iff ρ (e i).1).mp (hsimple _ (e i).2)
  · have heq : (⨆ i, (e i).1.restrictScalars k) =
        ⨆ S : s, S.1.restrictScalars k :=
      e.iSup_comp (g := fun S : s => S.1.restrictScalars k)
    rw [heq]
    rw [← Submodule.restrictScalars_iSup, ← sSup_eq_iSup', hsup]
    rfl

end Langlands.GroupScheme.MatrixRepresentation.AffineSemisimpleModules
