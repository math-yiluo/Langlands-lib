import Langlands.AlgebraicGeometry.Modules.CoherentClosure
import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Finite coherent filtrations by integral closed ideal sheaves -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Modules

/-- A coherent module on a Noetherian scheme admits a finite filtration
whose successive quotients are actual closed-immersion pushforwards of
nonzero coherent ideal sheaves on integral schemes. -/
def CoherentIntegralIdealFiltrationStatement : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X] (M : X.Modules),
    M.IsQuasicoherent → HasFiniteAffineSections M →
    ∃ (n : ℕ) (F : Fin (n + 1) → X.Modules),
      IsZero (F 0) ∧
      Nonempty (F (Fin.last n) ≅ M) ∧
      (∀ j, (F j).IsQuasicoherent ∧ HasFiniteAffineSections (F j)) ∧
      ∀ j : Fin n, ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
        IsClosedImmersion i ∧ IsIntegral Z ∧
        ∃ (I : Z.Modules) (ι : I ⟶ structureModule Z),
          Mono ι ∧ I.IsQuasicoherent ∧ HasFiniteAffineSections I ∧
          ¬ IsZero I ∧
          ∃ (α : F j.castSucc ⟶ F j.succ)
            (β : F j.succ ⟶ (Scheme.Modules.pushforward i).obj I)
            (h : α ≫ β = 0),
              (ShortComplex.mk α β h).ShortExact

end Langlands.AlgebraicGeometry.Modules
