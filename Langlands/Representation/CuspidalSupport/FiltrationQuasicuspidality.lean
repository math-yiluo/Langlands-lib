import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Filtration.CoinvariantVanishingStatement

namespace Langlands

open CategoryTheory

universe uR uG uV uF

namespace Jacquet

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]

/-- Vanishing coinvariants of every graded piece force vanishing for the
filtered representation. This uses only the quotient universal property. -/
theorem coinvariants_subsingleton_of_filtration
    {A : Rep.{uV} R G} {m : ℕ} (s : ObjectRepFiltration A m) (N : Subgroup G)
    (h : ∀ i, Subsingleton (Coinvariants (s.gradedRepresentation i).ρ N)) :
    Subsingleton (Coinvariants A.ρ N) := by
  have hstep : ∀ j : Fin (m + 1),
      (s.subrepresentation j).toSubmodule ≤ relations A.ρ N := by
    intro j
    induction j using Fin.induction with
    | zero =>
        rw [s.subrepresentation_zero]
        exact bot_le
    | succ i ih =>
        let U := s.subrepresentation i.succ
        let D := (s.step i.castSucc).lowerInUpper (s.step i.succ)
          (Discrete.mk PUnit.unit)
        let f : U.toSubmodule →ₗ[R] Coinvariants A.ρ N :=
          (mk A.ρ N).comp U.toSubmodule.subtype
        have hf : D.toSubmodule ≤ LinearMap.ker f := by
          intro v hv
          exact (mk_eq_zero A.ρ N v.val).mpr (ih hv)
        let g : s.gradedRepresentation i →ₗ[R] Coinvariants A.ρ N :=
          D.toSubmodule.liftQ f hf
        have hg : ∀ a : N,
            g.comp ((s.gradedRepresentation i).ρ a) = g := by
          intro a
          apply LinearMap.ext
          intro x
          obtain ⟨v, rfl⟩ := s.gradedProjection_surjective i x
          change mk A.ρ N (A.ρ a v.val) = mk A.ρ N v.val
          exact mk_apply_subgroup A.ρ N a v.val
        let k := lift (s.gradedRepresentation i).ρ N g hg
        have hz (x : s.gradedRepresentation i) : g x = 0 := by
          let := h i
          calc
            g x = k (mk (s.gradedRepresentation i).ρ N x) := rfl
            _ = k 0 := congrArg k (Subsingleton.elim _ _)
            _ = 0 := map_zero k
        intro v hv
        apply (mk_eq_zero A.ρ N v).mp
        exact hz ((s.gradedProjection i).hom ⟨v, hv⟩)
  have hall : ∀ v : A, mk A.ρ N v = 0 := by
    intro v
    apply (mk_eq_zero A.ρ N v).mpr
    apply hstep (Fin.last m)
    rw [s.subrepresentation_last]
    trivial
  refine ⟨fun x y => ?_⟩
  obtain ⟨v, rfl⟩ := mk_surjective A.ρ N x
  obtain ⟨w, rfl⟩ := mk_surjective A.ρ N y
  rw [hall v, hall w]

/-- The fully quantified finite-filtration coinvariant vanishing statement. -/
theorem coinvariantFiltrationVanishing :
    CoinvariantFiltrationVanishingTheorem.{uR, uG, uV} := by
  intro R _ G _ A m s N h
  exact coinvariants_subsingleton_of_filtration s N h

end Jacquet

namespace CuspidalSupport

open GeneralLinear Geometric

/-- Quasicuspidality is closed under the published finite object filtrations.
No smoothness, admissibility or splitting assumption is needed for this step. -/
theorem isLeviQuasicuspidal_of_filtration
    {F : Type uF} [Field F] {n : ℕ} (B : BlockShape n)
    {A : Rep.{uV} ℂ (B.Levi F)} {m : ℕ} (s : ObjectRepFiltration A m)
    (h : ∀ i, IsLeviQuasicuspidal B (s.gradedRepresentation i).ρ) :
    IsLeviQuasicuspidal B A.ρ := by
  intro S hS
  exact Jacquet.coinvariants_subsingleton_of_filtration s
    (refinedUnipotent F B S) (fun i => h i S hS)

end CuspidalSupport
end Langlands
