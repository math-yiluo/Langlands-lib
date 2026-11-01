import Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingStatement
import Langlands.AlgebraicGeometry.Modules.NoetherianVanishing.Induction

/-!
# Vanishing of quasi-coherent cohomology above the dimension: proof

Every irreducible closed subset of a space of dimension at most `d` has height at most `d`, so
the induction on the height of the support, applied with the closed set `X` itself, gives
`Hⁿ(X, M) = 0` for `n > d`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Modules

open QuasicoherentLocal NoetherianVanishing in
/-- On a noetherian separated scheme of dimension at most `d`, the cohomology of a
quasi-coherent module vanishes in every degree above `d`. -/
theorem noetherianSeparatedQuasicoherentVanishing :
    NoetherianSeparatedQuasicoherentVanishingStatement.{u} := by
  intro R X f _ _ d hd M hM n hn
  refine isZero_relativeCohomology_of_height f (d + 1) ⊤ M
    (IsAffineLocallyQuasicoherent.of_isQuasicoherent M) ?_ ?_ n hn
  · refine (VanishesOn.bot M).mono (fun x hx => ?_)
    exact absurd (Set.mem_univ x) hx
  · intro T _
    have h := height_le_of_topologicalKrullDim_le hd T
    exact (ENat.lt_add_one_iff (ENat.natCast_ne_top d)).2 h |>.trans_eq (by push_cast; rfl)

end Langlands.AlgebraicGeometry.Modules
