import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Automorphic.GroupSchemeInvariantForms

/-! # Stability of the solutions of `Ξ_main` under the center of the enveloping algebra

Bernstein–Lapid, proof of Lemma 8.1 (number field case): all equations of `Ξ_main` commute with
the action of the center `𝔷` of the universal enveloping algebra, so the solution space of
`Ξ_main(s)` in `𝔉^R_L` is `𝔷`-stable. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- `𝔷`-stability of the solutions of `Ξ_main` (Bernstein–Lapid, proof of Lemma 8.1, number
field case). In the setting of `UniformGrowthLocalFinitenessStatement` (group data `u`, `t`, `z`
of `Ξ_main` and admissible analytic data `X` on an open `W ⊆ ℂⁿ`), for every compact open
`L ≤ G(𝔸_f)`, every `R`, every `s ∈ W`, every solution `v` of `Ξ_main(s)` in `𝔉^R_L` and every
element `Y` of the center of the complex enveloping algebra, the function `Y v` is again the
function of a solution of `Ξ_main(s)` in `𝔉^R_L`. -/
def LocalFinitenessCenterStabilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (T : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (iT : T.toGrp ⟶ G) (ν : cocharacterLattice T),
    IsConnectedReductive G → IsMaximalSplitTorus iT → IsGenericCocharacter iT ν →
    ∀ (Ua : simpleRelativeRoots iT ν → GroupScheme (Spec (CommRingCat.of F)))
      [∀ α, IsAffine (Ua α).X.left] (u : ∀ α, Ua α ⟶ G)
      [∀ α, IsClosedImmersion (u α).hom.hom.left]
      (t : simpleRelativeRoots iT ν → AdelicGroupPoints F T.toGrp) (r : ℕ)
      (z : Fin r → AdelicGroupPoints F T.toGrp),
      IsLocalFinitenessGroupData iT ν u t z →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
      (hrho : IsClosedSubgroup rho) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (n : ℕ) (W : TopologicalSpace.Opens (Fin n → ℂ))
      (X : LocalFinitenessData F G (simpleRelativeRoots iT ν) r n W),
      X.IsAdmissible →
      ∀ L : Subgroup (FiniteAdelicGroupPoints F G),
        IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
        IsCompact (L : Set (FiniteAdelicGroupPoints F G)) →
      ∀ (R : ℝ) (s : W),
        ∀ v ∈ X.solutions u (fun α => map F T.toGrp G iT (t α))
            (fun j => map F T.toGrp G iT (z j)) rho hN hrho hsmooth hcalc R L s,
        ∀ Y : AdelicEnvelopingCenter F G hsmooth,
          ∃ w ∈ X.solutions u (fun α => map F T.toGrp G iT (t α))
              (fun j => map F T.toGrp G iT (z j)) rho hN hrho hsmooth hcalc R L s,
            (w : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val =
              adelicCenterAction F G hsmooth hcalc Y
                (v : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val

end Langlands.Global
