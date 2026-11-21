import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Automorphic.GroupSchemeInvariantForms

/-! # Solutions of `Ξ_main` are automorphic forms

Bernstein–Lapid, §7.2 with the argument of Lemma 8.1 (number field case): if the test functions
of the Harish-Chandra equations of `Ξ_main` are finite under left translation by a subgroup
`K_∞` of the infinite adelic points, then every solution of `Ξ_main(s)` in `𝔉^R_L` is an
automorphic form on `G(F) \ G(𝔸)` for `K_∞`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Solutions of `Ξ_main` are automorphic (Bernstein–Lapid §7.2, Theorem 7.2 and the proof of
Lemma 8.1, number field case). In the setting of `UniformGrowthLocalFinitenessStatement` (group
data `u`, `t`, `z` of `Ξ_main` and admissible analytic data `X` on an open `W ⊆ ℂⁿ`), let
`K_∞` be a subgroup of `G(𝔸_∞)` such that every test function `h i k` of `X` is left
`K_∞`-finite, i.e. `g ↦ h i k g⁻¹` is right `K_∞`-finite. Then for every compact open
`L ≤ G(𝔸_f)`, every `R` and every `s ∈ W`, the underlying function of every solution of
`Ξ_main(s)` in `𝔉^R_L` is an automorphic form on `G(F) \ G(𝔸)`
(`IsAutomorphicFunctionOn` for `rationalSubgroup F G` and `K_∞`). -/
def LocalFinitenessSolutionAutomorphyStatement : Prop :=
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
      ∀ Kinf : Subgroup (InfiniteAdelicGroupPoints F G),
        (∀ i k, IsInfiniteSubgroupFiniteFunction F G Kinf (fun g => X.h i k g⁻¹)) →
      ∀ L : Subgroup (FiniteAdelicGroupPoints F G),
        IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
        IsCompact (L : Set (FiniteAdelicGroupPoints F G)) →
      ∀ (R : ℝ) (s : W),
        ∀ v ∈ X.solutions u (fun α => map F T.toGrp G iT (t α))
            (fun j => map F T.toGrp G iT (z j)) rho hN hrho hsmooth hcalc R L s,
          IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho
            (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v)

end Langlands.Global
