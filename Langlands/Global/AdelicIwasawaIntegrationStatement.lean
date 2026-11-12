import Langlands.Global.AdelicParabolicModulus
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # The Iwasawa integration formula on `G(𝔸_F)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal CompactlySupported Pointwise

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

/-- **Iwasawa integration formula** (Mœglin–Waldspurger I.1.13). For every number field `F`,
connected reductive `G` over `F`, cocharacter `χ` of `G` with representing group schemes
`P`, `M`, `U` of the dynamic parabolic `P(χ)`, its Levi factor `Z(χ)` and its unipotent
radical `U(χ)`, and every compact subgroup `K` of `G(𝔸_F)` with `P(𝔸_F) K = G(𝔸_F)`, there is
a constant `c > 0` such that for every compactly supported continuous `f : G(𝔸_F) → ℂ`
`∫_{G(𝔸_F)} f(g) dg = c ∫_K ∫_{M(𝔸_F)} ∫_{U(𝔸_F)} f(u m k) δ_P(m)⁻¹ du dm dk`,
where `dg`, `dm`, `du` are Mathlib's Haar measures and `dk` is the Haar probability on `K`. -/
def AdelicIwasawaIntegrationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (P M U : GroupScheme (Spec (CommRingCat.of F)))
    (iP : P ⟶ G) (iM : M ⟶ G) (iU : U ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hM : (Dynamic.centralizer χ).IsRepresentedBy iM)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy iU),
    haveI := hG.isAffineHom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := isAffine_parabolic F hP
    haveI := isAffine_centralizer F hM
    haveI := locallyOfFiniteType_centralizer F hM
    haveI := isAffine_unipotent F hU
    haveI := locallyOfFiniteType_unipotent F hU
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsCompact (K : Set (AdelicGroupPoints F G))),
      Set.range (map F P G iP) * (K : Set (AdelicGroupPoints F G)) = Set.univ →
      ∃ c : ℝ≥0, 0 < c ∧ ∀ f : C_c(AdelicGroupPoints F G, ℂ),
        ∫ g, f g ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
          (c : ℝ) • ∫ k, ∫ m, ∫ u,
            ((parabolicModulus F hP hU
                (map F M P (Dynamic.centralizerToParabolic hP hM) m) : ℝ≥0) : ℝ)⁻¹ •
              f (map F U G iU u * map F M G iM m * (k : AdelicGroupPoints F G))
            ∂(Measure.haar : Measure (AdelicGroupPoints F U))
            ∂(Measure.haar : Measure (AdelicGroupPoints F M))
            ∂(compactHaarProbability F G K hK)

end Langlands.Global.AdelicGroupPoints
