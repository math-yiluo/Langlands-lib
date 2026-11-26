import Langlands.Global.AdelicIntertwiningHaarOffset
import Langlands.Global.AdelicIntertwiningClosedQuotient
import Langlands.Global.AdelicSquareIntegrableInducedForms

/-! # The Haar factor of a Levi conjugation in the intertwining integral

Conjugation by a point `m` of the target Levi `M'(𝔸)` acts on the target radical `V(𝔸)` and
preserves the closed stabilizer `V(𝔸) ∩ w U(𝔸) w⁻¹`. The ratio of its Haar moduli on the two
groups is the factor by which the closed-quotient change of variables of the intertwining
integral moves `m` from the external argument into the integrand
(`intertwiningIntegralConjugation`). This file states that the factor is
`δ_Q(m)^{1/2} δ_P(w⁻¹ m w)^{-1/2}`, which is the normalization in Bernstein–Lapid (6.5). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.QuotientIntegration AdelicGroupPoints

/-- The Haar factor of a target Levi conjugation in the intertwining integral (Bernstein–Lapid
(6.5)). Let `G` be connected reductive over a number field, `p : P → G` and `q : Q → G`
parabolics with geometric unipotent radicals `iU`, `iV` and rational Levi subgroups
`l : M → P`, `l' : M' → Q`, and `(w, c)` a Weyl conjugation, so that `c(m) = w⁻¹ m w`. For every
`m ∈ M'(𝔸)`, let `α` be conjugation by `m` on `V(𝔸)` and `αH` its restriction to the closed
stabilizer `H = V(𝔸) ∩ w U(𝔸) w⁻¹`. Then the ratio of their Haar moduli is
`m^{ρ_Q} · c(m)^{-ρ_P}`, i.e. `δ_Q(m)^{1/2} δ_P(c(m))^{-1/2}`, where `ρ_Q = ½ det(Ad | Lie Q)` and
`ρ_P = ½ det(Ad | Lie P)`. -/
def IntertwiningStabilizerModulusStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
    [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
    [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
    (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P) (q : Q ⟶ G) (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsConnectedReductive G → IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsRationalLeviSubgroup l → IsParabolicSubgroup q →
    LeviSubgroup.IsGeometricUnipotentRadical iV → IsRationalLeviSubgroup l' →
    ∀ (hw : IsWeylConjugation p l q l' w c) (hi : IsClosedSubgroup (iU ≫ p))
      (hVu : IsUnipotent V) (hUn : (SubgroupFunctor.range iU).IsNormal)
      (hVn : (SubgroupFunctor.range iV).IsNormal),
      haveI : LocallyCompactSpace
          (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) :=
        (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)).locallyCompactSpace
      haveI : LocallyCompactSpace (intertwiningAdelicStabilizer p iU (iV ≫ q) w) :=
        (intertwiningStabilizer p iU (iV ≫ q) w
          (inferInstance : IsClosedImmersion (iV ≫ q).hom.hom.left) hi hVu).1.locallyCompactSpace
      ∀ m : AdelicGroupPoints F M',
        (((mulEquivHaarChar (EisensteinConstantTerm.conjAdelic q iV hVn (map F M' Q l' m)) /
            mulEquivHaarChar (subgroupAutomorphism (intertwiningAdelicStabilizer p iU (iV ≫ q) w)
              (EisensteinConstantTerm.conjAdelic q iV hVn (map F M' Q l' m))
              (conjAdelic_mem_intertwiningAdelicStabilizer_iff iU iV hw hUn hVn m)) : ℝ≥0) : ℝ) :
            ℂ) =
          parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' m) *
            parameterPower F P (-halfModulusParameter F P) (map F M' P (c ≫ l) m)

end Langlands.Global
