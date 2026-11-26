import Langlands.Global.AdelicIntertwiningAutomorphyStatement
import Langlands.Global.AdelicSquareIntegrableInducedForms

/-! # The normalized Harish-Chandra transfer of the center to a Levi subgroup

For a parabolic `Q = M'V` of a connected reductive group `G` over a number field, the center `𝔷`
of the complex enveloping algebra of `G(F_∞)` acts on functions on `G(F_∞)` that are left
invariant under `V(F_∞)` through their normalized restrictions `m ↦ δ_Q(m)^{-1/2} f(m g)` to
`M'(F_∞)`, by the normalized Harish-Chandra homomorphism `𝔷 → 𝔷(𝔪')`. This homomorphism depends
only on the Levi subgroup: for a second parabolic `P = MU` and a rational point `w` with
`w M w⁻¹ = M'`, it is the transport of the one of `P` along conjugation by `w`. This file states
that one element of the enveloping algebra of `M'(F_∞)` realizes both transfers. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints

/-- The normalized Harish-Chandra transfer of the center to a Levi subgroup, common to two
Weyl-conjugate parabolics (Mœglin–Waldspurger I.2.17; Bernstein–Lapid (6.5) and the proof of the
Lemma in §8.2). Let `G` be connected reductive over a number field `F`, `p : P → G` and
`q : Q → G` parabolics with geometric unipotent radicals `iU`, `iV` and rational Levi subgroups
`l : M → P`, `l' : M' → Q`, and let `(w, c)` be a Weyl conjugation, so that
`c(m') = w⁻¹ m' w`. Fix smooth structures on `G` and `M'`. For every element `z` of the center of
the complex enveloping algebra of `G(F_∞)` there is an element `y` of the complex enveloping
algebra of `M'(F_∞)` such that, for every point `g` of `G(F_∞)`:

1. for every plot-smooth `f` on `G(F_∞)` left invariant under `V(F_∞)`, `y` applied to
   `m' ↦ δ_Q(m')^{-1/2} f(m' g)` is `m' ↦ δ_Q(m')^{-1/2} (z f)(m' g)`;
2. for every plot-smooth `f` on `G(F_∞)` left invariant under `U(F_∞)`, `y` applied to
   `m' ↦ δ_P(c(m'))^{-1/2} f(c(m') g)` is `m' ↦ δ_P(c(m'))^{-1/2} (z f)(c(m') g)`.

Here `δ_Q(m')^{1/2}` is `m'^{ρ_Q}` for the parameter `ρ_Q = ½ det(Ad | Lie Q)`, and similarly for
`P`. The restricted functions are always plot-smooth; the clauses are stated for every proof of
this. -/
def LeviRestrictionCenterTransferStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
    [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [IsAffine M'.X.left]
    (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P) (q : Q ⟶ G) (iV : V ⟶ Q) (l' : M' ⟶ Q)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsConnectedReductive G → IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsRationalLeviSubgroup l → IsParabolicSubgroup q →
    LeviSubgroup.IsGeometricUnipotentRadical iV → IsRationalLeviSubgroup l' →
    IsWeylConjugation p l q l' w c →
    ∀ {d d' : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (hsmooth' : SmoothOfRelativeDimension d' M'.X.hom)
      (hcalc' : AdelicDifferentialCommutator F M' hsmooth')
      (z : AdelicEnvelopingCenter F G hsmooth),
      let Ainf := CommAlgCat.of F (InfiniteAdeleRing F)
      let ιQ : InfiniteAdelicGroupPoints F M' → InfiniteAdelicGroupPoints F G :=
        M'.affinePointsTarget (l' ≫ q) Ainf
      let ιP : InfiniteAdelicGroupPoints F M' → InfiniteAdelicGroupPoints F G :=
        M'.affinePointsTarget (c ≫ l ≫ p) Ainf
      let δQ : InfiniteAdelicGroupPoints F M' → ℂ := fun m =>
        parameterPower F Q (-halfModulusParameter F Q) (map F M' Q l' (ofInfinite F M' m))
      let δP : InfiniteAdelicGroupPoints F M' → ℂ := fun m =>
        parameterPower F P (-halfModulusParameter F P) (map F M' P (c ≫ l) (ofInfinite F M' m))
      ∃ y : AdelicEnvelopingAlgebra F M' hsmooth',
        (∀ (f : InfiniteAdelicGroupPoints F G → ℂ) (hf : f ∈ InfinitePlotSmoothFunctions F G),
          (∀ (v : InfiniteAdelicGroupPoints F V) (x : InfiniteAdelicGroupPoints F G),
            f (V.affinePointsTarget (iV ≫ q) Ainf v * x) = f x) →
          ∀ (g : InfiniteAdelicGroupPoints F G)
            (h : (fun m => δQ m * f (ιQ m * g)) ∈ InfinitePlotSmoothFunctions F M'),
            ((plotSmoothEnvelopingAction F M' hsmooth' hcalc' y) ⟨_, h⟩ :
                InfiniteAdelicGroupPoints F M' → ℂ) =
              fun m => δQ m * (plotSmoothCenterAction F G hsmooth hcalc z ⟨f, hf⟩ :
                InfiniteAdelicGroupPoints F G → ℂ) (ιQ m * g)) ∧
        (∀ (f : InfiniteAdelicGroupPoints F G → ℂ) (hf : f ∈ InfinitePlotSmoothFunctions F G),
          (∀ (u : InfiniteAdelicGroupPoints F U) (x : InfiniteAdelicGroupPoints F G),
            f (U.affinePointsTarget (iU ≫ p) Ainf u * x) = f x) →
          ∀ (g : InfiniteAdelicGroupPoints F G)
            (h : (fun m => δP m * f (ιP m * g)) ∈ InfinitePlotSmoothFunctions F M'),
            ((plotSmoothEnvelopingAction F M' hsmooth' hcalc' y) ⟨_, h⟩ :
                InfiniteAdelicGroupPoints F M' → ℂ) =
              fun m => δP m * (plotSmoothCenterAction F G hsmooth hcalc z ⟨f, hf⟩ :
                InfiniteAdelicGroupPoints F G → ℂ) (ιP m * g))

end Langlands.Global
