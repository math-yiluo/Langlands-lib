import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.Global.PositiveRealTorusIntrinsic

/-! # Finiteness of constant terms under the positive split component

Bernstein–Lapid §6.2 (decomposition (6.3)) and §8.5, after Mœglin–Waldspurger I.3.2: for
parabolics `P = M U ⊇ P' = M' U'` of a connected reductive group `G` over a number field and an
automorphic form `φ` on `U(𝔸)M(F) \ G(𝔸)`, the constant term `C_{P,P'}φ` of `φ` along `U'` is an
automorphic form on `U'(𝔸)M'(F) \ G(𝔸)`, and its left translates by the positive real points
`𝔄_{P'} = 𝔄_0 ∩ S_{M'}(𝔸)` of the split centre of `M'` span a finite-dimensional space. This
finiteness is what makes the decomposition of `C_{P,P'}φ` into finitely many generalized
`𝔄_{P'}`-eigenvectors possible. The module defines `𝔄_{P'}` and states the finiteness; it does
not prove it. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The points of the positive real torus `𝔄_0` of `T` (the image under `i` of the points of
`T(𝔸)` all of whose characters are positive scalar ideles, `PositiveRealTorus.imageSubgroup`)
that commute with the image of `M'(𝔸)` under `j : M' → G`. For a maximal split torus `T`
contained in a Levi subgroup `M'` this is Mœglin–Waldspurger's `A_{M'} = A_{M_0} ∩ Z_{M'}`
(I.2.1), which is Bernstein–Lapid's `𝔄_{P'} = 𝔄_0 ∩ S_{M'}(𝔸)` (§6.2), where `S_{M'}` is the
maximal split torus in the centre of `M'`. -/
def positiveCentralTorusPoints {F : Type u} [Field F] [NumberField F]
    {G M' : GroupScheme (Spec (CommRingCat.of F))} (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) (j : M' ⟶ G) : Subgroup (AdelicGroupPoints F G) :=
  PositiveRealTorus.imageSubgroup F T G i ⊓ Subgroup.centralizer (Set.range (map F M' G j))

/-- Finiteness of constant terms under the positive split component (Bernstein–Lapid §6.2,
decomposition (6.3), and §8.5; Mœglin–Waldspurger I.3.2). Let `p : P → G` and `p' : P' → G` be
parabolic subgroups of a connected reductive group `G` over a number field `F`, with geometric
unipotent radicals `iU : U → P`, `iU' : U' → P'`, rational Levi subgroups `l : M → P`,
`l' : M' → P'` and `P' ⊆ P`. Let `i : T → G` be a maximal split torus factoring through `M'` by
`τ`. Let `K` be a maximal compact subgroup of `G(𝔸)` with `P'(𝔸)K = G(𝔸)`, `rho` a closed
embedding and `φ` an automorphic form on `U(𝔸)M(F) \ G(𝔸)` for the archimedean part of `K` and
the adelic norm of `rho`. Then the functions `g ↦ C_{U'}φ(x g)`, for `x` in
`𝔄_{P'} = positiveCentralTorusPoints T i (l' ≫ p')`, span a finite-dimensional complex vector
space, where `C_{U'}φ = subgroupConstantTerm F (iU' ≫ p') φ` is the constant term of `φ` along
`U'`. -/
def ConstantTermSplitComponentFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine P'.X.left] [IsAffine U'.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
    [IsClosedImmersion (iU' ≫ p').hom.hom.left]
    (i : T.toGrp ⟶ G) (τ : T.toGrp ⟶ M'),
    IsConnectedReductive G →
    IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsRationalLeviSubgroup l →
    IsParabolicSubgroup p' → LeviSubgroup.IsGeometricUnipotentRadical iU' →
    IsRationalLeviSubgroup l' →
    IsMaximalSplitTorus i → τ ≫ l' ≫ p' = i →
    SubgroupFunctor.range p' ≤ SubgroupFunctor.range p →
    ∀ (K : Subgroup (AdelicGroupPoints F G)), IsMaximalCompactSubgroup F G K →
      IsIwasawaCompact p' K →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom)
        (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
        IsClosedSubgroup rho →
        IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
          (K.comap (ofInfinite F G).toMonoidHom) rho φ →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x :
            positiveCentralTorusPoints T i (l' ≫ p') =>
          fun g : AdelicGroupPoints F G =>
            subgroupConstantTerm F (iU' ≫ p') φ ((x : AdelicGroupPoints F G) * g)))

end Langlands.Global
