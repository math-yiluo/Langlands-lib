# Smoothness of the metaplectic representation and one-parameter subgroups

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
The counterpart is the smoothness of the Weil representation (GKT Theorem 9.23), in the sense of
Lie groups. The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.Metaplectic.Smooth` proves the smoothness of Schwartz vectors and
constructs the one-parameter subgroups of `RealMetaplecticGroup l` over those of `Sp_{2l}(ℝ)`.

## Content

- `RealMetaplecticGroup.contDiff_weil_comp`: if `γ : ℝᵏ → Mp` is continuous and the entries of
  `proj (γ t)` are smooth, then `t ↦ weil (γ t) (f ∈ L²)` is smooth for every Schwartz `f`: near each
  `t₀`, `(γ t₀)⁻¹ γ t` acts by the explicit big-cell operator, whose derivative is again an operator of
  the same kind applied to Schwartz functions, and induction on the order gives `C^∞`.
- `exp_mem_symplecticGroup` and `mem_sp_of_exp_mem_symplecticGroup`: `X ∈ sp` if and only if all
  `exp (t • X)` are symplectic.
- `RealMetaplecticGroup.oneParameter X`, for `X ∈ LieAlgebra.Symplectic.sp l ℝ`: the lift through `1`
  of the path `t ↦ exp (t • X)`, the unique continuous one because `proj` is a covering map
  (`eq_oneParameter`); it is a continuous one-parameter subgroup over `exp (t • X)`
  (`continuous_oneParameter`, `oneParameter_zero`, `oneParameter_add`, `proj_oneParameter`), and
  `t ↦ weil (oneParameter X t) f` has derivative `oscillatorDeriv X f` at `0`
  (`hasDerivAt_weil_oneParameter`): the oscillator operators are the derived representation.
- On Schwartz space, weakly (against continuous linear functionals `lam`):
  `contDiff_weilSchwartz_comp` and `hasDerivAt_weilSchwartz_oneParameter`, by factoring `lam` through
  the Weyl algebra and `L²` (`exists_factor_through_toLp`).
- `Intertwines.exists_generator_mem_weylAlgebra`: if `s t` is a continuous one-parameter group of
  linear maps preserving the standard symplectic form and `S t` a weakly continuous one-parameter
  group of intertwiners along `s t`, then `S` has a weak infinitesimal generator in the Weyl algebra:
  `s t = exp (t • X)` with `X ∈ sp` (one-parameter subgroups of matrices), `S t` is a scalar
  `c t` times `weilSchwartz (oneParameter X t)` (Schur), `c` is a continuous character, hence an
  exponential, and the generator is `oscillatorDeriv X + c'(0)`.

That the smooth vectors of `weil` are exactly the Schwartz functions, and the Lie algebra
homomorphism property of `oscillatorDeriv`, are not proved.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean`,
lines 294–446 (section `Metaplectic`: `omS_dRho`, `toLp_dRho_omS`, `contDiff_toLp_omS`,
`hasDerivAt_toLp_omS`, `metaplectic_schwartz_smooth`); `src/Development/WeilBound/ThetaLifts/CartanFactorisation/EqOfInner.lean`,
lines 212–319 (`exists_lift`, `lie`); `src/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOrb.lean` (whole: `orb`, `dm`,
`hasFDerivAt_orb`, `smooth_of`); `src/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MpFOne.lean`, lines 54–117 (`exp_mem_sp`, `onePar_of`);
`src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro.lean`
(whole). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- The section `Metaplectic` of the source is stated for an abstract quadruple `(G, pr, om, omS)` with
  the hypotheses `h3 : om g ∘ rho w = rho (pr g w) ∘ om g`, `h4 : om g (f ∈ L²) = omS g f`; here it is
  stated for `RealMetaplecticGroup l`, the hypotheses being `weil_schrodingerL2` and `weil_toLp`.
  `metaplectic_schwartz_smooth` is split into `contDiff_weilSchwartz_comp` and
  `hasDerivAt_weilSchwartz_oneParameter`; its first part is `weilSchwartz_schrodingerDeriv` of
  `Defs`.
- `exists_lift` and `lie` took the source's existence statement `RealMetaplecticRepresentation` as a
  hypothesis `hP`; they are stated without it, on the concrete group (`Internal.exists_lift` and
  `Intertwines.exists_generator_mem_weylAlgebra`, whose hypothesis on `s` is stated with
  `stdSymplecticForm`).
- `smooth_of (hT : TopG l) (hN : NearOne l) (hD : SecDer l) : Smooth l` → `contDiff_weil_comp`;
  `onePar_of … : OnePar l` → the definition `oneParameter` and its five theorems; the uniqueness
  `eq_oneParameter` is new.
- `exp_mem_sp` → `exp_mem_symplecticGroup`; `mem_sp_of_exp_mem_symplecticGroup` keeps its name.
- `MD/RealMetaplecticRepresentationHolds.lean` (the assembly) and the existence statement are not
  taken.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Real.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- theorem `Langlands.Theta.RealMetaplecticGroup.contDiff_weil_comp`
- theorem `Langlands.Theta.Real.exp_mem_symplecticGroup`
- theorem `Langlands.Theta.Real.mem_sp_of_exp_mem_symplecticGroup`
- def `Langlands.Theta.RealMetaplecticGroup.oneParameter`
- theorem `Langlands.Theta.RealMetaplecticGroup.continuous_oneParameter`
- theorem `Langlands.Theta.RealMetaplecticGroup.oneParameter_zero`
- theorem `Langlands.Theta.RealMetaplecticGroup.proj_oneParameter`
- theorem `Langlands.Theta.RealMetaplecticGroup.eq_oneParameter`
- theorem `Langlands.Theta.RealMetaplecticGroup.oneParameter_add`
- theorem `Langlands.Theta.RealMetaplecticGroup.hasDerivAt_weil_oneParameter`
- theorem `Langlands.Theta.RealMetaplecticGroup.contDiff_weilSchwartz_comp`
- theorem `Langlands.Theta.RealMetaplecticGroup.hasDerivAt_weilSchwartz_oneParameter`
- theorem `Langlands.Theta.Real.Intertwines.exists_generator_mem_weylAlgebra`

## Dependencies

`Langlands.Theta.Real.Metaplectic.Covering`; Mathlib (`Topology.Homotopy.Lifting`,
`Analysis.Convex.Contractible`).
