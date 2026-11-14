# Highly ramified stability of class pair gamma factors

Author: Worker 389.

This module transfers the two-factor stability of JPSS pair gamma factors
(`RankinSelberg.StableTwist.pairGammaStability`, module
`Langlands.Representation.RankinSelberg.StableTwist.JPSSStability`) from representations to
the class-level gamma factors `IsAutomorphicPairGammaFactor` used by the local Langlands
correspondence statements. It is a supporting step for the stable pair gamma comparison
under highly ramified twists. It introduces no definition and no axiom. Its main theorem
takes the twist exchange statement `RankinSelberg.PairGammaTwistExchangeStatement` as an
explicit hypothesis `hR1`, which it passes on to `pairGammaStability`.

The module declares three named local instances (`classStabilityTopology`,
`classStabilityGLTopology`, `classStabilityGLTopologicalGroup`) that install the canonical
topology of `K` and of `GL_n(K)`. They are local to the module and only make the class-level
relations elaborate; the names avoid clashes with other modules' local instances.

## Declarations

All declarations are in the namespace `Langlands.Automorphic.StableTwist`. `K` is a p-adic
field and `ψ` a nontrivial additive character of `K`.

- `selfDualHaar_val_eq K ψ ν ν'`: two self-dual Haar measures for `ψ`
  (`LocalFactor.PadicAbelian.SelfDualHaar`) have the same underlying measure.
- `exists_isAutomorphicPairGammaFactor K ψ hν π π'`: for a self-dual measure `ν` for `ψ` and
  classes `π`, `π'` of ranks `r + 1`, `t + 1` (`AutomorphicClass`), some rational function
  `G` satisfies `IsAutomorphicPairGammaFactor K ψ ν π π' G`.
- `classPairGammaStability hR1 K ψ A₁ A₂ B₁ B₂ ...`: let `A₁, A₂` be automorphic objects of
  rank `r + 1` and `B₁, B₂` of rank `t + 1`, all with `ψ`-generic representations, such that
  `A₁, A₂` have the same central character and so do `B₁, B₂` (`SameGLCentralCharacter`).
  There is `N : ℕ` such that for every quasi-character `χ` of multiplicative conductor at
  least `N`, all classes `π₁χ`, `π₂χ` with `IsCharacterTwist K χ [A₁] π₁χ` and
  `IsCharacterTwist K χ [A₂] π₂χ` (where `[A]` is `automorphicClassOf K A`), every self-dual
  measure `ν` for `ψ` and every `G`: if `G` is a class pair gamma factor of `(π₂χ, [B₂])`,
  then it is one of `(π₁χ, [B₁])`.

## Implemented proofs

**Uniqueness of the self-dual measure.** This is the uniqueness part of the Library's p-adic
Fourier duality, `LocalFactors.padicFourierDuality`, applied to `ψ`.

**Existence of class gamma factors.** The contragredient classes are smooth duals
(`isSmoothDual_iff_eq_contragredient`). The pair L-polynomials of `(π, π')` and of the
contragredient pair, and the pair epsilon factor of `(π, π')`, exist by
`Global.CuspidalPairFunctionalEquation.exists_isAutomorphicPairLPolynomial` and
`exists_isAutomorphicPairEpsilonFactor`; `automorphicPairGammaFactor` assembles them into a
gamma factor.

**Class-level stability.**

1. Choose a self-dual measure `ν₀` for `ψ` (`HighlyRamified.nonempty_selfDualHaar`) and get
   `N` from `pairGammaStability hR1` applied to the four representations.
2. Given `χ`, `π₁χ`, `π₂χ`, `ν` and `G`, replace `ν` by `ν₀` (uniqueness above). Unfold the
   twist relations: `π_iχ = [C_i]` for objects `C_i` with
   `twist(χ ∘ det)(A_i') ≅ C_i`, where `[A_i'] = [A_i]`; composing with the isomorphism
   `A_i ≅ A_i'` (`automorphicClassOf_eq_iff`, `Langlands.twistEquiv`) gives an isomorphism
   `g_i : twist(χ ∘ det)(A_i) ≅ C_i`.
3. `C_i` is `ψ`-generic: twists of generic representations are generic
   (`isGeneric_quasicharacter_twist_iff`) and genericity is invariant under isomorphism
   (`Whittaker.isGeneric_iff_of_equiv`).
4. For generic objects a class gamma factor is a symmetric p-adic gamma certificate of the
   representations (`IsAutomorphicPairGammaFactor.isPadicSymmetricGammaFactor_of_generic`,
   with the published comparison `genericLanglandsPairEpsilonFactorComparison`), and
   certificates transport along isomorphisms (`IsPadicSymmetricGammaFactor.congr_equiv`).
   So `G` is a certificate of `(twist(χ ∘ det)(A₂), B₂)`.
5. Take a class gamma factor `G₁` of `([C₁], [B₁])` (existence above); in the same way it is a
   certificate of `(twist(χ ∘ det)(A₁), B₁)`. The stability of step 1 gives `G₁ = G`, so `G`
   is a class gamma factor of `(π₁χ, [B₁])`.

## Sources and provenance

This is an internal derivation from Library results. The underlying stability is Jacquet and
Shalika, *A Lemma on Highly Ramified ε-Factors*, Math. Ann. 271 (1985), Proposition (4.1),
printed p.326 (`jacquet-shalika-1985-ramified-factors`), in the two-factor form used by
Henniart, *On the local Langlands conjecture for GL(n): the cyclic case*, Ann. of Math. 123
(1986), proof of Lemma 4.2, printed p.158 (`henniart-1986-cyclic`). The identification of
class gamma factors with JPSS gamma factors for generic representations is the Library's
`isPadicSymmetricGammaFactor_of_generic`.
