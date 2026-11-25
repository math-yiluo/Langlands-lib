# Proof: centrality of homomorphisms from groups of multiplicative type spreads from nilpotent thickenings

`Langlands.GroupScheme.multiplicativeTypeInfinitesimalCentrality` proves
`Langlands.GroupScheme.MultiplicativeTypeInfinitesimalCentralityStatement.{u}`
([statement](MultiplicativeTypeInfinitesimalCentralityStatement.md)) in every universe `u`.
The data are a closed immersion `i : S₀ ⟶ S` such that every point of `S` lies in an affine
open `U` with `i.ker.ideal U` nilpotent, group schemes `G, H` over `S` with `G` of
multiplicative type, and a homomorphism `u : G ⟶ H` whose base change along `i` is central.
The goal is `IsCentral u`.

The statement is SGA 3, IX, Corollaire 3.9. SGA 3 derives it from Proposition 3.8 (rigidity
of actions of groups of multiplicative type), applied to the conjugation action of `G` on
`H`. The Lean proof uses the same idea, but applies the rigidity only on affine open charts of
`H`, after reducing to an affine base. The hypothesis `LocallyOfFinitePresentation H.X.hom`
of the statement is not used.

## Steps

1. **Affine base.** The affine case is
   `NilpotentConjugation.isCentral_of_isMultiplicativeType`
   ([`Torus.NilpotentConjugationAction`](NilpotentConjugationAction.md)). For a commutative
   ring `R`, a nilpotent ideal `I`, group schemes `G, H` over `Spec R` with `G` of
   multiplicative type and `H` arbitrary, and a homomorphism `G ⟶ H` whose base change along
   `Spec (R ⧸ I) ⟶ Spec R` is central, the homomorphism is central. That module proves it
   with the conjugation action on affine charts of `H`, as summarised there.

2. **The ideal on an affine open.** `MultiplicativeTypeInfinitesimalCentrality.exists_quotient_lift`:
   for every affine open `U` of `S`, the composite
   `Spec (Γ(S, U) ⧸ i.ker.ideal U) ⟶ Spec Γ(S, U) ⟶ S` factors through `i`. Because `i` is a
   closed immersion, `Γ(S, U) ⟶ Γ(S₀, i⁻¹U)` is surjective (`Scheme.Hom.app_surjective`) with
   kernel `i.ker.ideal U` (`Scheme.Hom.ker_apply`). So `Γ(S, U) ⧸ i.ker.ideal U` is isomorphic to
   `Γ(S₀, i⁻¹U)`. The factorisation is the spectrum of this isomorphism followed by the open
   immersion of the affine open `i⁻¹U` of `S₀`. The commuting square is
   Mathlib's `IsAffineOpen.SpecMap_appLE_fromSpec`.

3. **Globalization.** `MultiplicativeTypeInfinitesimalCentrality.isCentral_of_locallyNilpotent`
   chooses, for every point `x` of `S`, an affine open `U x ∋ x` on which the ideal is
   nilpotent. The open immersions `Spec Γ(S, U x) ⟶ S` are flat and jointly surjective, so
   they form a cover for the precoverage of flat morphisms (`Scheme.Cover.mkOfCovers`). By the
   Library `IsCentral.of_flatCover`
   ([`Torus.MultiplicativeTypeAffineInfinitesimalCentrality`](MultiplicativeTypeAffineInfinitesimalCentrality.md)),
   it suffices to prove centrality of the base change of `u` to each `Spec Γ(S, U x)`. That
   base change has a multiplicative-type source (`IsMultiplicativeType.baseChange`). By step 2
   and the Library `isCentral_baseChange_of_commSq`, its further base change to
   `Spec (Γ(S, U x) ⧸ i.ker.ideal (U x))` is a base change of the central homomorphism over
   `S₀`, so it is central. Step 1 applies with the nilpotent ideal `i.ker.ideal (U x)`.

4. **Conclusion.** `multiplicativeTypeInfinitesimalCentrality` introduces the data of the
   statement and applies step 3.

## Scope

The theorem proves the statement exactly, for every closed immersion with locally
nilpotent ideal and all group schemes and homomorphisms as there, with no additional
hypotheses. The finite-presentation hypothesis on `H` is not needed.
