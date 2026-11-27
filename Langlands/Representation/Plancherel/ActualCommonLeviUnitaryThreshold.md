# Explicit convergence thresholds for unitarizable common-Levi data

Lean module: `Langlands.Representation.Plancherel.ActualCommonLeviUnitaryThreshold`,
namespace `Langlands.Plancherel.ActualCommonLeviV3`.

## Purpose and status

For a common Levi cocharacter `χ` of `G` and two cocharacters `ψ`, `ψ'` with the same
centralizer as `χ`, `pairFullDomainRegion χ K hK ψ hψ ψ' A` is the set of unramified parameters
`z` of the centralizer scheme of `χ` at which the standard intertwining integral from `P(ψ)` to
`P(ψ')` has full domain (`StandardIntertwining.domain … = ⊤`): for every vector `f` of the source
normalized induction `I^G_{P(ψ)}(A ⊗ z)` and every `g ∈ G(F)`, the smooth-dual scalar integrals
of `f` at `g` converge absolutely and are represented by a vector of the carrier of `A ⊗ z`.
The module proves that for an admissible
unitarizable `A` this set contains an explicit strict root region: a cone in the real parts,
given by finitely many strict inequalities with one threshold `R`. All results are proved; no
`sorry`, no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Data

`F` is a nonarchimedean local field (universe `u`) and `G` a connected reductive group over `F`
(`hG`). `χ`, `ψ`, `ψ'` are cocharacters of `G` with `hψ : Z_G(ψ) = Z_G(χ)` and
`hψ' : Z_G(ψ') = Z_G(χ)`. `K` is a compact open subgroup of `G(F)` (`hK`) with
`hψK : G(F) = P(ψ)(F) K`. `A` is a smooth representation of the literal Levi `levi χ` on a
complex space in universe `uV`.

## Results

**Theorem `exists_threshold_mem_pairFullDomainRegion`.** Take root presentations `r`, `r'`
(`ParabolicRootPresentation`) of two parabolics `P`, `P'` with the same Levi model `M`
(`hLevi : l ≫ p = l' ≫ p'`) and one split component `a`. Assume geometric unipotent radicals
`n`, `n'`, a parabolic `Q` representing the dynamic parabolic of `−λ_{r'}` with unipotent
radical `v`, and realizations `s : Realizes χ ψ p l n`, `s' : Realizes χ ψ' p' l' n'`. Let the
relative Weyl group be finite. If `A` is admissible and unitarizable, there is `R : ℝ` such that
every `z` whose presentation character `characterComparison χ ψ r s z` lies in
`parabolicPointUnramifiedIntertwiningRegion r B n q v R` is in
`pairFullDomainRegion χ K hK ψ hψ ψ' A`. Here `B` is the Weyl-induced form
`weylInducedCharacterForm` of the presentation `r`.

Proof as implemented:

1. Point data. `presentationPointData` (for `ψ`) gives the semidirect decomposition, closedness
   and the factorization `G(F) = P(F) K`. The decomposition and closed radical for `ψ'` come from
   `commonDecomposition` and `radical_isClosed`, rewritten along `s'`.
2. The representation. Transport `A` to the presentation's Levi points
   (`presentationRepresentation`). Admissibility transfers by `representationOfEq_isAdmissible'`
   and unitarizability by composition with `subgroupHomeomorphOfEq`.
3. Decay inputs. `parabolicCharacterDecayInput_of_statements` (with the published
   `relativeRootSystem` and `centralSplitTorusCharacter`) gives a matrix representation
   `ρ` (with its hypothesis `hρ`) and character decay. From it `parabolicOppositeConeDecay_of_characterDecay` gives cone
   decay on the region `C = parabolicPointUnramifiedIntertwiningRegion r B n q v`, and
   `parabolicSquaredModulusInput_of_statements` gives the squared-modulus input.
4. Coefficient growth. Matrix coefficients of an admissible unitarizable representation are
   bounded (`IsUnitarizable.smoothCoefficient_bounded`). This is `HasCommonCoefficientGrowth`
   with exponent `0`.
5. Conclusion. `exists_region_convergence_domination_of_coneDecay` gives the threshold `R` and
   convergence on the region of threshold `R`. `mem_pairFullDomainRegion` turns this into
   membership in `pairFullDomainRegion`.

**Theorem `characterComparison_parabolicData`.** For `d : ParabolicData χ ψ T a` (module
`DynamicCommonLeviPresentations`), the presentation character comparison
`characterComparison χ ψ d.r d.realizes` is the transport
`parabolicLeviUnramifiedCharactersHomeomorph d.r` along the presentation's own Levi point
identification. Proof: both are restrictions along identifications of the same Levi points,
which agree by `d.levi_comp` (`parameterPointComparison_coe`,
`parabolicLeviPointHomeomorph_apply_coe`).

**Theorem `exists_threshold_mem_pairFullDomainRegion_of_data`.** Take presentations
`d₁ : ParabolicData χ ψ T a` and `d₂ : ParabolicData χ ψ' T a` on one split component `a` of the
centralizer scheme of `χ`, and opposite data `o` for `−λ_{d₂}`. If `A` is admissible and
unitarizable, there is `R` such that every unramified parameter `z` of the centralizer scheme
in `parabolicUnramifiedIntertwiningRegion d₁.r B d₁.n o.q o.v R` lies in
`pairFullDomainRegion χ K hK ψ hψ ψ' A`. Here `B` is the Weyl-induced form of `d₁.r`. Proof:
`exists_threshold_mem_pairFullDomainRegion` for `d₁.r`, `d₂.r`. The region condition is read
on `z` by `characterComparison_parabolicData` (`parabolicUnramifiedIntertwiningRegion` is the
preimage of the point region under `parabolicLeviUnramifiedCharactersHomeomorph`).

## Relation to the source

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, registered as
`waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`); PDF page = printed
page − 234.

Théorème IV.1.1 (printed p.278): for `π` of finite length there is `R` such that
`J_{P'|P}(π ⊗ χ)` is defined by convergent integrals whenever `⟨Re χ, α⟩ > R` for all
`α ∈ Σ(P) ∩ Σ(P̄')`. The theorems here are a variant with different hypotheses: `A` admissible
and unitarizable (so with bounded coefficients) instead of finite length. They give the same
kind of threshold region, read in the root presentation of the source parabolic.

## Imports

`ActualCommonLeviUnitaryContinuation`, `DynamicOppositeConjugationScalar`,
`DynamicCommonLeviContinuationAssembly`, `DynamicCommonLeviPresentationReduction`,
`ParabolicCharacterDecayProof`, `ActualCommonLeviV3Continuation`,
`Representation.Unitary.SmoothCoefficientBoundednessProof`, `Representation.Unitary.Restriction`,
`GroupScheme.Rational.RelativeRootSystemProof` and
`GroupScheme.Rational.CentralSplitTorusCharacterProof`.
