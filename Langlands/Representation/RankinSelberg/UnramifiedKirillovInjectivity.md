# Injectivity of the Kirillov map

Author: Worker 1797. Module
`Langlands.Representation.RankinSelberg.UnramifiedKirillovInjectivity`, namespace
`Langlands.RankinSelberg.UnramifiedUnitary`.

This helper module is an input to the proof of the unitary pole bound
`Langlands.RankinSelberg.UnramifiedUnitaryPoleFreeStatement`. That proof follows the
proof of Jacquet–Shalika, Euler products I, Proposition (1.3). The result proved
here is the injectivity half of the assertion in Jacquet–Shalika, *On Euler products
and the classification of automorphic representations I*, Amer. J. Math. 103 (1981),
§(1.1), printed p. 505 (literature id
`provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`).
That assertion says that for an irreducible generic `π`, the map `W ↦ W|_P` from the
Whittaker model to functions on the mirabolic group `P` is a bijection onto the
Kirillov space. The source gives no proof; it cites Gelfand–Kazhdan. The Lean proof
below is an internal route through the Library's derivative and Zelevinsky theory,
not the Gelfand–Kazhdan argument.

## Statements

Let `T : F.TopologicalData` be topological data for a p-adic field `F`, with the
topology `T.topology` on `F`. Let `ψ` be a unitary additive character and `n : ℕ`.
`P = mirabolic n F` is the last-row mirabolic subgroup of `GL_(n+1)(F)`.

- `kirillov_injective T ψ n π hπ hirr ℓ hℓ hmult v hv`. Here `π` is a representation
  of `GL_(n+1)(F)` on a complex vector space `V`, in an arbitrary universe, and it is
  smooth (`hπ`) and irreducible (`hirr`). `ℓ` is a standard Whittaker functional
  (`Whittaker.glFunctionals ψ n π`) with `ℓ ≠ 0`, and every such functional is a
  scalar multiple of `ℓ` (`hmult`). If `ℓ(π(p) v) = 0` for every `p ∈ P`, then
  `v = 0`.
- `kirillov_injective_saturated` is the same statement for a bundled smooth
  representation `SmoothRep.{0, uF, max uF uV}`. That carrier universe is the one in
  which the Library's Zelevinsky exhaustion theorem is stated. `kirillov_injective`
  reduces to it by `SmoothRep.universeLift`, using
  `SmoothRep.isIrreducible_universeLift_iff`. The functionals and the multiplicity
  hypothesis are moved along `ULift` by composition with `ULift.down` and `ULift.up`.

The hypotheses are those of a generic representation in the sense of the source:
nonzero Whittaker functional and uniqueness up to scalars. The multiplicity
hypothesis is assumed here and is not derived. Admissibility is not used.

## Auxiliary lemmas

- `mirabolicUpperUnipotent_isLimitOfCompactSubgroups`: the upper unipotent subgroup
  `Mirabolic.upperUnipotent n F` of `P` is a union of compact subgroups. Every compact
  subset lies in one of them. The proof transports the Library's
  `upperUnipotent_isLimitOfCompactSubgroups` (for `GL_(n+1)`) along
  `Mirabolic.upperUnipotentContinuousEquiv`.
- `nontrivial_coinvariants_rankCast`: a rank cast `mirabolicRankCast T h` does not
  change whether the full upper `(U, θ)`-coinvariants are nonzero. Proof: `subst`.
- `hasNonzeroDerivative_top_iff`: a smooth `P`-representation `B` has a nonzero
  derivative of the top order `n + 1` iff its coinvariants
  `Coinvariants B (Mirabolic.upperUnipotent n F) θ` are nontrivial. Here `θ` is the
  standard character `TopLocalization.mirabolicUpperCharacter ψ.complex n`. Proof: by
  `mirabolicDerivativeOfOrder_top`, the top derivative is the rank-cast of
  `mirabolicDerivative T ψ 0 n`. By the natural isomorphism
  `TopLocalization.mirabolicLocalizationIso`, that is the coinvariant functor. Rank
  casts preserve nontriviality (`RestrictionBridge.nontrivial_generalLinearRankCast_iff`
  and the previous lemma).
- `mem_mirabolicFunctionals_iff`: a linear form on `V` is a `(U, θ)`-functional for
  the restriction of `π` to `P` iff it is a standard Whittaker functional of `π`. This
  holds because `Mirabolic.upperUnipotentEquiv` identifies the two unipotent groups and
  `entrywiseCharacter_eq_standardCharacter` identifies the two characters.
- `character_isLocallyConstant`, `mirabolicUpperCharacter_isLocallyConstant`: a
  complex character with open kernel is locally constant. `θ` has open kernel, since
  it is the transport of the continuous standard character
  (`standardCharacterContinuous`, `isOpen_ker_of_continuous_complex_character`).
- `isInvariant_bot`: the trivial subgroup satisfies the invariance hypothesis of the
  localization functor.

## Proof of `kirillov_injective_saturated`

Let `A` be the restriction of `π` to `P`. Let `Y ⊆ A` be the kernel of the Kirillov
map, i.e. the vectors `w` with `ℓ(π(p) w) = 0` for all `p ∈ P`. `Y` is a
`P`-subrepresentation. Suppose `v ∈ Y` and `v ≠ 0`.

1. **Homogeneity of an ambient representation.**
   `Classification.multisegmentSocleExhaustion` embeds `π` into a Zelevinsky product
   `d.induced` of segment representations. The segments are precedence-ordered and
   socle-generic. By `Classification.precedenceOrdered_endpointSeparated` (with
   `cuspidalIntegralTwistFreeness`) and `Classification.segmentSocleProductHomogeneity`,
   the restriction `X` of `d.induced` to `P` is homogeneous
   (`isGeneralLinearHomogeneous_iff`). The embedding restricts to an injective
   `P`-map `A → X`.
2. **The level is the top order.** By `mem_mirabolicFunctionals_iff`, `ℓ` is a
   `(U, θ)`-functional on `A`. `Whittaker.functionalsLocalizationDualEquiv` turns it
   into a linear form on the coinvariants, and that form is nonzero because `ℓ ≠ 0`.
   So the coinvariants of `A` are nonzero. By `hasNonzeroDerivative_top_iff`, `A` has a
   nonzero derivative of order `n + 1`, hence `level A = n + 1` (`level_eq_iff`). Since
   `A` embeds in the homogeneous `X`, `LevelCalculus.level_eq_of_isHomogeneous` gives
   `level X = n + 1`.
3. **The kernel has nonzero coinvariants.** `Y` is nonzero and embeds in `X`. By
   `hasNonzeroDerivative_of_isHomogeneous`, every nonzero subrepresentation of a
   homogeneous representation of level `n + 1` has a nonzero derivative of order
   `n + 1`. By `hasNonzeroDerivative_top_iff`, `Y` has a nonzero coinvariant class
   `[w]`.
4. **Exactness.** The full upper unipotent group of `P` is a union of compact
   subgroups and `θ` is locally constant. So the coinvariant functor preserves
   injections of smooth representations (`Jacquet.Localization.map_injective_of_smooth`).
   The class of `w` in the coinvariants of `A` is therefore nonzero.
5. **Contradiction with multiplicity one.** Choose a linear form `g` on the
   coinvariants of `A` with `g([w]) ≠ 0`
   (`Module.forall_dual_apply_eq_zero_iff`). `functionalsLocalizationDualEquiv`
   turns `g` into a `(U, θ)`-functional `λ` on `A`, i.e. a standard Whittaker
   functional of `π`, with `λ(w) ≠ 0`. By `hmult`, `λ = c ℓ`. But `ℓ(w) = 0`, because
   `w ∈ Y` (take `p = 1`). So `λ(w) = 0`, a contradiction.

Hence `v = 0`.
