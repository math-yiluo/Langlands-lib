# Proof of the comparison of `𝔞_P` and `𝔞_P^*` with the relative root data

Module `Langlands.Global.ArthurParabolicSpacesProof`, namespace
`Langlands.Global.ArthurParabolicSpaces`.

`parabolicSpacesComparison` proves `ParabolicSpacesComparisonStatement.{u}`
([paired statement](ArthurParabolicSpacesStatement.md)). Take a field `k`, a connected reductive
group `G`, a maximal split torus `i : T ⟶ G`, a generic cocharacter `ν`, integral reflection data
`D` and a set `S` of simple relative roots. For the standard parabolic representative
`P_S = Standard.parabolicScheme i ν S`, the theorem proves:

1. restriction `restrictToTorus k i ν S : X(P_S) ⊗ ℝ → X(T) ⊗ ℝ` is injective;
2. its range is `corootAnnihilator i D S`;
3. the transpose `toCharacterDual k i ν S : V T → Hom(X(P_S), ℝ)` is surjective;
4. the kernel of the transpose is `Submodule.span ℝ (D.realCorootsOf S)`;
5. the transpose restricted to `rootAnnihilator T S` is bijective.

## Source

J. Arthur, *An introduction to the trace formula* (2005), in the volume registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: §5, (5.1), p.24, and the description
`𝔞_P = {H ∈ 𝔞_0 : α(H) = 0, α ∈ Δ_0^P}` on p.26. Arthur works over a number field. The statement
and this proof work over an arbitrary field. The Lean argument below does not follow Arthur's text.
It is assembled from results already proved in the Library.

## Inputs

- `Langlands.GroupScheme.standardCocharacter` (`StandardCocharacterStatement`): `S` has a standard
  cocharacter `ζ`. For it, `standardParabolic i ν S` and `standardLevi i ν S` equal the dynamic
  parabolic and the dynamic centralizer of `ζ` composed with `i`.
- `Langlands.GroupScheme.Dynamic.parabolicCharacterEquiv`: restriction to the dynamic centralizer
  is an isomorphism from the rational characters of a closed represented dynamic parabolic onto
  those of the centralizer.
- `Langlands.GroupScheme.standardLeviCharacterAnnihilator`
  (`StandardLeviCharacterAnnihilatorStatement`, Renard V.3.13): restriction of real rational
  characters from a represented standard Levi to `T` has range `corootAnnihilator i D S`.
- `Langlands.GroupScheme.standardLeviCentralDirections`,
  `Langlands.GroupScheme.splitComponentStatement` and
  `Langlands.GroupScheme.renardLeviCentralDecomposition`. The first says the standard Levi is
  connected reductive and that its split component `A` maps to `T` compatibly with the
  inclusions. The second gives a split component. The third, applied to the identity of the
  Levi, says that restriction of real rational characters from the Levi to `A` is bijective.
- `Langlands.GroupScheme.standardLeviRealDecomposition` (`StandardLeviRealDecompositionStatement`,
  Renard V.3.13 in corrected form) for `J = K = S`. It gives the complements
  `corootAnnihilator i D S ⊕ span(1 ⊗ S) = X(T) ⊗ ℝ` and
  `rootAnnihilator T S ⊕ span(coroots of S) = V T`.
- `Langlands.GroupScheme.RealTorusSpace.isPerfPair_of_isSplitTorus`: the real pairing of `X(T) ⊗ ℝ`
  with `V T` is perfect. `rootAnnihilator_eq_cocharacterAnnihilator` describes the root
  annihilator by this pairing.
- From `Langlands.Global.ArthurParabolicSpaces`: `torusToParabolic_comp`,
  `toCharacterDual_apply` and the transpose identity `realParameterPairing_toCharacterDual`.

## Lean proof

**Factorization through the Levi.** Choose a standard cocharacter `ζ` for `S`. The closed
representatives `Standard.parabolicHom i ν S` and `Standard.leviHom i ν S` then represent the
dynamic parabolic and the dynamic centralizer of `ζ` composed with `i`. These inclusions are monomorphisms. Cancelling
the inclusion of `P_S` shows that the dynamic `centralizerToParabolic` equals
`Standard.leviToParabolic i ν S`. Let `tL : T ⟶ M_S` be the factorization of `i` through the
Levi representative. Cancelling the inclusion of `P_S` again gives
`torusToParabolic k i ν S = tL ≫ leviToParabolic`. Since `characterRestrict_comp` reverses
composites, `restrictToTorus` is the composite of real restriction along `leviToParabolic`
followed by real restriction along `tL`.

**Restriction from `P_S` to `M_S` is bijective.** It is the real base change of the additive
isomorphism `parabolicCharacterEquiv`, so it is a linear equivalence.

**Items 1 and 2.** By `standardLeviCharacterAnnihilator`, real restriction along `tL` has range
`corootAnnihilator i D S`. Precomposing with a surjection does not change the range, which gives
item 2. For injectivity along `tL`, take a split component `a : A ⟶ M_S` and the map `f : A ⟶ T`
from `standardLeviCentralDirections`. Cancelling the Levi inclusion gives `f ≫ tL = a`.
Restriction along `a` is restriction along `tL` followed by restriction along `f`. Restriction
along `a` is injective by `renardLeviCentralDecomposition`, so restriction along `tL` is
injective. Composed with the bijection above, this gives item 1.

**Item 3.** Let `φ : Hom(X(P_S), ℝ)`. Since `restrictToTorus` is injective, it has a linear left
inverse `g`. The linear form `m ↦ ⟨m, φ⟩` (`realParameterPairing`) composed with `g` is a linear
form on `X(T) ⊗ ℝ`. By perfectness it equals `⟨·, v⟩` for some `v ∈ V T`. Evaluating
`toCharacterDual v` at a character `χ` gives `⟨restrictToTorus (1 ⊗ χ), v⟩ = φ(χ)`.

**Items 4 and 5.** These use two general lemmas proved in the module:

- `ker_eq_of_isCompl_of_disjoint`: if `C ≤ ker f`, `W` and `C` are complements, and `W` meets
  `ker f` trivially, then `ker f = C`;
- `bijective_domRestrict_of_isCompl`: a surjective linear map restricts to a bijection on any
  complement of its kernel.

Each real coroot of `S` lies in the kernel of the transpose: its pairing with
`restrictToTorus (1 ⊗ χ)` vanishes because that vector lies in `corootAnnihilator i D S`
(item 2). Next let `v ∈ rootAnnihilator T S` lie in the kernel, and split any `y ∈ X(T) ⊗ ℝ` as
`y₁ + y₂` with `y₁` in the coroot annihilator and `y₂` in the span of `1 ⊗ S`. Then `⟨y₁, v⟩ = 0`
by item 2 and the transpose identity, and `⟨y₂, v⟩ = 0` because `v` annihilates `S`. By
perfectness `v = 0`. With the complement `rootAnnihilator T S ⊕ span(coroots of S)`, the first
lemma gives item 4. Item 4 together with that complement, item 3 and the second lemma gives
item 5.

## Provenance

Source: Arthur 2005, (5.1) and p.26, for standard parabolic subgroups, as formulated in the paired
statement. The proof is derived from the published Library results listed under Inputs.
