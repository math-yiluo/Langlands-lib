# The étale locus of a closed subscheme of an étale scheme, with a given level

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteEtaleLevel`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal`. This module supports the proof of
Step 2a of Murre's induction (`MurreCompleteLocalStepStatement`, Bourbaki exp. 294, Case I,
Step 2a).

The Library (`EtaleLocusBasic`, `EtaleLocusLevel`, `EtaleLocusStd`, `EtaleLocusGen`, namespace
`EtaleLocus`) studies the étale locus of `ξ ∈ F(Spec (R'/𝔍))`, where `R'` is étale over `R`. At
a point `w` it uses a *level*: a representing scheme of `F` over `Spec O_w`, where
`O_w = R'_{P_w}` (`Level F (algebraMap R' (Ow 𝔍 w))`). The Library builds levels from the
hypothesis that `F` is representable over every local scheme of `Spec R`. In Step 2a that
hypothesis is unavailable at the closed point of `Spec R`. So the two Library arguments needed
here are restated with the level as an explicit argument. Their proofs are the Library proofs
with the call to `nonempty_level_localization` removed.

* `nonempty_level_of_range`: let `j : U ⟶ Spec R` be an open immersion and suppose `F` is
  representable over `U` (`UnramifiedRepresentable (baseChange j F)`). If the image of
  `Spec D ⟶ Spec R` lies in `U`, there is a level `R' → D`. The morphism factors through `U`
  (`IsOpenImmersion.lift`). The representing scheme is the pullback, as in the Library's
  `nonempty_level_localization`
  (`LocalToGlobal.unramifiedRepresentable_baseChange`, `baseChangeCompIso`,
  `unramifiedRepresentable_of_iso`).
* `infinitesimallyEtaleAt_of_le_of_level`: the Library's `infinitesimallyEtaleAt_of_le`
  (generization), given a level at `w`. If `ξ` is infinitesimally étale at `w` and `y ≤ w`, then
  it is infinitesimally étale at `y`. Proof as in the Library: `van_of_killAt` shows that `𝔍`
  vanishes in the stalk `𝒪_{X,x}` of the level at the point `x` given by `w`. The point given by
  `y` is a generization of `x` (`left_eq_of_elemEquiv_eq` for `genDatum`), so `𝔍` vanishes in
  its stalk too (`structMap_stalkSpecializes`). Then `killAt_of_van` and
  `killAt_of_localization` give the lifting condition at `y`.
* `infinitesimallyEtaleAt_of_killAt_surjective`: let a level at `w` be given. Suppose the
  lifting condition `KillAt ξ w A (δ' ∘ (R' → O_w))` holds for every *surjection* `δ'` from
  `O_w` onto a local artinian ring `A`. Then `ξ` is infinitesimally étale at `w`. This is the
  Library's `van_of_killAt` argument, which only uses `A = 𝒪_{X,x}/m^(N+1)` and
  `δ' = χ ∘ θ`. The extra step proves that this `δ'` is surjective: `ψ : 𝒪_{X,x} → O_w/𝔍O_w`
  is surjective with kernel contained in `𝔍 𝒪_{X,x}` (`ker_ψ_le`), which lies in the maximal
  ideal. So `θ` is surjective modulo the nilpotent image of `𝔍` in `𝒪_{X,x}/m^(N+1)`
  (`surjective_of_isNilpotent_map`). With `θ(𝔍) ⊆ ⋂ m^(N+1) = 0` (Krull), `killAt_of_van` and
  `killAt_of_localization` conclude as in the Library's `infinitesimallyEtaleAt_of_noLargerLift`.
