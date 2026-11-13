# Proof of Lemma Q: the Galois action on the simple roots

Author: Worker 2 (statement module and helper `RadicalGaloisInnerTransport` by Worker 5268).

This module proves the statement
`Langlands.Global.AdelicGaloisUnit.SplitBorelGaloisRootActionStatement` from the module
`Langlands.Global.AdelicGaloisRootAction`. The theorem is
`splitBorelGaloisRootAction : SplitBorelGaloisRootActionStatement.{u}`.

## Mathematical content

Let `G` be connected reductive over `F`, `L/F` finite Galois, `T₀ ⊂ G` a maximal `F`-torus
that splits over `L`, `i = i₀_L`, and `ν` a generic cocharacter of `T₀_L`. Let `Δ` be the
simple roots of `ν`. For each `σ ∈ Gal(L/F)` the proof constructs Tits' `*`-action
`σ* = w_σ ∘ σ`, where `w_σ` is the Weyl element that moves the Galois-translated chamber back
to the chamber of `ν` (Tits 1966, §2.3, printed p. 39). The proof then checks the five
clauses of `IsGaloisRootAction`.

The implemented route differs from the "intended proof" sketched in the statement's
Markdown in one point. The action laws are **not** proved by Bruhat-decomposition rigidity of
standard parabolics. They come from the published fact that a Weyl element preserving the
positive roots of a generic cocharacter is trivial (`hasTrivialPositiveRootStabilizer`).

## Positive-root-preserving lattice automorphisms

Section `RootPreserving`, namespace `Langlands.GroupScheme`. Here `T` is a split torus over a
field `k`, `i : T → G`, and `ν` is a cocharacter.

* `PreservesPositiveRoots i ν f` (internal Prop-valued `def`): the linear automorphism `f` of
  `X*(T)` satisfies `f χ ∈ Φ ↔ χ ∈ Φ` for all characters, where `Φ = relativeRoots i`, and
  `0 < ⟨f α, ν⟩ ↔ 0 < ⟨α, ν⟩` for every root `α`.
* `PreservesPositiveRoots.symm` and `.trans`: the property is stable under inverse and
  composition.
* `PreservesPositiveRoots.mem_positiveRelativeRoots_iff`: such an `f` preserves the positive
  roots (both directions).
* `PreservesPositiveRoots.mem_simpleRelativeRoots_iff`: such an `f` preserves the simple
  roots. A simple root is a positive root that is not a sum of two positive roots. This uses
  `f` for one direction and `f.symm` for the other, since `f` is additive.
* `pos_iff_of_dominant`: assume `Φ = -Φ`, `ν` is generic, and `ν'` is generic and pairs
  nonnegatively with every positive root of `ν`. Then `ν` and `ν'` give every root the same
  sign. If `⟨β, ν⟩ > 0`, dominance gives `⟨β, ν'⟩ ≥ 0` and genericity excludes `0`. If
  `⟨β, ν⟩ < 0`, then `-β` is positive, so `⟨β, ν'⟩ ≤ 0`.
* `weylAction_apply_eq_self_of_preserves`: let `n` be a normalizing point. If its Weyl action
  `weylAction i n` preserves the positive roots of `ν`, it is the identity. The image of `n`
  in `relativeWeylGroup i` satisfies the hypothesis of `HasTrivialPositiveRootStabilizer i ν`,
  via `relativeWeylCharacterAction_mk`. Hence that image is `1`, and so is its action on
  characters.

## Galois lemmas for the base-changed torus

Section `Galois`, namespace `Langlands.GroupScheme`. Here `T₀ → G` is defined over `F`, and
the objects carry the subscript `L`.

* `latticePairing_characterAut_galois_cocharacterAut_galois`: let `e` be a torus automorphism.
  Applying `σ` and then `e` to a character and to a cocharacter preserves their pairing. This
  combines `latticePairing_characterAut_cocharacterAut` and
  `latticePairing_galoisRepresentation`.
* `exists_galois_weylAction`: for a normalizing point `n` of `i₀_L` there is a normalizing
  point `n'` with `σ(w_n ψ) = w_{n'}(σ ψ)` for all characters `ψ`. Here `n'` is the descent
  transport of `n` (`IsNormalizingPoint.exists_descentTransport`). The identity follows from
  `characterAut_descentTransport` and `weylAction_eq`.
* `range_radicalGaloisHom_eq_parabolic`: let `p` represent the dynamic parabolic `P(ζ)` of a
  cocharacter `ζ` of `T₀_L`. Then the canonical Galois translate `radicalGaloisHom p σ`
  represents `P(σ ζ)`. The proof unfolds `radicalGaloisHom` and rewrites with
  `SubgroupFunctor.descentTransport_range`,
  `Dynamic.parabolic_transportCocharacter_eq_descentTransport` and
  `cocharacterLattice.groupHom_transport_comp`.

## The core theorem

`exists_isGaloisRootAction_of_galois` (namespace `Langlands.Global.AdelicGaloisUnit`) is
stated for an arbitrary monomorphism `i : T₀_L → G_L` and has these hypotheses:

* `G_L` is connected reductive.
* `T₀_L` is split.
* `i` is a maximal split torus.
* `ν` is generic.
* Three Galois hypotheses:
  * `hgroot`: `σ` preserves the roots of `i`.
  * `hgweyl`: Galois conjugates of Weyl actions are Weyl actions.
  * `hgpar`: the Galois translate of a represented `P(ζ)` is `P(σ ζ)`.

It concludes `∃ m τ, IsGaloisRootAction F L G T₀ i ν m τ`. It is separate from the main
theorem only for elaboration reasons: rewriting directly with terms
`(GroupScheme.baseChange _).map i₀` is fragile. The proof:

1. **Published inputs.** `relativeRootSystem`, `relativeRootNegation`,
   `hasTrivialPositiveRootStabilizer` and `standardCocharacter`, all for `i` over `L`.
2. **Chamber moves.** For each `σ`, `HasRelativeRootSystem.exists_normalizerPoint_dominant`
   gives a normalizing point `n σ`. The cocharacter `n σ · (σ ν)` pairs nonnegatively with
   every positive root of `ν`. The points are chosen with `choose`.
3. **Root maps.** `A σ := (galoisEquiv σ).trans (weylAction i (n σ))`, so
   `A σ χ = characterAut (normalizingAut i (n σ)) (σ χ)` holds by `rfl`. This is
   `galoisRootMap τ σ` for `τ σ := normalizingAut i (n σ)`. By the pairing lemma,
   `⟨A σ χ, n σ · σ ζ⟩ = ⟨χ, ζ⟩`.
4. **`A σ` preserves the positive roots.** It preserves `Φ` by `weylAction_mem_roots_iff`
   and `hgroot`. Through the pairing identity, `n σ · σ ν` is generic. `pos_iff_of_dominant`
   applied to `ν' = n σ · σ ν`, followed by the pairing identity, gives the sign condition.
5. **Identity law.** `A 1 = weylAction i (n 1)`, since `σ = 1` acts trivially (`map_one`).
   This Weyl action preserves the positive roots, so it is the identity
   (`weylAction_apply_eq_self_of_preserves`).
6. **Composition law.** `hgweyl` applied to `n σ'` gives `n'` with
   `A σ ∘ A σ' = w_{n σ · n'} ∘ (σσ')`. Hence
   `w_{n σ · n' · (n (σσ'))⁻¹} = (A σ ∘ A σ') ∘ (A (σσ'))⁻¹`. This composite preserves the
   positive roots (`symm`, `trans`), so it is the identity, and `A (σσ') = A σ ∘ A σ'` on all
   characters.
7. **Parabolics.** Let `J ⊆ Δ`, and let `ζ` be a standard cocharacter for `J`
   (`standardCocharacter`), so `P_J = P(ζ)`. `A σ` maps `J` into `Δ`. By the pairing identity,
   `n σ · σ ζ` is a standard cocharacter for `A σ '' J`: it vanishes on `A σ '' J` and is
   positive on the other simple roots, because `(A σ)⁻¹` also preserves `Δ`. So
   `P_{A σ '' J} = P(n σ · σ ζ)`. By `hgpar`, the Galois translate of `P_J` is `P(σ ζ)`.
   `P_{A σ '' J}` followed by conjugation by `(n σ)⁻¹` represents
   `P((σ ζ ≫ i) ≫ int(n σ) ≫ int((n σ)⁻¹)) = P(σ ζ ≫ i)`, via
   `range_comp_iso_eq_parabolic`, `groupHom_cocharacterAut_comp` and `innerIso_mul_hom`.
8. **Assembly.** Take `m σ := (n σ)⁻¹` and `τ σ := normalizingAut i (n σ)`. Then
   `IsNormalizingPoint i (m σ)⁻¹ (τ σ)` is `isNormalizingPoint_normalizingAut` after
   `inv_inv`. Clause 2 is step 4 with `mem_simpleRelativeRoots_iff`, clause 3 is step 7,
   clause 4 is step 5 and clause 5 is step 6.

## The main theorem

`splitBorelGaloisRootAction` introduces the data of the statement and derives the following:

* `IsConnectedReductive G_L` by `IsConnectedReductive.baseChange_of_algebraicExtension`;
* that `i₀_L` is a maximal torus, by `maximalTorusBaseChange`;
* that it is a maximal split torus, by `IsMaximalTorus.isMaximalSplitTorus` and the
  splitting of `T₀_L`.

It then applies the core theorem with `i = (GroupScheme.baseChange (algebraBaseMap F L)).map
i₀`. The three Galois hypotheses are supplied by `mem_roots_galois_iff`,
`exists_galois_weylAction` and `range_radicalGaloisHom_eq_parabolic`. The theorem uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`.
