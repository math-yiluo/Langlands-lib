# Representability of relative effective divisors, with quasi-projective Hilbert-polynomial pieces

Author: Worker 22, for task `07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705).
The interface was agreed with Worker 5705, who uses the statement in the
Picard construction of that task.

## Statement

`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesStatement.{u}`
is a proposition with no proof asserted here.

**Data and hypotheses.** It quantifies over

- a noetherian commutative ring `A : Type u`, with `S = Spec (CommRingCat.of A)`;
- a scheme `X`, a morphism `f : X ⟶ S` and a module `𝓛X : X.Modules`.

It assumes

- `Flat f`;
- `Scheme.Modules.IsInvertible 𝓛X`;
- `Scheme.Modules.ClosedImmersionBySections 𝓛X f`: finitely many global
  sections of `𝓛X` define a closed immersion of `X` into a finite projective
  space over `A`.

The last two are the FLT-port definitions (`Langlands.AnthropicFLT.Definitions`)
that serve as the hypotheses of the published FLT Hilbert-scheme theorem
`AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections`.

**Conclusion.** There are a scheme `D`, a morphism `d : D ⟶ S` and a relative
effective divisor `W : RelativeEffectiveDivisor (pullback.snd f d)` on
`X ×_S D` over `D`, such that the following hold.

1. `LocallyOfFinitePresentation d` and `IsSeparated d`.
2. *Representability on all test schemes.* Let `T : Scheme.{u}` be a scheme
   and `s : T ⟶ S`. For a morphism `g : T ⟶ D` with `hg : g ≫ d = s`,
   write `g_X = pullback.map f s f d (𝟙 X) g (𝟙 _) _ _`. This is the morphism
   `X ×_S T ⟶ X ×_S D` induced by `g`. The pulled-back actual ideal
   `W.ideal.comap g_X` then satisfies the following.
   - For every such `g`, it is a relative effective Cartier ideal for the
     projection `pullback.snd f s : X ×_S T ⟶ T`.
   - For every relative effective Cartier ideal `I` on `X ×_S T` over `T`,
     there is exactly one `g : T ⟶ D` with `g ≫ d = s` and
     `W.ideal.comap g_X = I`.

   Together these give a bijection between the morphisms `T ⟶ D` over `S`
   and the relative effective divisors of `X ×_S T` over `T`, given by
   pulling back `W`. So `D`, with `W`, represents the functor of relative
   effective divisors on all `S`-schemes in universe `u`, including
   non-noetherian, non-quasi-compact and non-separated ones. Kleiman's
   `Div_{X/S}` is this functor restricted to locally noetherian `S`-schemes.
   The extension to all test schemes is derived below, in "Derivation for
   arbitrary test schemes"; the sources do not state it.
3. *Hilbert-polynomial pieces.* There is a family `U : Polynomial ℚ → D.Opens`
   of open subschemes. Its members are pairwise disjoint (`Pairwise (Disjoint on U)`)
   and cover `D` (`⨆ θ, U θ = ⊤`). For every `θ` the following hold.
   - `IsHQuasiProjective ((U θ).ι ≫ d)`: the open subscheme `U θ` has a
     quasi-compact immersion into some `ProjectiveSpace A n` over `S`.
   - Take an affine test: a ring `B : Type u`, `s : Spec B ⟶ S`, and
     `g : Spec B ⟶ D` with `hg : g ≫ d = s`, so that item 2 applies with
     `T = Spec B`. Take the classified ideal `I = W.ideal.comap g_X`, with
     closed subscheme `I.subscheme` and
     `ι = I.subschemeι`. Then `g` lands in `U θ` (`Set.range g.base ⊆ U θ`) if
     and only if the following holds. For every algebraically closed field
     `k : Type u` and every ring map `sk : B →+* k`, there is `n₀` such that for
     all `n ≥ n₀`,
     `Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s) (M^{⊗ n}) k sk = θ(n)`
     in `ℚ`. Here `M` is the pullback of `𝓛X` along
     `ι ≫ pullback.fst f s : I.subscheme ⟶ X`. The tensor power `M^{⊗ n}` is
     written, exactly as in the FLT theorem, as `Nat.rec` on `n` starting from
     the monoidal unit and tensoring with `M` on the right. In words, this is
     the dimension of the global sections of `M^{⊗ n}` on the geometric fibre
     of the divisor over `Spec k`.

The relative effective divisors and their Cartier ideals are the Library's
`Picard.RelativeEffectiveDivisor` and `Picard.IsRelativeEffectiveCartierIdeal`.
An actual ideal sheaf qualifies when its kernel module is locally free of
rank one and its closed subscheme is flat over the base. Equality of divisors
is equality of actual ideal sheaves.

## Sources

S. L. Kleiman, *The Picard scheme*
(`kleiman-2005-picard-scheme-arxiv-math0504020v1`):

- Conventions, p.15: "Throughout these notes, we work only with locally
  Noetherian schemes". Kleiman adds that a limiting process reduces the general
  case to the noetherian one, but he does not carry it out. So all of his test
  schemes `T` below are locally noetherian.
- Lemma 3.4 (p.22, proof pp.22–23), for locally noetherian schemes: a closed
  subscheme `D ⊆ X` is a relative effective divisor near a point `x` over
  `s ∈ S` exactly when `X` and `D` are `S`-flat at `x` and the fibre `D_s` is
  an effective divisor on `X_s` at `x`. The proof uses the local flatness
  criterion and Nakayama's lemma over the noetherian local rings.
- Definition 3.6 (p.23) defines the functor `Div_{X/S}(T)` of relative
  effective divisors on `X_T/T`. The paragraph after it proves base-change
  stability.
- Theorem 3.7 (p.23), proved on p.24: if `X/S` is projective and flat, then
  `Div_{X/S}` is representable by an open subscheme `Div_{X/S}` of the Hilbert
  scheme `Hilb_{X/S}`. The universal divisor is the restriction of the
  universal closed subscheme to this open subscheme.
- In the proof of the main Theorem 4.8 (p.30), the piece of `Div_{X/S}` with
  Hilbert polynomial `θ` lies in `Hilb^θ_{X/S}`, "which is projective over
  `S`", and is therefore quasi-projective.

N. Nitsure, *Construction of Hilbert and Quot schemes*
(`nitsure-2005-hilbert-quot-arxiv-math0504590v1`):

- p.3: the functors are defined on `Sch_S`, "the category of all locally
  noetherian schemes over `S`", for `S` noetherian.
- pp.3–4 define `Hilb_{X/S}` as `Quot_{O_X/X/S}` and decompose it by the
  Hilbert polynomials of the fibres, computed with respect to a line bundle `L`
  (p.4).
- Theorem 5.3 (p.24): over a noetherian `S`, for `X` a closed subscheme of
  `P^n_S` and `L = O(1)|_X`, each `Quot^{Φ,L}` (in particular each `Hilb^Φ`)
  embeds over `S` as a closed subscheme of some `P^r_S`.

The Library theorem
`AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections`
(the "FLT theorem", ported from the Anthropic FLT formalization) is the other
input. Its tests are all affine schemes `Spec B`, for every commutative ring
`B : Type u`, noetherian or not.

The statement therefore has provenance *derived*. Its conclusion on locally
noetherian tests is Kleiman's Theorem 3.7 with the pieces of p.30. Its
conclusion on arbitrary tests is the derivation below. That derivation combines
Kleiman's proof with the FLT theorem, and a proof of the statement must supply
it.

## Derivation for arbitrary test schemes

The Lean statement asks for representability (item 2) on every
`T : Scheme.{u}` over `S`. The following route needs no noetherian
approximation, because the FLT theorem already covers all affine tests.

1. **The Hilbert scheme on all tests.** The FLT theorem gives `Hilb`,
   `πH : Hilb ⟶ S` and a classifier `pt`. The classifier sends each closed
   immersion `ι : Z ⟶ X ×_S Spec B` such that `ι ≫ pullback.snd f s` is flat
   and locally of finite presentation to a morphism `Spec B ⟶ Hilb` over `S`.
   For every ring `B`, `pt` is surjective onto the morphisms over `S`, injective
   up to isomorphism of `Z` over `X ×_S Spec B`, and natural for ring maps
   `B → B'`, which act on `Z` by base change. The theorem does not provide a
   universal family, so a proof must construct one.
   - For each affine open `V ⊆ Hilb`, surjectivity gives a flat, locally finitely
     presented closed subscheme of `X ×_S V` classified by the inclusion
     `V ⟶ Hilb`.
   - On an affine open `V'' ⊆ V ∩ V'`, naturality along `V'' ⟶ V` and
     `V'' ⟶ V'`, together with injectivity, shows that the two restrictions
     agree.
   - Ideal sheaves glue, so these subschemes form one closed subscheme
     `W_H ⊆ X ×_S Hilb` that is flat and locally finitely presented over `Hilb`.
   - Naturality, checked on an affine open cover of `Spec B`, shows that `pt`
     of the pullback of `W_H` along any `g : Spec B ⟶ Hilb` over `S` is `g`.

   Now let `T` be any scheme over `S`. Pulling back `W_H` is a bijection from
   the morphisms `T ⟶ Hilb` over `S` onto the flat, locally finitely presented
   closed subschemes of `X ×_S T`. On the affine opens of `T` this is the FLT
   classification. On affine opens of the pairwise overlaps, the classifying
   morphisms agree by naturality and injectivity, so they glue. The glued
   morphism is unique because a morphism is determined by its restrictions to
   an open cover. No quasi-compactness or separatedness of `T` is used.
2. **Divisors are classified by `Hilb`.** Let `I` be a relative effective
   Cartier ideal on `X ×_S T` over `T`. Its kernel module is locally free of
   rank one, so the ideal is locally principal and `I.subscheme ⟶ X ×_S T` is
   a closed immersion of finite presentation. The projection `X ×_S T ⟶ T` is
   locally of finite presentation because `f` is (see "Projectivity
   hypothesis" below). Finally `I.subscheme` is flat over `T` by definition.
   So step 1 gives a unique `g : T ⟶ Hilb` over `S` along which `W_H` pulls
   back to `I`.
3. **The Cartier locus.** Kleiman's proof of Theorem 3.7 (p.24) works with the
   universal family itself, so it carries over to `W_H ⟶ Hilb`. Let `U ⊆ Hilb`
   be the complement of the image, under the proper projection
   `q : W_H ⟶ Hilb`, of the closed set of points at which `W_H` is not an
   effective divisor in `X ×_S Hilb`. Here `Hilb` is locally of finite
   presentation over the noetherian ring `A`, so `Hilb` and `X ×_S Hilb` are
   locally noetherian. Kleiman's argument, including Lemma 3.4, therefore
   applies verbatim: `U` is open, and `W_H ∩ (X ×_S U)` is a relative effective
   divisor on `X ×_S U` over `U`. Take `D := U`, `d := U.ι ≫ πH`, and `W` this
   divisor.
4. **Arbitrary tests.**
   - The base-change argument after Kleiman's Definition 3.6 (p.23) uses only
     two facts: the divisor is flat over its base, and its ideal is invertible.
     So it holds for every `T` and gives the first clause of item 2.
   - Now let `I` be a relative effective divisor on `X ×_S T` over `T`, and let
     `g : T ⟶ Hilb` be the morphism from step 2. Kleiman's fibre argument
     (p.24) shows that `g` factors through `U`. Let `t ∈ T` have residue field
     `κ(t)`. The fibre `I_t` is an effective divisor, by base change. It is the
     base change of `(W_H)_{g(t)}` to `κ(t)`. A field extension is faithfully
     flat, so `(W_H)_{g(t)}` is an effective divisor too. Lemma 3.4, applied at
     the points of the locally noetherian `X ×_S Hilb` over `g(t)`, then gives
     `g(t) ∈ U`.
   - This argument puts no noetherian hypothesis on `T`.
   - The open immersion `U ⟶ Hilb` is a monomorphism, so uniqueness in
     step 2 gives uniqueness of the factorisation `T ⟶ D`. This is the second
     clause of item 2.
5. **Pieces.** Take `U θ := U ∩ Hilb^θ`, where the `Hilb^θ` are the FLT pieces.
   - **Membership.** Let `g : Spec B ⟶ D` classify the ideal `I`. By step 1,
     `pt` of `I.subschemeι` is `g ≫ U.ι`. So the FLT piece clause with
     `Z = I.subscheme` and `ι = I.subschemeι` is exactly the membership
     condition of item 3.
   - **Comparison with Nitsure's `Hilb^θ`.** Nitsure's `Hilb^θ` represents the
     Hilbert functor with polynomial `θ` on locally noetherian `S`-schemes
     (pp.3–4). The FLT piece is locally of finite presentation over `A`, hence
     locally noetherian. By step 1 it represents the same functor on locally
     noetherian tests, for three reasons. First, there closed subschemes of
     `X_T` are automatically locally of finite presentation over `T`. Second,
     their support is proper over `T` because `X` is projective. Third, the
     `h⁰` condition agrees with Nitsure's Euler-characteristic condition; see
     "Measuring the Hilbert polynomial" below. Yoneda's lemma in the category
     of locally noetherian `S`-schemes then identifies the two schemes.
   - **Quasi-projectivity.** By Nitsure's Theorem 5.3, `U θ` is an open
     subscheme of a closed subscheme of some `P^r_A`. The resulting immersion
     into `P^r_A` is quasi-compact because `P^r_A` is noetherian.

These steps explain the derivation. They are not Lean proofs.

## Relation between the Lean statement and the sources

- **Projectivity hypothesis.** "`X/S` projective" is given by
  `ClosedImmersionBySections 𝓛X f`. It provides global sections
  `σ₀, …, σ_N` of `𝓛X` and a closed immersion `X ⟶ ℙᴺ_A` over `A`. Each `σᵢ`
  is a basis of `𝓛X` over the preimage of the chart `D₊(Xᵢ)`, compatibly with
  the chart coordinates `Xⱼ/Xᵢ`. So `𝓛X` plays the role of `O(1)|_X`, and
  Hilbert polynomials are computed with respect to `𝓛X`, Nitsure's `L`. The
  Library theorem
  `Langlands.AlgebraicGeometry.Picard.exists_closedImmersionBySections_iff_isHProjective`
  shows that such a pair `(𝓛X, presentation)` exists exactly when
  `IsHProjective f`. Since `A` is noetherian and `X` is closed in `ℙᴺ_A`, `f`
  is locally of finite presentation, so the FLT theorem applies without an
  extra hypothesis. Geometric integrality of the fibres is not needed.
- **Test schemes.** Kleiman and Nitsure use only locally noetherian test
  schemes. Item 2 holds for all `T : Scheme.{u}`; steps 1–4 of the derivation
  above give this extension. Item 3 characterises the pieces on affine tests
  `Spec B` for every ring `B`, like the FLT piece condition. Whether a morphism
  `T ⟶ D` lands in the open `U θ` can be checked on an affine open cover of
  `T`, so nothing is lost.
- **Universal divisor.** The universal divisor `W` lives on all of `X ×_S D`,
  not only over affine opens. So users can restrict it to any open subscheme
  of `D`. They can also classify divisors over non-affine schemes directly by
  item 2, for instance over a projective bundle on an open subscheme of `D`.
- **Base change.** The first clause of item 2 is the base-change stability of
  `W` along the classifying morphisms. It is stated directly, so the statement
  does not depend on the unproved
  `Picard.RelativeEffectiveDivisorBaseChangeStatement`.
- **Measuring the Hilbert polynomial.** The fibre Hilbert polynomial is
  detected by `h⁰` of large twists rather than by Euler characteristics. By
  Serre vanishing, for large `n` the dimension of global sections of the `n`-th
  twist on a projective scheme over a field equals the Euler characteristic.
  Both quantities are unchanged by extending the field. So the condition says
  that the Hilbert polynomial with respect to `𝓛X` of each fibre of the
  divisor is `θ`. The expression is token-for-token the piece condition of the
  FLT theorem, specialised to `ι = I.subschemeι`. A development check confirms
  that the FLT piece condition, applied to `I.subschemeι`, typechecks as this
  clause.
- **Pieces of `D`.** The pieces `U θ` are the intersections of the open
  subscheme `D` with the clopen pieces `Hilb^θ` (step 5). They are open. Being
  disjoint and covering, they are also closed. A piece may be empty.
- **Quasi-projectivity of the pieces.** The FLT theorem itself gives the
  Hilbert pieces only as clopen subschemes, quasi-compact over `S`. Their
  projectivity (Nitsure's Theorem 5.3, through the Grassmannian embedding) is
  extra content of this statement; see step 5.
- **Finiteness and separation.** `d` is locally of finite presentation and
  separated because `D` is open in the Hilbert scheme, which has both
  properties. The FLT theorem asserts both for the Hilbert scheme it
  constructs.

## Use

Kleiman's construction of the Picard scheme (Theorem 4.8, pp.27–31) uses the
pieces of `Div_{X/S}` as the quasi-projective scheme `Z` that is quotiented by
the linear-system equivalence relation. See
`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientStatement`.
Task 5705 uses the statement for this step.
