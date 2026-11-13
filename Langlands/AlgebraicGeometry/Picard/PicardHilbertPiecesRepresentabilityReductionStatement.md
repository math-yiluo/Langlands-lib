# Reduction of the representability of the Picard pieces to divisors, linear systems, fppf quotients and base change of divisors

Authors: Worker 22.

Worker 22 wrote the Lean file and this description for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705), in agreement with that
task's first executor, Worker 5705. The proposition reduces the published
`PicardHilbertPiecesRepresentabilityStatement` (the quasi-projective pieces
`P^φ_m` of the Picard sheaf, Kleiman's proof of Theorem 4.8) to four published
statements. It is the reduction that proof Task 6214 allows.

No proof is asserted here. The module only states the implication.

## Statement

The module defines one declaration,
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionStatement`,
with the single universe parameter `u`. It is a proposition (`def … : Prop`):

```lean
RelativeEffectiveDivisorHilbertPiecesStatement.{u} →
  ProperFlatIntegralLinearSystemStatement.{u} →
    FppfQuotientLocallyNoetherianStatement.{u} →
      RelativeEffectiveDivisorBaseChangeStatement.{u} →
        PicardHilbertPiecesRepresentabilityStatement.{u}
```

All five propositions are published Library statements, imported from their
modules. All are used at the same universe `u`. The hypotheses are:

1. `Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesStatement`
   ("(a)"). For a flat `f : X ⟶ Spec A` over a noetherian ring with an
   invertible `𝓛X` whose sections give a closed immersion, there is a scheme
   `D` with a relative effective divisor `W` on `X ×_A D`. It is locally of
   finite presentation and separated over `A`, and it classifies relative
   effective Cartier ideals on `X_T` for every `T`. The comap of `W` along a
   classifying map is again relative effective Cartier. `D` has disjoint opens
   `U θ` covering it. Each is H-quasi-projective and consists, on affine tests,
   of the divisors whose geometric fibres have Hilbert polynomial `θ` with
   respect to `𝓛X` (Kleiman Theorem 3.7).
2. `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement`
   ("(b)"). For a proper flat `g : Y ⟶ T` with geometrically integral fibres
   over a locally noetherian `T` and an invertible `M` on `Y`, it gives the
   linear system `l : Λ ⟶ T`, which is proper, with a universal divisor `W` on
   `Y ×_T Λ`. On locally noetherian tests `T'`, `W` classifies, uniquely, the
   relative effective Cartier ideals `E` with `O(E) ≅ M_{T'} ⊗ N'` for an
   invertible `N'` on `T'`. If `H¹` of `M` vanishes on all fibres, then `l` is
   flat and locally of finite presentation, and also surjective if moreover
   `H⁰` never vanishes (Kleiman Theorem 3.13).
3. `Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianStatement`
   ("(c'')"). Let `ζ : Z → G` be a map to an fppf sheaf on `Over (Spec A)`,
   with `A` noetherian, `Z` H-quasi-projective and `ζ` fppf-locally
   surjective. Let `s, t : R ⟶ Z` satisfy `ζ s = ζ t` and represent `Z ×_G Z`
   on locally noetherian tests, with `s` flat and proper. Then there are an
   H-quasi-projective `Q`, a flat, surjective, proper, locally finitely
   presented `π : Z ⟶ Q`, and `e : Q → G` with `π e = ζ`, bijective on locally
   noetherian tests (Kleiman Lemma 4.9 with [AK80, Thm. 2.9], fppf form).
4. `Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeStatement`
   ("base change"). For a relative effective Cartier ideal `I` on `X` over `S`
   and any `g : T ⟶ S`, the comap of `I` to `T ×_S X` is relative effective
   Cartier, and the pullback of the ideal module of `I` is isomorphic to the
   ideal module of the comap. The isomorphism is compatible with the
   inclusions into the structure modules (Kleiman p.23, after Definition 3.6).

The conclusion `Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityStatement`
("(C)") is unchanged. For a proper flat `f : X ⟶ Spec A` with geometrically
integral fibres and a section, an `𝓛X = O_X(1)` as above, and opens
`U T s L c m` with its four properties, it gives, for each `c` and `m`, an
H-quasi-projective `Q` and `β : Q → Pic` that is injective on locally
noetherian tests. Its image there consists of the classes of the line bundles
`L` with `U T L c m = T`.

The Library theorem
`Langlands.AlgebraicGeometry.Picard.properFlatIntegralSheafClassTwist`
proves `ProperFlatIntegralSheafClassTwistStatement` ("S-cls"). Under the
hypotheses of (C), every element of the Picard sheaf is the class of a line
bundle, and two line bundles have the same class exactly when they differ by
the pullback of an invertible module on the base. Since S-cls is proved, it is
not a hypothesis here; the intended proof uses the theorem.

## Source and derivation

The source is S. L. Kleiman, *The Picard scheme*, arXiv math/0504020v1
(2005), registered as `kleiman-2005-picard-scheme-arxiv-math0504020v1`.
Kleiman proves the existence of the pieces in the proof of Theorem 4.8
(pp.29–31). The divisor scheme and its Hilbert-polynomial parts come from
Theorem 3.7, the linear system `LinSys_L = P(Q)` from Theorem 3.13 (p.25), and
the quotient from Lemma 4.9 with Exercise 4.10 (pp.30–31). Kleiman treats the
base change of relative effective divisors and of their ideals in the
paragraph after Definition 3.6 (p.23). The statement here makes each of these
ingredients a hypothesis, in the form of a published Library statement.
Provenance is derived: the reduction is not stated by Kleiman but extracted
from his proof. The derivations of the differences between (C) and Kleiman's
text are in the Markdown of
`PicardHilbertPiecesRepresentabilityStatement` and are not repeated here.

The intended proof follows Kleiman's argument, with the fppf topology
replacing the étale one. Fix `c` and `m`, and write `S = Spec A`.

1. **The open part `Z` of the divisor scheme.** Apply (a) to `f` and `𝓛X` to
   get `D`, `W` and the opens `U θ`. `D` is locally of finite type over the
   noetherian `S`, hence locally noetherian. Let `L_W` be `O(W)` tensored with
   the `m`-th power of the inverse of the pullback of `𝓛X`, on `X ×_S D`. Let
   `Z₀ := U D d L_W c m`, an open of `D`. Through property 2 of (C) and base
   change, a point `x : Spec B → Z₀` with `B` noetherian corresponds to a
   divisor `x^*W` with `O(x^*W) ≅ (x^*L_W)(m)`. So property 4 of (C) and the
   criterion in (a) put `Z₀` inside `U (θ c m)`. As an open of an
   H-quasi-projective scheme, `Z₀` is H-quasi-projective. This is Kleiman's
   `Z = P^{φ₀}_0 ×_P Div`, which lies in `Hilb^θ` (p.30). The twist by `O(m)` is
   built into `L_W`.
2. **The Abel map.** `ζ : Z₀ → Pic` sends `x` to the class of `x^*L_W`. Let `G`
   be the fppf sheafification of its image, a subsheaf of `Pic`. `ζ` maps
   fppf-locally surjectively onto `G`.
3. **The relation `R`.** Apply (b) over `T := Z₀` to the family
   `X ×_S Z₀ → Z₀` and `M := O(W)|_{Z₀}`. This gives `l : Λ ⟶ Z₀` and a
   universal divisor `W_Λ`. Set `s := l`, and let `t : Λ ⟶ Z₀` classify `W_Λ`
   through (a). `t` lands in `Z₀` by properties 1 and 2 of (C) and base change.
   S-cls (the class identity of twists) gives `ζ s = ζ t`. On a locally
   noetherian `T`, let `x, y : T ⟶ Z₀` have the same image in `Pic`. Then S-cls
   gives `x^*L_W ≅ y^*L_W ⊗ N`. Base change then shows that `y^*W` lies in the
   linear system of `x^*O(W)`, so (b) gives a unique `k` with `k ≫ s = x` and
   `k ≫ t = y`. This is Kleiman's `T' ×_P Z = LinSys_{L'}` (p.30). By
   property 3 of (C), `H¹` vanishes and `H⁰` does not on the fibres, so `s` is
   flat, of finite presentation and surjective. It is also proper.
4. **The quotient.** (c'') applied to `ζ : Z₀ → G` and `s, t` gives `Q`, `π`
   and `e : Q → G`. Let `β` be `e` followed by the inclusion `G ⊆ Pic`. On
   locally noetherian tests, `β` is injective because `e` is bijective and the
   inclusion is injective.
5. **The image.** Let `T` be locally noetherian and `L` a line bundle on `X_T`.
   If the class of `L` is `β(q)`, pull back along the fppf cover `T ×_Q Z₀ → T`
   (a pullback of `π`). There the class is `ζ` of a point, so property 1 of (C)
   and S-cls give `U = ⊤` on the cover. Property 2 and the surjectivity of the
   cover then give `U T L c m = T`. Conversely, if `U T L c m = T`, apply (b)
   to `L(m)` over `T`. The resulting `Λ_T → T` is flat, locally of finite
   presentation and surjective by property 3, hence a single-arrow fppf cover.
   Its universal divisor is classified by (a) through `Z₀`, and the class of
   `L` on `Λ_T` is `ζ` of that point. So the class of `L` lies in `G`, the
   image of `β`.

The base-change hypothesis is needed because the line bundle `O(E)` of a
relative effective divisor is built from its actual ideal module, while (a)
and (b) only say that the comap of the universal ideal along a classifying map
is again relative effective Cartier. They do not identify its ideal module with
the pullback of the universal one. The proof needs `O(g^*W) ≅ g^*O(W)` in
steps 1, 3 and 5: for `Z₀ ⊆ U (θ c m)`, for `ζ s = ζ t` and the universal
property of `R`, and for the image. `RelativeEffectiveDivisorBaseChangeStatement`
supplies exactly this kernel isomorphism. Its proof is Task 5913.

## Conventions and scope

- The statement is an implication between published propositions. It
  introduces no new definitions and assumes nothing beyond the four listed
  propositions.
- (a) and base change hold for arbitrary test schemes in universe `u`. (c'')
  concerns fppf sheaves on all `Spec A`-schemes, but its representability
  clause and the bijectivity of `e` concern locally noetherian tests only.
  (b) concerns locally noetherian bases and tests. The intended proof applies
  (b) only to the locally noetherian `Z₀` and to locally noetherian tests
  `T`, which matches the locally noetherian tests of (C).
- Each hypothesis is a published statement with its own proof obligation. Once
  the reduction is proved, (C) follows from proofs of the four hypotheses.
