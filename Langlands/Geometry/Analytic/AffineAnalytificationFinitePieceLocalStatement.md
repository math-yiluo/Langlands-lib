# Statement: local structure of the finite pieces of an affine analytification map

Lean: `Langlands.Analytic.AffineAnalytification.AffineAnalytificationFinitePieceLocalStatement`
(intermediate statement for the proof of `AffineAnalytificationFiniteGermComparisonStatement`).

## Setting

Let `K` be a complete, ultrametric, nontrivially normed field, let `A` and `B` be commutative
`K`-algebras with finite polynomial presentations `P` and `Q`, and let `f : A →ₐ[K] B`. Write
`X` for the analytification `(presentation K Q).space` of `B`, `Y` for the analytification
`(presentation K P).space` of `A`, and `g := saturatedHom K P Q f : X → Y` (published in
`AffineAnalytificationLocalizedMap`).

Fix open sets `V ⊆ X` and `U ⊆ Y` such that `g` is finite over `V` and `U`
(`StrongHom.IsFiniteOver`, published in `FullRecognitionFiniteMorphisms`). Fix a recognized
affinoid subset `W` of `Y` with `W.locus ⊆ U`, write `R := W.algebra`, and fix a recognized
affinoid subset `V'` of `X` whose locus is `V ∩ g⁻¹(W.locus)`, with algebra `S := V'.algebra`
and the hypothesis `h` that `g` maps the chart image of `V'` into that of `W`. Then
`φ := g.fullRecognitionPairs.pullback V' W h : R → S` is the bounded map of the piece, and we
assume that `φ` is finite Banach (`BoundedAlgHom.IsFiniteBanach`). `IsFiniteOver` provides this
for one recognized subset with the given locus. A recognized subset is determined by its locus
(it is a subtype of a type of subsets), so that subset is `V'` itself, and the assembly obtains
the hypothesis directly.

## Assertion

There exist `K`-algebra maps `α : A → R` and `β : B → S` such that

1. `α` is flat (`α.toRingHom.Flat`);
2. for every point `t` of the Banach spectrum of `R` and every `a : A`, `t (α a)` equals the
   value at `a` of the seminorm `pointSeminorm K P (W.chart t)` of the analytic point
   `W.chart t`;
3. for every point `s` of the Banach spectrum of `S` and every `b : B`, `s (β b)` equals the
   value at `b` of the seminorm `pointSeminorm K Q (V'.chart s)` of the analytic point
   `V'.chart s`; and
4. with `A`-algebra structures on `R` and `B` given by `α` and `f`, there is a ring map
   `χ : R ⊗[A] B → S` with `χ (r ⊗ 1) = φ r` and `χ (1 ⊗ b) = β b`, such that for every point
   `s` of the Banach spectrum of `S`, the induced local map
   `Localization.localRingHom (s.kernel.comap χ) s.kernel χ rfl :
   (R ⊗[A] B)_(χ⁻¹ ker s) → S_(ker s)` is bijective.

The maps `α`, `β`, `χ` are existential: the Library has no named canonical map from `A` to the
algebra of a general recognized subset. Conditions 2 and 3 tie `α` and `β` to the points of `W`
and `V'`: each point restricts along them to the seminorm of its analytic point. They fix only these
absolute values, not the maps themselves. Condition 4 forces `φ ∘ α = β ∘ f`, since `χ` is
defined on the tensor product over `A`. Condition 3 identifies the prime `β⁻¹(ker s)` of `B` with
the kernel of the seminorm of `V'.chart s`.

## Provenance

This statement is derived Library content. It is not stated in this form in the sources.
Conditions 1–3 restate results of Berkovich 1990 for the Library's recognized subsets.
Condition 4 is a new assertion about the Library's recognized pieces. The sources only motivate
it, and the argument below justifies it.

* Conditions 2 and 3 hold for the canonical maps from the algebra to the affinoid algebra of an
  affinoid domain of its analytification (Berkovich 1990, §3.4). They are stated through the
  Library's `pointSeminorm` because the Library names no such map for a general recognized subset.
* Flatness of `α` is Berkovich 1990, last paragraph of the proof of Theorem 3.4.1 (printed
  pp.63–64/PDF pp.77–78): the algebra of an affinoid domain of the analytification is flat over
  the algebra. For the Library this is chart flatness (`AffineAnalytificationChartFlatStatement`,
  published) composed with affinoid-domain flatness (`Domain.FlatnessStatement`, proved in
  `GeneralizedAffinoid.DomainFlatnessProof`).
* Condition 4 is motivated by Berkovich 1993, Proposition 2.6.10 (printed p.54/PDF p.51), but it
  is not that proposition. Proposition 2.6.10 starts from a finite morphism
  `Spec(C) → Spec(B)` of affine schemes of finite type over the spectrum of a `k`-affinoid
  algebra. It expresses the tensor product of the analytic stalk at a point `y` with the
  algebraic local ring at `z`, over the algebraic local ring at the image of `y`, as a product of
  the analytic stalks at the points over `y`. The factors at points that do not lie over `z` are
  further localized. Its proof uses the identity `A_W = A_V ⊗_B C` for an affinoid domain `V` and
  its full preimage `W` under the finite algebraic morphism. In the proof of Proposition 3.2.10
  (printed p.60/PDF p.57), Zariski's Main Theorem first embeds the source in a scheme finite over
  the target, and only then is Proposition 2.6.10 applied. Proposition 3.3.11 (printed p.64/PDF
  p.61) obtains unramifiedness separately, by comparing the sheaves of differentials, and gets
  étaleness from Proposition 3.2.10.
* In the Library's setting the morphism `Spec B → Spec A` need not be finite. Only the
  analytification is finite over `V` and `U`, and the piece `V'` is cut out of the preimage of `W`
  by the open set `V`. Condition 4 is the analogue of `A_W = A_V ⊗_B C` for such a piece. It
  asserts an isomorphism only after localizing at the primes of points of `V'`: in general `χ` is
  surjective but not injective, since `V'` omits the part of the preimage of `W` outside `V`.
  The argument below uses neither Zariski's Main Theorem nor Proposition 2.6.10. It uses the
  universal properties of the Library's chart algebras and affinoid pushouts, finiteness of `φ`,
  and the Krull intersection theorem.

## Why condition 4 holds

Write `C := R ⊗[A] B` and let `χ : C → S` be the map given by `φ` and `β`. A Lean proof following
this outline is in `FinitePieceLocalProof` and its support modules. Its theorem
`affineAnalytificationFinitePieceLocal` takes `AffineAnalytificationChartFlatStatement` and
`Domain.FlatnessStatement` as hypotheses, for condition 1.

1. *Test factorizations.* Let `E` be a complete ultrametric normed `K`-algebra and let
   `τ : C → E` be a ring map that is bounded on `R`. Choose a chart `B_i` of the analytification
   of `B` whose locus contains `V'`, large enough that `τ` restricted to `B` extends boundedly to
   `B_i`. Choose a chart `A_j` of the analytification of `A` containing `W` and the image of the
   chart `i`. Let `D` be the affinoid pushout of the chart map `A_j → B_i` and the restriction
   `A_j → R`. By the Library's `fullRecognitionPullbackEquiv`, `D` is the algebra of the recognized
   preimage `V''` of `W` in the chart `i`, with locus `chart_i ∩ g⁻¹(W)`. The two extensions of `τ`
   agree on `A_j`, because bounded maps out of a chart algebra are determined by `A`. So they
   induce a bounded map `θ : D → E`. Both legs give a map `κ : C → D` with `θ ∘ κ = τ`. The
   restriction `ρ : D → S` from `V''` to `V'` satisfies `ρ ∘ κ = χ`. Since
   `V'.locus = V''.locus ∩ V` with `V` open, `V'` is clopen in `V''`, so `ρ` is surjective. It
   is the restriction to an idempotent `e` of `D`: `ρ e = 1`, and `ρ x = 0` implies `e x = 0`. A
   bounded map out of `D` is determined by its composite with `κ`, by the universal property of
   the pushout and of the chart algebra `B_i`.
2. *`χ` is surjective.* Its image `S₀` is an `R`-subalgebra of `S`. It is a finite `R`-module,
   because `S` is finite over the Noetherian ring `R` (`φ` is finite Banach). Give `S₀` a complete
   ultrametric `K`-algebra norm by the quotient norm from `Rⁿ` through chosen generators. Apply
   step 1 with `E := S₀` and `τ := χ`. The inclusion `ι : S₀ → S` is bounded, because it is
   compatible with the bounded maps from `R` to the finite algebra `S₀` and to `S`. Then
   `ι ∘ θ = ρ`, since both agree after `κ`. As `ρ` is surjective, `S = ι(θ(D)) ⊆ S₀`.
   Chart density alone does not give this, since restriction maps to Laurent domains need not
   have dense image. The factorization through `D` uses both legs of `χ`.
3. *The kernel lies in every thickening.* Let `n` be a maximal ideal of `S`, let `p := χ⁻¹(n)`
   and `k ≥ 1`. Every element of `C` is integral over `R` modulo `p`, because `C/p` embeds in `S/n`,
   which is finite over `R`. Since `C` is of finite type over `R`, `E := C/p^k` is a finite
   `R`-module. Give it a norm as in step 2 and apply step 1 with `τ` the quotient map. The map
   `λ : C/p^k → S/n` induced by `χ` is bounded, where `S/n` has the quotient norm, and
   `λ ∘ θ = (S → S/n) ∘ ρ`. Hence `λ(θ e) = 1`. The kernel `p/p^k` of `λ` is nilpotent, so `θ e`
   is a unit. An idempotent unit equals `1`, so `θ e = 1`. For `c ∈ ker χ`, `ρ(κ c) = 0` gives
   `e κ(c) = 0`. Then `τ c = θ(e) θ(κ c) = θ(e κ c) = 0`, that is, `c ∈ p^k`.
4. *Krull.* `C` is Noetherian, being of finite type over `R`. Let `s` be a point of the Banach
   spectrum of `S` and `n ⊇ ker s` a maximal ideal. By step 3 every `c ∈ ker χ` lies in
   `⋂_k p^k`, so `c` maps to `0` in the Noetherian local ring `C_p` (Krull intersection theorem).
   Since `χ⁻¹(ker s) ⊆ p`, `c` also maps to `0` in `C_(χ⁻¹ ker s)`. So the local map at `ker s` is
   injective, and it is surjective by step 2.

## Use

The module `AffineAnalytificationFiniteGermAssembly` proves
`finiteGermComparison_of_finitePieceLocal`, which derives the target
`AffineAnalytificationFiniteGermComparisonStatement` from this statement by commutative algebra:
the published `TensorStalkBaseChange`, `TensorStalkReflection` and `FlatTargetDescent` modules, plus
unfolding of `HasFinitePiecesAt`, `IsFlatAt` and `IsUnramifiedAt` (published
`FullRecognitionEtaleMorphisms`). It uses conditions 1, 3 and 4.
