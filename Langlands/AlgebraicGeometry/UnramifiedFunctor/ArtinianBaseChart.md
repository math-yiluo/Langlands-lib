# Step 1 of Murre's induction: the chart of a field point

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseChart`, a supporting module of
`murreArtinianBase` (module `MurreArtinianBase`). Namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase`. Notation as in `ArtinianBaseTools`.

Murre's Step 1 (Bourbaki exp. 294, PDF p. 6) obtains, for each point of `F`, a complete local
ring pro-representing `F` there via (F4). Here the conditions are (F4′) and strong (F5), and the
local rings are built directly. A minimal field point `η ∈ F(Spec L)` determines the artinian
ring `E/J`: `E` is a formally étale lift of `L` over `R`, and `J` is the smallest ideal to which
`η` lifts. Over `E/J`, `η` has a lift `ξ` satisfying ring-level forms of "infinitesimally étale"
and "monomorphism". This construction is internal to the proof.

## `exists_etale_lift`

Let `R` be local artinian, `k` a field with `R → k` surjective (`k` is the residue field), and
`L / k` finite separable. Then there is a local artinian `R`-algebra `E` such that:

* `E` is formally étale and of finite type over `R`;
* there is a surjection `πE : E → L`.

Construction:

* `θ` is a primitive element of `L / k`, with separable minimal polynomial `g`, and `ĝ ∈ R[X]`
  is a monic lift of `g`. Then `E = R[X]/(ĝ)` is finite over `R`, hence artinian.
* `πE` sends `X` to `θ`. It is surjective, and its kernel lies in `m_R E`, which is nilpotent.
  So `E` is local (`isLocalRing_of_ker_nil`).
* The image of `ĝ'` is a unit of `E`, since `g` is separable. Hence `E` is the standard étale
  algebra of the Mathlib pair `StandardEtalePair` `(ĝ, ĝ')`. Via
  `StandardEtalePair.equivAwayAdjoinRoot` and `IsLocalization.atUnit`, `E` is formally étale.

## `chart_lift`

Let `E` be local artinian and formally étale with residue map `πE : E → L`, and `η ∈ F(Spec L)`.
Let `J` be the least ideal `I` such that `η` has an element over it on `E/I` (hypothesis
`hJmin`: `J ≤ I` for every such `I`; this is stronger than minimality), and let
`ξ ∈ F(Spec (E/J))` be such an element. Let `A` be local artinian, `I ⊆ A` nilpotent,
`u₀ : E/J → A/I`, and `v ∈ F(Spec A)` with `u₀^* ξ = v|_{A/I}`. Then `u₀` lifts to
`u : E/J → A` with `u^* ξ = v`.

* Formal smoothness lifts `E → E/J → A/I` to `ψ : E → A`. Its kernel `K` lies in `m_E`, so
  `C = E/K` is local and embeds in `A`.
* `v` lies over `η` along `C ⊆ A`: field points of `A` kill `I`, and `u₀^* ξ = v|_{A/I}`.
* `descend_general` lifts `η` to `C = E/K`. Since `J` is least, `J ≤ K`, so `ψ` factors
  through `u : E/J → A`.
* `u^* ξ` and `v` have the same restriction `u₀^* ξ` to `A/I`. They are equal by strong (F5)
  (`nilInj`).

## `exists_chart_ring`

Assume:

* `R → k` is surjective with nilpotent kernel;
* `L / k` is finite separable;
* `E` is local artinian and formally étale, with surjection `πE : E → L`;
* `η ∈ F(Spec L)` is minimal (`IsMinimal`).

Then there are an ideal `J ≤ ker πE` and `ξ ∈ F(Spec (E/J))` over `η` such that:

1. (ring-level infinitesimal étaleness) for local artinian `A`, nilpotent `I`, `u₀ : E/J → A/I`
   and `v ∈ F(Spec A)` with `u₀^* ξ = v|_{A/I}`, there is a unique `u : E/J → A` lifting `u₀`
   with `u^* ξ = v`;
2. (monomorphism on field points) two maps `φ₁, φ₂ : E/J → K` to a field with
   `φ₁^* ξ = φ₂^* ξ` are equal.

The proof goes as follows.

* The set of ideals `I` such that `η` has an element over it on `E/I` contains `ker πE`.
  Choose a minimal element `J` (well-foundedness of `<` on ideals of the artinian ring `E`).
  It is the least element, since the set is closed under `⊓` (`inter_closed`).
* Existence in (1) is `chart_lift`. Uniqueness holds because `E/J` is formally unramified over
  `R` (`Algebra.FormallyUnramified.ext`).
* For (2), `φ₁` and `φ₂` factor through the residue field `L` of `E/J`. Since `ξ` restricts to
  `η` there, `mono_field` applies.
