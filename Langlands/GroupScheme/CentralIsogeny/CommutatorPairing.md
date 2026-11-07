# The commutator pairing of a central extension with commutative quotient

This module develops the published descended commutator

    CommutatorDescent.hom π hπ : G × G ⟶ C

of `GroupScheme/CentralIsogeny/CommutatorDescent` for a homomorphism of group schemes
`π : C ⟶ G` over an arbitrary base scheme `S`. Here the full scheme-theoretic kernel of
`π` is central (`hπ : IsCentral (kernelι π)`), and `π` is quasi-compact, flat and
surjective on underlying schemes (instance arguments). When the points of `G` commute, it
packages the descended commutator as a morphism `G × G ⟶ K` into a group scheme `K`
representing the kernel. This morphism is biadditive, alternating and equivariant. It is
the scheme-theoretic form of the elementary commutator pairing
`(π x, π y) ↦ x y x⁻¹ y⁻¹` of a central extension with abelian quotient. No field or
smoothness hypothesis occurs.

## Group-theoretic lemmas

In an arbitrary group `M`:

- `commutator_mul_left_of_commute a b c h`: if the commutator `b c b⁻¹ c⁻¹` commutes with
  every element, then
  `(a b) c (a b)⁻¹ c⁻¹ = (a c a⁻¹ c⁻¹)(b c b⁻¹ c⁻¹)`.
- The published `RationalDensity.commutatorElement_mul_of_commute a b c h`: if `a c a⁻¹ c⁻¹` commutes with every element,
  then `a (b c) a⁻¹ (b c)⁻¹ = (a b a⁻¹ b⁻¹)(a c a⁻¹ c⁻¹)`.

The first identity is a direct group calculation. The second reuses the existing
lemma in `GroupScheme/Rational/SplitUnipotentStableCenter`, with the commutator
notation unfolded. Both retain the same centrality hypothesis.

## Local lifting of several quotient points

The published `AutomorphicAction.hom_ext_of_local_quotient_lift` (module
`GroupScheme/ActionDescent`) says the following for a quasi-compact, flat, surjective `π`.
Two maps `f, f' : T ⟶ Y` out of a test scheme agree if they agree after every base change
`b : V ⟶ T` along which a given quotient point `x : T ⟶ G` lifts to `C`.
`hom_ext_of_local_quotient_lift₂` and `hom_ext_of_local_quotient_lift₃` iterate it, so
that two or three quotient points lift simultaneously.

## Properties of the descended commutator

For a central kernel (`hπ`) and `T`-points `x, y` of `G`, write `⟨x, y⟩` for
`lift x y ≫ hom π hπ : T ⟶ C`.

- `lift_hom_naturality`: `b ≫ ⟨x, y⟩ = ⟨b ≫ x, b ≫ y⟩` for every `b : T' ⟶ T`.
- `lift_hom_of_eq`: if `x = π g` and `y = π h`, then `⟨x, y⟩ = g h g⁻¹ h⁻¹`. This is the
  published `lift_hom`.
- `lift_one_hom`, `lift_hom_one`, `lift_self_hom`: `⟨1, y⟩ = ⟨x, 1⟩ = ⟨x, x⟩ = 1`.
- `lift_swap_hom`: `⟨y, x⟩ = ⟨x, y⟩⁻¹`.
- `lift_hom_act`: take an action `a` of a group scheme `H` on `C` by automorphisms and an
  action `b` of `H` on `G` (structure `AutomorphicAction`). Suppose they are compatible,
  `b.act h (π g) = π (a.act h g)` on all points. Then
  `⟨b.act h x, b.act h y⟩ = a.act h ⟨x, y⟩`.

Each proof lifts the points involved locally and applies `lift_hom` together with the
corresponding group identity. For `lift_hom_act`, it also uses the facts that `a.act h`
is multiplicative and preserves inverses.

## Commutative quotient

From here on there is an additional hypothesis
`hG : ∀ (T : Over S) (x y : T ⟶ G.X), Commute x y`.

- `lift_hom_comp`: `⟨x, y⟩ ≫ π = 1`. By the published `hom_comp`, the left side is the
  commutator of `x` and `y` in `G`, which is trivial.
- `lift_hom_mem_range_kernelι`: `⟨x, y⟩` lies in the range of the actual kernel inclusion
  `kernelι π`. This uses the published `mem_range_kernelι_iff`.
- `lift_hom_commute`: `⟨x, y⟩` commutes with every `T`-point of `C`. It lies in the kernel,
  and the kernel is central.
- `lift_mul_hom`, `lift_hom_mul`: `⟨x x', y⟩ = ⟨x, y⟩⟨x', y⟩` and
  `⟨x, y y'⟩ = ⟨x, y⟩⟨x, y'⟩`. All three points are lifted locally. The commutators of
  the lifts are central by `lift_hom_commute`, and the group lemmas above apply.

## The pairing

Now let `κ : K ⟶ C` be a homomorphism that represents the range of the kernel inclusion
(`hκ : (SubgroupFunctor.range (kernelι π)).IsRepresentedBy κ`). That is, `κ` is a
monomorphism over `S`, and its points are exactly the points of `C` killed by `π`. The
actual kernel always qualifies (`isRepresentedBy_kernelι`). In applications `K` can be a
smaller model of the kernel, such as a represented root subgroup.

- `pairing π hπ hG hκ : G.X ⊗ G.X ⟶ K.X` (definition). Apply `lift_hom_mem_range_kernelι`
  to the universal pair of points `(fst, snd)`: the descended commutator `hom π hπ` is a
  point of the range of `kernelι π`. The pairing is the preimage of this point under the
  points bijection `hκ.pointsEquiv` of the representation.
- `pairing_comp`: `pairing π hπ hG hκ ≫ κ = hom π hπ`.
- `lift_pairing_comp`: `(lift x y ≫ pairing) ≫ κ = ⟨x, y⟩`.
- `lift_pairing`: for lifted points, `(lift (π g) (π h) ≫ pairing) ≫ κ = g h g⁻¹ h⁻¹`.
- `lift_pairing_naturality`: naturality in the test scheme.
- `lift_mul_pairing`, `lift_pairing_mul`: the pairing is multiplicative in each point.
  Since the points of `G` commute, it is biadditive.
- `lift_one_pairing`, `lift_pairing_one`: the pairing is trivial when one point is `1`.
- `lift_self_pairing`: the pairing is alternating.
- `lift_swap_pairing`: exchanging the points inverts the pairing.
- `lift_pairing_act`: take compatible automorphic actions `a` on `C` and `b` on `G` as in
  `lift_hom_act`, and an action `c` on `K` with `a.act h (κ l) = κ (c.act h l)`. Then
  `lift (b.act h x) (b.act h y) ≫ pairing = c.act h (lift x y ≫ pairing)`.

Each property is proved by cancelling the monomorphism `κ` and applying the corresponding
property of `⟨x, y⟩`.

## A criterion for central kernels

`isCentral_kernelι_of_commute π hN hc` states the following. Let `N` be a subgroup functor
of `C` equal to the range of `kernelι π`, and suppose every point of `N` commutes with every
point of `C` over the same test scheme. Then `IsCentral (kernelι π)`. The proof uses the
published `isCentral_kernelι_iff` and the stability of `N` under base change. This
criterion lets the pairing be applied when the kernel is known as a named subgroup functor,
for example a root subgroup.

## Provenance

No result here is an original-literature theorem. The construction is the standard
commutator pairing of a central extension with abelian quotient, in the scheme-theoretic
form needed later. It is internal infrastructure for the commutator description of
multipliable root groups. That description is the step toward the coordinates of
`RootUnitaryCoordinates` (Kaletha–Prasad, §2.9 and Construction 6.1.17), but this module
proves nothing about root groups.
