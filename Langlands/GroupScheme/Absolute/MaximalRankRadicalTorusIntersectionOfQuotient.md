# Radical torus intersections from the solvable torus quotient

Worker 1496. This module proves `MaximalRankRadicalTorusIntersectionStatement`
from one premise, the published but unproved `SolvableTorusQuotientStatement`
(Milne 2017, Theorem 16.33(a), (c)). That premise stays an explicit hypothesis
of the final theorem. The module does not prove the target unconditionally,
and it does not complete the proof task for the target. Once
`SolvableTorusQuotientStatement` has a proof, applying the final theorem to it
proves the target with no premise.

Compared with `maximalRankRadicalTorusIntersectionStatement_of_complement` in
`Absolute/MaximalRankRadicalTorusIntersectionOfComplement`, this module
removes the conjugacy premise `MaximalTorusConjugacyStatement`. The closed
unipotent subgroup and torus splitting premises are replaced by their Library
proofs. The decomposition premise `hcomp` is derived from
`SolvableTorusQuotientStatement`. Maximal tori are compared only inside the
solvable subgroup `P = R · T` of `H`, where conjugacy follows from the
published conditional theorem `maximalToriAreConjugate_of_solvableTorusQuotient`.

## Declarations

Throughout, `k` is a field and all group schemes are over `Spec k`.

- `SubgroupFunctor.smoothConnectedProduct i j hi hj hn` and
  `SubgroupFunctor.smoothConnectedProductι i j hi hj hn`. Let `G` be affine and
  locally of finite type. Let `i : H ⟶ G` and `j : N ⟶ G` be smooth connected
  closed subgroups with the range of `i` normalized by the range of `j`. These
  are a chosen group scheme `P` and a map `P ⟶ G`, the witnesses of the Library
  theorem `SubgroupFunctor.exists_smoothConnected_fppfProduct`. They are chosen
  by `Classical.choose`, so nothing beyond that theorem's conclusion is known
  about them.
- `SubgroupFunctor.smoothConnectedProductι_spec`: the chosen map represents the
  fppf-local product `range i · range j` (`IsFppfProduct`), and `P` is smooth
  and connected.
- `SubgroupFunctor.IsFppfProduct.exists_mul_of_rationalPoint`, over an
  algebraically closed field. Suppose `p : P ⟶ G` represents the fppf-local
  product of `F` and `N`. Then every rational point `x` of `G` in the range of
  `p` is a product `x = a * b`, where `a` and `b` are rational points in `F`
  and `N`.
- `SubgroupFunctor.IsFppfProduct.isSolvableGroupScheme`, over an algebraically
  closed field. Suppose `p` represents the fppf-local product of `range r` and
  `range n`, where `range r` is normal and `R` and `N` are solvable. Then `P` is
  solvable.
- `maximalRankRadicalTorusIntersectionStatement_of_solvableTorusQuotient`:
  `SolvableTorusQuotientStatement.{u} → MaximalRankRadicalTorusIntersectionStatement.{u}`.

## Rational points of a represented product

Let `x` be a rational point in the range of `p`. By the definition of
`IsFppfProduct`, there is a test scheme `V` with a flat, surjective map
`v : V ⟶ Spec k` locally of finite presentation, together with
`a ∈ F(V)` and `b ∈ N(V)` such that `v ≫ x = a * b`. Since `k` is algebraically
closed and `V` is nonempty and locally of finite type over `k`, the Library
lemma `exists_point_lift_of_locallyOfFiniteType_surjective` gives a rational
point `e` of `V` with `e ≫ v = 𝟙`. Then `x = e ≫ v ≫ x = (e ≫ a) * (e ≫ b)`
by `MonObj.comp_mul`. The two factors lie in `F` and `N` because subgroup
functors are stable under pullback.

## Solvability of the product

`isSolvableGroupScheme_iff_rationalPoints` reduces solvability of `R`, `N` and
`P` to solvability of their groups of rational points. Composition with `r`,
`n` and `p` gives group homomorphisms `R(k) → G(k)`, `N(k) → G(k)` and
`P(k) → G(k)` (`IsMonHom.monoidHom`). Let `A` and `B` be the images of the first
two. They are solvable as images of solvable groups, and `A` is normal because
`range r` is normal. So `A ⊔ B` is solvable by the Library lemma
`isSolvable_sup_of_normal`. By the previous section, the image of `P(k)` lies
in `A ⊔ B`. Since `p` is a closed immersion, hence a monomorphism, `P(k)` embeds
into `A ⊔ B` and is solvable.

## The main theorem

Fix the data of `MaximalRankRadicalTorusIntersectionStatement`: `G` connected
reductive over the algebraically closed field `k`, a smooth connected closed
subgroup `j : H ⟶ G`, a maximal torus `t : T ⟶ G` with `f ≫ j = t`, and a
solvable radical `r : R ⟶ H`.

1. `f` is a maximal torus of `H`, by `IsMaximalTorus.of_comp`. Since `range r`
   is normal in `H`, it is normalized by `range f`.
2. Let `p : P ⟶ H` be `smoothConnectedProductι r f`, so `P` represents
   `range r · range f` and is smooth and connected. Both factors lie in the
   product. `IsRepresentedBy.factorHom` gives `r' : R ⟶ P` and `f' : T ⟶ P`
   with `r' ≫ p = r` and `f' ≫ p = f`.
3. `f'` is a maximal torus of `P` and `r'` is a closed subgroup of `P`, both by
   the `of_comp` lemmas along the closed subgroup `p`. The range of `r'` is
   normal in `P`: conjugating a point of `r'` by a point of `P` and composing
   with `p` gives a conjugate point of `r` in `H`, and `p` is a monomorphism.
4. `P` is solvable, by `IsFppfProduct.isSolvableGroupScheme` with `R` solvable
   (part of `IsSolvableRadical`) and `T` commutative.
5. The term `solvableSplitExtension_of_oneDimensional perfectFieldOneDimensionalUnipotent`,
   from the companion module `Absolute/SolvableSplitExtensionOneDimensional`,
   proves `SolvableSplitExtensionStatement` with no premise. With the premise
   `hquot`, `maximalToriAreConjugate_of_solvableTorusQuotient` gives
   `MaximalToriAreConjugate P`.
6. The Library theorem `exists_radicalTorusIntersection_of_complement` applies
   inside `P`, to `f'` and `r'`. Its inputs are the following. Closed subgroups
   of unipotent groups are unipotent (the proved `unipotentClosedSubgroup`).
   `T` is split, by `IsTorus.isSplitTorus_of_finiteGaloisSplitting` with the
   proved `torusFiniteGaloisSplitting`. For every maximal torus `s` of the
   smooth connected solvable group `R`, there is a closed unipotent `u : U ⟶ R`
   with `subgroupMultiplication u s` an isomorphism. This last input comes from
   `solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient hquot`
   with the same split-extension proof. The theorem gives `S`, a closed
   `sT : S ⟶ T`, a maximal torus `sR : S ⟶ R` with `sT ≫ f' = sR ≫ r'`, and
   `range (sT ≫ f') = range f' ⊓ range r'`.
7. Composing with `p` gives `sT ≫ f = sR ≫ r`. The range equality transports
   along `p`. If `y ≫ f = z ≫ r` on a test scheme, then `y ≫ f' = z ≫ r'`
   because `p` is a monomorphism, so `y ≫ f'` lies in `range (sT ≫ f')`.
   Composing back with `p` puts the common point in `range (sT ≫ f)`. The
   reverse inclusion follows from `sT ≫ f = sR ≫ r`.

The axioms are `propext`, `Classical.choice` and `Quot.sound`. The proof uses
neither `MaximalTorusConjugacyStatement` nor `BorelConjugacyStatement`.

## Provenance

The target statement is the derived formulation of the maximum-rank argument
of Borel and Tits (1965), described in its own Markdown. The route here is an
internal reduction and does not follow a single source proof. It uses the
following standard facts:

- the product of a normal subgroup and a subgroup normalizing it (here the
  Library theorem `exists_smoothConnected_fppfProduct`);
- solvability of an extension of solvable groups, applied to rational points
  over an algebraically closed field;
- conjugacy of maximal tori in a smooth connected solvable group over an
  algebraically closed field (Milne 2017, Theorem 16.27(b), printed p.333),
  through the published conditional theorem
  `maximalToriAreConjugate_of_solvableTorusQuotient`;
- the decomposition `R = R_u ⋊ S` of a smooth connected solvable group (Milne
  2017, Theorem 16.33(d), printed pp.335–336), through
  `solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient`.

The source is Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`.
