# Torus complements in solvable groups from a section of the torus quotient

This module proves Milne 2017, Theorem 16.33(d), `H = H_u ⋊ T`, in the form
`SolvableMaximalTorusSemidirectStatement`. The proof is conditional on five published
proposition targets, which appear as explicit hypotheses:

- `SolvableTorusQuotientStatement`: a smooth connected solvable group has a split torus
  quotient by a smooth connected normal unipotent closed subgroup (Milne 16.33(a)–(c)).
- `SolvableSplitExtensionStatement`: that quotient has a homomorphic section
  (Milne 16.26(a)).
- `SolvableMaximalTorusConjugacyStatement`: two maximal tori of a smooth connected solvable
  group are conjugate by a rational point.
- `UnipotentClosedSubgroupStatement`: closed subgroups of affine unipotent groups of finite
  type are unipotent (Milne 14.7).
- `TorusFiniteGaloisSplittingStatement`: every torus splits over a finite Galois extension.
  Over an algebraically closed field this makes every torus split
  (`IsTorus.isSplitTorus_of_finiteGaloisSplitting`, module `Torus/SplitReflection`).

The module also contains one definition and several lemmas over an arbitrary base.

## Split tori as commutative group schemes

Let `S` be a scheme and `D` a group scheme over `S` with `hD : IsSplitTorus D`.

- `IsSplitTorus.toCommGroupScheme` (definition): `D` regarded as a commutative group scheme
  over `S`, using the Library's `IsSplitTorus.isCommMonObj`. `toCommGroupScheme_toGrp` says
  its underlying group scheme is `D` (by `rfl`). It is used to pass `D` to
  `exists_maximalTorus_extension_of_finiteType`, which takes a commutative source.
- `IsSplitTorus.points_mul_comm`: points `x`, `y : T ⟶ D.X` over any `T` commute. Transport
  along the isomorphism with `𝔾_m^I` (`isoPointsEquiv`) and use commutativity there.
- `IsSplitTorus.innerIso_hom`: the inner automorphism of `D` by any section `g` of `D` over
  `S` is the identity.
- `innerIso_hom_comp_of_isSplitTorus`: for a homomorphism `q : H ⟶ D` and a section `g` of
  `H` over `S`, `(H.innerIso g).hom ≫ q = q`. By the Library's `innerIso_hom_comp`, the left
  side is `q` followed by the inner automorphism of `D` by `g ≫ q`, which is trivial.

## Lemmas over a field

Let `k` be a field and `𝕊 = Spec k`. All group schemes below are over `𝕊`.

- `range_le_of_isUnipotent_of_isSplitTorus`: let `q : H ⟶ D` have split torus target, and
  suppose the scheme kernel of `q` has the points of `i : U ⟶ H` on every test scheme
  (`SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i`). Then for every unipotent
  `W` and every homomorphism `w : W ⟶ H`, `range w ≤ range i`. Indeed `w ≫ q` is trivial
  (`IsUnipotent.comp_eq_one_of_isSplitTorus`, module `Torus/UnipotentHom`), so every point of
  `W` lands in the kernel of `q`.
- `range_inf_eq_bot_of_isSplitTorus_of_isUnipotent`: assume
  `UnipotentClosedSubgroupStatement`. Let `t : T ⟶ H` be a closed subgroup with `T` a split
  torus, and let `i : U ⟶ H` be a homomorphism from an affine unipotent group locally of
  finite type. Then `range t ⊓ range i = ⊥` on every test scheme. The scheme intersection
  `subgroupIntersection t i` (module `SubgroupIntersection`) is a closed subgroup of `U`,
  being a pullback of the closed immersion `t`. It is therefore unipotent. Its map to the
  split torus `T` is thus trivial, so every point in both ranges is `1`.
- `IsClosedSubgroup.of_comp_eq_id`: if `H` is separated over `𝕊` and `σ ≫ q = 𝟙 D`, then `σ`
  is a closed subgroup. `q` is separated because `H` is, and `σ ≫ q` is the identity, a closed
  immersion; so `σ` is a closed immersion (`IsClosedImmersion.of_comp`).

Now let `H` be smooth, affine and connected over `𝕊`, with `k` algebraically closed and `H`
solvable. Let `i : U ⟶ H` be a closed subgroup with `U` unipotent, and let `q : H ⟶ D` be a
homomorphism onto a split torus whose scheme kernel has the points of `i`. Let `σ : D ⟶ H`
satisfy `σ ≫ q = 𝟙 D`.

- `isIso_comp_of_section`: assume conjugacy of maximal tori in solvable groups,
  `UnipotentClosedSubgroupStatement` and `TorusFiniteGaloisSplittingStatement`. Then for every
  maximal torus `s : T ⟶ H`, `s ≫ q` is an isomorphism of group schemes. The proof:
  1. `σ` is a closed subgroup with split torus source, so it factors as `a ≫ t₀` through a
     maximal torus `t₀ : T₀ ⟶ H` (`exists_maximalTorus_extension_of_finiteType`, module
     `Rational/MaximalTorusFiniteType`).
  2. `T₀` is split, so `range t₀ ⊓ range i = ⊥` by the lemma above. Hence `t₀ ≫ q` is a
     monomorphism (`mono_comp_of_inf_eq_bot`, module `Absolute/SolvableComplementOfQuotient`).
  3. `a ≫ (t₀ ≫ q) = σ ≫ q = 𝟙 D`, so `t₀ ≫ q` is a split epimorphism, hence an isomorphism.
  4. By conjugacy there are a rational point `g` of `H` and an isomorphism `e : T ≅ T₀` with
     `s ≫ inner(g) = e ≫ t₀`. Since `inner(g) ≫ q = q`, we get `s ≫ q = e ≫ t₀ ≫ q`, an
     isomorphism.
- `isIso_subgroupMultiplication_of_section`: under the same hypotheses, the multiplication
  `subgroupMultiplication i s : U ⊗ T ⟶ H`, `(v, t) ↦ i(v) s(t)`, is an isomorphism of
  schemes. `isIso_subgroupMultiplication_of_isIso_comp` (module
  `Absolute/SolvableComplementOfQuotient`) gives the isomorphism in the order `T × U`. The
  Library's `isIso_subgroupMultiplication_reverse_iff` (module `Rational/LeviMultiplication`)
  converts it to the order `U × T`.

## The main theorem

`solvableMaximalTorusSemidirectStatement_of_section`: the five hypotheses listed at the top
imply `SolvableMaximalTorusSemidirectStatement`. Given `k`, `H` and a maximal torus
`s : T ⟶ H`, `SolvableTorusQuotientStatement` supplies `U`, `D`, `i`, `q` with `i` a smooth
connected unipotent closed subgroup with normal range and `q` a fppf quotient by
`range i` onto a split torus. The kernel condition in `IsFppfQuotient` is the hypothesis
`range (kernelι q) = range i` used above. `SolvableSplitExtensionStatement` supplies the
section `σ`. The witness for the statement is `(U, i)`: the first five conditions come from
the quotient, containment of every unipotent closed subgroup comes from
`range_le_of_isUnipotent_of_isSplitTorus`, and the multiplication isomorphism comes from
`isIso_subgroupMultiplication_of_section`.

## Provenance

The target is Milne 2017, Theorem 16.33(d) (printed p. 336, zero-based PDF page 351). For a
maximal torus `T` of a smooth connected solvable group `G` over an algebraically closed field,
Milne's proof uses Theorem 16.27 (printed p. 333, PDF page 348) to show that the quotient map
`G ⟶ G/G_u` restricts to an isomorphism `T ≅ G/G_u`, and then Proposition 2.34 (printed p. 50,
PDF page 65) to conclude `G ≅ G_u ⋊ T`. Theorem 16.27(b) shows that the maximal diagonalizable
subgroups are the images `s(D)` of sections `s` of `q`, all conjugate. This module follows the
same outline with a different split of the inputs. The section comes from
`SolvableSplitExtensionStatement` (Milne 16.26(a)). The image of the section is extended to a
maximal torus `T₀`, and `T₀ ⟶ G/G_u` is shown to be an isomorphism directly (steps 1–3 above).
An arbitrary maximal torus is then moved onto `T₀` with the separate conjugacy statement for
maximal tori in solvable groups, in place of Theorem 16.27. The containment of unipotent
subgroups in `G_u` is Milne 16.33(b); here it is derived from the triviality of homomorphisms
from unipotent groups to split tori. The lemmas over an arbitrary base and the
commutative-group packaging of split tori are derived helpers specific to this formalization.
