# Borel subgroups through a maximal torus over an algebraically closed field

Module `Langlands.GroupScheme.Absolute.BorelDynamicConjugacy`. It is derived infrastructure for
clause 3 of `Langlands.GroupScheme.RegularCocharacterBorelStatement` (task
`618cd683-cfcd-43a3-b4bf-6c8abd208b1f`). The main theorem is conditional: it takes the
published `BorelConjugacyStatement` and `MaximalTorusConjugacyStatement` as hypotheses and does
not prove them.

## Contents

### Ranges under isomorphisms

- `SubgroupFunctor.range_iso_comp`: for an isomorphism `e : H' ≅ H` and any `i : H ⟶ G`, the
  points of `e.hom ≫ i` and of `i` agree on every test scheme.
- `range_comp_iso_eq_parabolic`: if `i : H ⟶ G` is a monomorphism whose points are the dynamic
  parabolic `P(χ)` on every test scheme, then for every automorphism `e` of `G` the points of
  `i ≫ e.hom` are `P(χ ≫ e.hom)`. The proof transports the representation along `e`
  (`SubgroupFunctor.IsRepresentedBy.comp_iso`) and uses `Dynamic.parabolic_eq_comap_of_iso`.

### Dynamic parabolics of a torus

- `IsTorusDynamicParabolic j i` (definition), for a homomorphism `j : T ⟶ G` from a commutative
  group scheme `T` over any base scheme and a homomorphism `i : B ⟶ G`: there is a cocharacter
  `ν : cocharacterLattice T` (a homomorphism `𝔾_m ⟶ T`) such that `i` represents the dynamic
  parabolic subgroup functor `Dynamic.parabolic (groupHom ν ≫ j)`. Representing means that `i` is
  a monomorphism and that its points are exactly `P_G(ν ≫ j)` on every test scheme. When `T` is a
  torus this says that `i` is the subgroup Milne writes `P(λ)` for a cocharacter `λ` of `T`.
- `IsTorusDynamicParabolic.exists_comp_eq`: if `IsTorusDynamicParabolic j i`, then `j` factors
  through `i`. Reason: the image of a commutative group scheme lies in the dynamic parabolic of
  each of its cocharacters (`range_le_dynamicParabolic`), and a representing monomorphism lifts every
  homomorphism whose points lie in the functor (`SubgroupFunctor.IsRepresentedBy.factorHom`).

### Borel subgroups through a maximal torus

`exists_isRepresentedBy_parabolic_of_isBorelSubgroup`. Hypotheses:

- `hBC : BorelConjugacyStatement` and `hTC : MaximalTorusConjugacyStatement`;
- `K` an algebraically closed field and `G` a smooth affine group over `K` with connected
  underlying space;
- `j : T ⟶ G` a maximal torus and `ν₀` a cocharacter of `T`;
- a Borel subgroup `i₀ : P₀ ⟶ G` representing `Dynamic.parabolic (groupHom ν₀ ≫ j)`;
- a Borel subgroup `i : B ⟶ G` and `f : T ⟶ B` with `f ≫ i = j`.

Conclusion: there is an automorphism `σ` of `T` such that `i` represents
`Dynamic.parabolic (groupHom (ν₀ ≫ σ.hom) ≫ j)`. The cocharacter `ν₀ ≫ σ.hom` is the image of
`ν₀` under the automorphism `σ` of `T`.

Proof:

1. `hBC` gives `g ∈ G(K)` and an isomorphism `φ : P₀ ≅ B` with `i₀ ≫ int(g) = φ ≫ i`. By the
   two range lemmas, the points of `i` are `P((ν₀ ≫ j) ≫ int(g))`.
2. `j` factors through `i₀` by `f₀`, because a commutative subgroup lies in the dynamic
   parabolic of each of its cocharacters (`range_le_dynamicParabolic` and
   `SubgroupFunctor.IsRepresentedBy.factorHom`). Then `(f₀ ≫ φ) ≫ i = j ≫ int(g)`.
3. `f` and `f₀ ≫ φ` are maximal tori of `B`, by the Library lemma `IsMaximalTorus.of_comp`
   (`Torus.MaximalTransport`), applied to `j` and to `j ≫ int(g)` (`IsMaximalTorus.comp_iso`,
   same module). `B` is smooth and connected as a Borel
   subgroup, and affine as a closed subgroup of an affine group.
4. `hTC`, applied inside `B`, gives `b ∈ B(K)` and `σ : T ≅ T` with
   `(f₀ ≫ φ) ≫ int_B(b) = σ ≫ f`. Inner automorphisms commute with homomorphisms
   (`innerIso_hom_comp`), so `(j ≫ int(g)) ≫ int(i(b)) = σ ≫ j`.
5. Conjugation by `i(b)` preserves the points of `i`, because `int(i(b))` restricts to the
   automorphism `int_B(b)` of `B`. Hence the points of `i` are
   `P((ν₀ ≫ j) ≫ int(g) ≫ int(i(b))) = P((ν₀ ≫ σ) ≫ j)`. Since `i` is a closed immersion, it
   is a monomorphism, and so it represents this functor.

`IsTorusDynamicParabolic.of_isBorelSubgroup`: same setting (`hBC`, `hTC`, `K` algebraically
closed, `G` smooth affine connected, `j` a maximal torus). If some Borel subgroup `i₀` satisfies
`IsTorusDynamicParabolic j i₀`, then every Borel subgroup `i : B ⟶ G` through which `j` factors
(`f ≫ i = j`) satisfies `IsTorusDynamicParabolic j i`. The proof applies
`exists_isRepresentedBy_parabolic_of_isBorelSubgroup` and uses the cocharacter `ν₀ ≫ σ.hom`.

## Provenance

This is the algebraically closed case of the surjectivity part of Milne, *Algebraic Groups*
(2017), Theorem 21.32 (statement printed p.434, PDF p.450; proof printed pp.434–435, PDF
pp.450–451). Milne takes a regular `λ`, writes `B = n P(λ) n⁻¹` with `n ∈ N_G(T)(k)` by
Corollary 17.11 (printed p.355, PDF p.371), and concludes `B = P(w⁻¹(λ))`. The proof of 17.11
conjugates `B` onto `P(λ)` by Theorem 17.9(b) and then moves the two maximal tori of `B` onto
each other by Theorem 17.10.

The predicate `IsTorusDynamicParabolic` is internal: it names the property "`B = P(λ)` for some
cocharacter `λ` of `T`" that appears in the statement of Theorem 21.32, phrased with the
published dynamic parabolic subgroup functor `Dynamic.parabolic` and with
`SubgroupFunctor.IsRepresentedBy`. It is defined for every base scheme, but this module uses it
only over an algebraically closed field.

The Lean proof follows the same steps with these changes:

- Milne's Lie-algebra computation of `n P(λ) n⁻¹` is replaced by transport of the dynamic
  parabolic subgroup functor along the inner automorphism (`Dynamic.parabolic_eq_comap_of_iso`).
- The torus conjugacy inside `B` is applied to the actual homomorphisms `f` and `f₀ ≫ φ`, and
  the resulting automorphism `σ` of `T` plays the role of the Weyl group element.
- Regularity of `ν₀` is not used and is not concluded. The given Borel subgroup `i₀` of the
  form `P(ν₀ ≫ j)` replaces Milne's Proposition 21.29.

Range transport reuses `SubgroupFunctor.range_iso_comp` from the common
`GroupScheme/SubgroupFunctor` module; the published normalizer construction
uses the same declaration.
