# Isogenies of split reductive groups are determined by the torus and the simple root groups: proof

The theorem `Langlands.GroupScheme.splitIsogenySimpleRootRigidity` has type
exactly `SplitIsogenySimpleRootRigidityStatement.{u}`
([statement](SplitIsogenySimpleRootRigidityStatement.md)), in every universe `u`
and with no additional hypotheses. It uses only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

The statement is Milne, *Algebraic Groups* (2017), Corollary 21.63. Let `k` be
a field, let `(G, T)` and `(G', T')` be split connected reductive groups over
`k` with split maximal tori `i : T ⟶ G` and `i' : T' ⟶ G'`, and let `ν` be a
generic cocharacter of `T`. Let `φ₁ φ₂ : G ⟶ G'` be isogenies of split
reductive groups with `i ≫ φ₁ = i ≫ φ₂` that agree on every point, over every
test scheme, of `RelativeRoot.subgroup i α` for every
`α ∈ simpleRelativeRoots i ν`. Then `φ₁ = φ₂`.

The proof uses neither the isogeny conditions on `φ₁` and `φ₂` (surjectivity,
finite kernel, `T` mapped into `T'`) nor the torus `i'`. It uses only that `G`
and `G'` are connected reductive, that `i` is a split maximal torus, that `ν`
is generic, and the two agreement hypotheses.

## Helper declarations

All helpers are in the namespace
`Langlands.GroupScheme.SplitIsogenySimpleRootRigidity`.

- `homEqualizerSubgroup f g`: for homomorphisms `f g : G ⟶ H` of group schemes
  over any scheme `B`, the subgroup functor of `G` whose points over a test
  scheme `T` are the `x : T ⟶ G.X` with `x ≫ f.hom.hom = x ≫ g.hom.hom`. The
  identity, products and inverses of such points are again such points, because
  `f` and `g` preserve them (`MonObj.one_comp`, `MonObj.mul_comp`,
  `GrpObj.inv_comp`). Restriction along a map of test schemes preserves the
  condition. `mem_homEqualizerSubgroup` restates membership.
- `mem_homEqualizerSubgroup_iff_factors`: a point lies in
  `homEqualizerSubgroup f g` exactly when it factors through the equalizer, in
  schemes over `B`, of `f.hom.hom` and `g.hom.hom`. This follows from
  `equalizer.lift` and `equalizer.condition`.
- `homEqualizerSubgroup_isClosedRepresentable`: if `H` is separated over `B`,
  then `homEqualizerSubgroup f g` is represented by a closed subgroup of `G`.
  The equalizer inclusion is a closed immersion (Mathlib's
  `isClosedImmersion_equalizer_ι_left`), and
  `SubgroupFunctor.isClosedRepresentable_of_scheme` transfers the group
  structure to it.
- `range_le_homEqualizerSubgroup_iff f g j`: for a homomorphism `j : K ⟶ G`,
  the range of `j` lies in `homEqualizerSubgroup f g` exactly when
  `j ≫ f = j ≫ g`. The forward direction applies the containment to every
  point of `K` and uses `hom_ext_points`. The reverse direction composes the
  equality with each point.
- `eq_of_isAlgClosed`: the theorem over an algebraically closed field, for any
  two homomorphisms `φ₁ φ₂ : G ⟶ G'` between connected reductive groups. Its
  hypotheses are a split maximal torus `i` of `G`, a generic cocharacter `ν`,
  `i ≫ φ₁ = i ≫ φ₂`, and
  `RelativeRoot.subgroup i α ≤ homEqualizerSubgroup φ₁ φ₂` for every simple
  root `α`.
- `exists_simpleRelativeRoot_of_baseChange`: let `T` be a split torus with
  `i : T ⟶ G` (`G` affine and locally of finite type), let `K/k` be a field
  extension and write `b : Spec K ⟶ Spec k`. Every simple root of
  `i_K = (GroupScheme.baseChange b).map i` for the cocharacter
  `cocharacterLattice.baseChange b T ν` is
  `characterLattice.baseChange b T α` for a simple root `α` of `i` for `ν`.

## The algebraically closed case

`eq_of_isAlgClosed` proceeds as follows. Write `χ` for the cocharacter
`CommGroupScheme.groupHom ν ≫ i` of `G`.

1. **The agreement subgroup.** `G'` is affine, hence separated, so
   `homEqualizerSubgroup_isClosedRepresentable` gives a closed subgroup
   `q : E ⟶ G` whose range is `homEqualizerSubgroup φ₁ φ₂`.
2. **The unipotent subgroup `U(χ)`.** `rootDatumExistence` gives a root datum
   `P` with `IsRootDatumOf i P`. Since the range of `q` contains the root
   subgroup of every simple root, `LeviGluing.unipotent_le_range_of_simpleRoots`
   shows that it contains `Dynamic.unipotent χ`. This is the step that needs
   `k` algebraically closed.
3. **The centralizer `Z(χ)`.** `centralizer_comp_eq_range_of_isRegular` shows
   that `Dynamic.centralizer χ` is the range of `i`. A regular cocharacter in
   the sense of that theorem is a generic one: both say that every root pairs
   nonzero with `ν`. The range of `i` lies in the agreement subgroup by
   `range_le_homEqualizerSubgroup_iff` and `i ≫ φ₁ = i ≫ φ₂`.
4. **The parabolic `P(χ)`.** Every point of `Dynamic.parabolic χ` is a product
   of a point of the centralizer and a point of the unipotent subgroup, so
   `Dynamic.parabolic_le_of_centralizer_le_of_unipotent_le` puts
   `Dynamic.parabolic χ` in the agreement subgroup.
5. **A Borel subgroup.** `Dynamic.Affine.parabolicHom χ` is a closed subgroup
   (`Dynamic.Affine.isClosedSubgroup_parabolicHom`) representing
   `Dynamic.parabolic χ` (`Dynamic.Affine.isRepresentedBy_parabolicHom`). By
   the first clause of `regularCocharacterBorel` it is a Borel subgroup of
   `G`. By step 4 and `range_le_homEqualizerSubgroup_iff`,
   `Dynamic.Affine.parabolicHom χ ≫ φ₁ = Dynamic.Affine.parabolicHom χ ≫ φ₂`.
6. **Borel rigidity.** `borelHomomorphismRigidity` (Milne 17.21) is applied
   with the `k`-algebra `R = k`. It shows that the base changes of `φ₁` and
   `φ₂` along `Spec.map (CommRingCat.ofHom (algebraMap k k))` are equal; the
   hypothesis on the Borel subgroup is the image of the equality of step 5
   under the base-change functor. This base map is the identity of `Spec k`
   (`Algebra.algebraMap_self`, `CommRingCat.ofHom_id`, `Spec.map_id`), hence
   an isomorphism, and
   `LocallyNoetherianHomEquality.baseChange_hom_ext_of_isIso` gives
   `φ₁ = φ₂`.

## The main theorem

`splitIsogenySimpleRootRigidity` passes to `K = AlgebraicClosure k`, with
`b = Spec.map (CommRingCat.ofHom (algebraMap k K))`.

1. **Hypotheses over `K`.** `G_K` and `G'_K` are connected reductive
   (`connectedReductiveFieldExtensionStatement`). `T_K` is split
   (`IsSplitTorus.baseChange`). `i_K` is a maximal torus (the forward
   direction of `maximalTorusBaseChange`, Milne 17.82). The cocharacter
   `ν_K = cocharacterLattice.baseChange b T ν` is generic: every character of
   `T_K` is `characterLattice.baseChange b T α` for a character `α` of `T`
   (`IsSplitTorus.characterLattice_baseChange_bijective`), it is a root of
   `i_K` exactly when `α` is a root of `i` (`mem_roots_baseChange_iff`), and
   the pairing is unchanged (`latticePairing_baseChange`). The equality
   `i_K ≫ φ₁_K = i_K ≫ φ₂_K` is the image of `i ≫ φ₁ = i ≫ φ₂` under the
   base-change functor.
2. **Simple roots.** `exists_simpleRelativeRoot_of_baseChange` uses the same
   three facts. The positivity of a root and the decomposition of a root as a
   sum of two positive roots correspond on both sides, since
   `characterLattice.baseChange b T` is additive.
3. **Simple root subgroups.** For a simple root `α` of `i`,
   `RelativeRoot.subgroup_baseChange` identifies
   `RelativeRoot.subgroup i_K (characterLattice.baseChange b T α)` with the
   base change of `RelativeRoot.subgroup i α`. A point `x` of the latter over a
   `K`-scheme `T'` corresponds to the point `baseChangePointsEquiv b G T' x` of
   `RelativeRoot.subgroup i α` over `T'` regarded as a `k`-scheme
   (`SubgroupFunctor.mem_baseChange`). By hypothesis `φ₁` and `φ₂` agree on it.
   By `baseChangePointsEquiv_comp` this says that `x ≫ φ₁_K` and `x ≫ φ₂_K`
   have the same image under the bijection `baseChangePointsEquiv b G' T'`,
   so they are equal.
4. **Descent.** `eq_of_isAlgClosed` gives `φ₁_K = φ₂_K`. The map `b` is the
   spectrum of an injective ring map, hence scheme-theoretically dominant
   (`isSchemeTheoreticallyDominant_specMap`), and it is quasi-compact
   (`fieldExtension_fpqc`). `G` is smooth, hence flat, and `G'` is affine,
   hence separated, so `SchematicHomEquality.baseChange_hom_ext` gives
   `φ₁ = φ₂`.

## Relation to the literature

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over
a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, Corollary 21.63, printed p.443. Milne's proof
reads: "As φ₁ and φ₂ agree on the Borel subgroup U_α·T of G_α, they agree on
G_α (see 17.21), and these groups generated G (see 21.62)."

The Lean proof follows a different route to the same conclusion. It applies
Borel rigidity (17.21) once, to the Borel subgroup `P(χ)` of `G` itself rather
than to the rank-one subgroups `G_α`. The agreement on `P(χ) = Z(χ)·U(χ)` comes
from the agreement on `T = Z(χ)` and from the fact that a closed subgroup
containing the simple root subgroups contains `U(χ)`. That fact is the
Library's `LeviGluing.unipotent_le_range_of_simpleRoots`, proved over an
algebraically closed field; in this proof it takes the place of the generation
statement 21.62 in Milne's argument. The Library's
`borelHomomorphismRigidity` and `unipotent_le_range_of_simpleRoots` are stated
over algebraically closed fields, so the proof passes to an algebraic closure
and descends the equality along the scheme-theoretically dominant map
`Spec k̄ → Spec k`.
