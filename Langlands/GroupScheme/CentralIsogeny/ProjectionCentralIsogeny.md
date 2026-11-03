# Projections of closed subgroups of fibre-compatible products

Author: Worker 1224. This is supporting material for task
`569a2d94-1d47-448e-8db3-48ecf4755ef4`, which proves the published
`Langlands.GroupScheme.CentralIsogenyCommonSemisimpleRefinement`. That proof
builds a common refinement `D` as a closed subgroup of `C × H` on which `π : C ⟶ G`
and `q : H ⟶ G` agree. This module shows that each projection from such a `D` is a
central isogeny once it is dominant. It does not prove dominance, which that proof
gets from perfectness of semisimple groups.

All groups are actual group schemes over `Spec k` for an arbitrary field `k`, in an
arbitrary universe `u`. `IsCentralIsogeny` is the Library predicate from
`CentralIsogeny/Basic`. It asks for the underlying scheme morphism to be finite, flat,
surjective and locally of finite presentation, and for the full scheme-theoretic
kernel to be central against all test schemes. The module assumes neither
reducedness of the kernel nor representability of any centre.

## Flatness of surjective homomorphisms

- `flat_of_surjective_algClosed`: over an algebraically closed field `K`, let
  `f : D ⟶ C` be a homomorphism. Suppose `D` is locally of finite type and
  quasi-compact, `C` is reduced and locally of finite type, and the underlying
  scheme morphism of `f` is surjective. Then that morphism is flat.

  *Proof.* Let `D` act on `C` by left translation through `f`. This is
  `SchemeAction.restrict (ModObj.regular C.X) f`, and on points it sends `(g, c)`
  to `(g ≫ f) * c`. Its orbit map through the identity `1` of `C` is `f` itself.
  The action is transitive on rational points. Take a rational point `y` of `C`,
  with image the closed point `c`. Surjectivity gives a point of `D` over `c`. The
  fibre over `c` is a nonempty locally closed subset of the Jacobson space of `D`,
  so it contains a closed point `d'`. A closed point of a scheme locally of finite
  type over an algebraically closed field is a rational point
  (`pointOfClosedPoint`). Two rational points of `C` with the same closed-point
  image are equal (`ext_of_apply_closedPoint_eq`), so `d'` maps to `y`. The
  published `orbitMapFaithfullyFlat` then gives flatness of the orbit map, that
  is, of `f`.

- `flat_of_surjective`: over an arbitrary field `k`, let `f : D ⟶ C` be a
  homomorphism with `D` locally of finite type and quasi-compact, `C` smooth, and
  the underlying morphism of `f` surjective. Then that morphism is flat.

  *Proof.* Base change along `Spec` of the algebraic closure `k → k̄`
  (`toAlgebraicClosure`). The base-changed square is a pullback
  (`baseChange_map_isPullback`, from `CentralIsogeny/FpqcReflection`). Hence the
  base-changed homomorphism is surjective, its source is locally of finite type
  and quasi-compact, and its target is smooth and therefore reduced
  (`isReduced_of_smooth_over_field`). The previous lemma gives flatness over
  `k̄`. The morphism `Spec k̄ ⟶ Spec k` is surjective, flat and quasi-compact, and
  flatness descends along such morphisms. This is the Library instance
  `descendsAlong_flat_surjective_inf_flat_inf_quasicompact` from
  `AlgebraicGeometry/Morphisms/FpqcFiniteDescent`, used with
  `MorphismProperty.of_isPullback_of_descendsAlong`.

These two lemmas are the scheme-theoretic form of Milne, *Algebraic Groups*
(2017), Proposition 1.65(a) and Proposition 1.70 (printed pp. 26 and 28, PDF
pp. 42 and 44). There, a surjective homomorphism onto a reduced algebraic group is
faithfully flat. The implemented proof follows the same orbit-map route. Here
smoothness of the target replaces reducedness, because reducedness must hold after
base change to `k̄`.

## Projections from a closed subgroup of `C × H`

Fix `C H G D : GroupScheme (Spec (CommRingCat.of k))`, `π : C ⟶ G`, `q : H ⟶ G`
and a closed subgroup `i : D ⟶ C ⊗ H` (`IsClosedSubgroup i`, so the underlying
morphism is a closed immersion). Assume the compatibility
`hcomm : i ≫ fst C H ≫ π = i ≫ snd C H ≫ q`. Here `C ⊗ H` is the cartesian
product group, whose underlying scheme is the fibre product `C ×_k H`.

- `isFinite_fst_of_closedSubgroup (hq : IsFinite q.hom.hom.left) i hi hcomm`: the
  underlying morphism of `i ≫ fst C H` is finite.

  *Proof.* By `hcomm`, the closed immersion `D ⟶ C ×_k H` factors as
  `φ : D ⟶ C ×_G H` followed by the canonical map `g : C ×_G H ⟶ C ×_k H`. The
  map `g` is a monomorphism. Since `φ ≫ g` is a closed immersion, hence finite,
  `φ` is finite (`IsFinite.of_comp`). The projection `C ×_G H ⟶ C` is a base change
  of the finite `q`, so it is finite. The projection `D ⟶ C` is `φ` followed by
  this projection.

- `isCentralIsogeny_fst_of_closedSubgroup (hq : IsCentralIsogeny q)
  (hC : Smooth C.X.hom) i hi hcomm (hDs : Smooth D.X.hom)
  (hDa : IsAffineHom D.X.hom) (hdom : IsDominant (i ≫ fst C H).hom.hom.left)`:
  `IsCentralIsogeny (i ≫ fst C H)`. No hypothesis on `π` is used.

  *Proof.* Write `p₁ = i ≫ fst C H` and `p₂ = i ≫ snd C H`.
  - Finiteness is the previous lemma.
  - Surjectivity: a finite morphism is closed, so its range is closed. A dominant
    morphism with closed range is surjective
    (`surjective_of_isDominant_of_isClosed_range`). This is Milne's
    Corollary 1.69 in scheme form.
  - Flatness is `flat_of_surjective`. Here `D` is locally of finite type because
    it is smooth (`hDs`), it is quasi-compact because it is affine (`hDa`), and `C`
    is smooth (`hC`).
  - Local finite presentation: `p₁` is locally of finite type, because its composite
    with the structure morphism of `C` is. `C` is locally noetherian, so `p₁` is
    locally of finite presentation
    (`LocallyOfFinitePresentation.iff_locallyOfFiniteType`).
  - Centrality of the full kernel uses the all-test criterion `isCentral_kernelι_iff`
    with `mem_center`. Let `x` be a `T`-point of `D` with `x ≫ p₁ = 1`, and let
    `a : T' ⟶ T` and `y` be a `T'`-point of `D`. Then `(a ≫ x) ≫ p₂ ≫ q = 1`, by
    the compatibility `p₂ ≫ q = p₁ ≫ π`. So `(a ≫ x) ≫ p₂` lies in the kernel of
    `q`, and it is central because `q` is a central isogeny
    (`IsCentralIsogeny.mem_center_of_comp_eq_one`). Since `i` is a monomorphism,
    points of `D` are determined by their images under `p₁` and `p₂`. The two
    products `(a ≫ x) * y` and `y * (a ≫ x)` both map to `y ≫ p₁` under `p₁`. Under
    `p₂` they map to products of `(a ≫ x) ≫ p₂` and `y ≫ p₂` in the two orders,
    which agree by the centrality just shown. Both maps are homomorphisms
    (`MonObj.mul_comp`).

  The conclusion matches Milne's Definition 18.1 (printed p. 387, PDF p. 403): a
  central isogeny is a surjective homomorphism with finite central kernel. The
  Library predicate also requires flatness and local finite presentation, and the
  proof establishes these as well.

- `isCentralIsogeny_snd_of_closedSubgroup (hπ : IsCentralIsogeny π)
  (hH : Smooth H.X.hom) i hi hcomm hDs hDa
  (hdom : IsDominant (i ≫ snd C H).hom.hom.left)`:
  `IsCentralIsogeny (i ≫ snd C H)`.

  *Proof.* Compose `i` with the swap isomorphism `C ⊗ H ≅ H ⊗ C`, given by
  `lift (snd C H) (fst C H)`. The composite is again a closed subgroup, since a
  closed immersion followed by an isomorphism is a closed immersion. The
  compatibility holds with `q` and `π` exchanged. Then apply the previous theorem
  with the roles of `C, π` and `H, q` exchanged.

## Provenance

The module's provenance is internal. The flatness lemmas follow Milne's route
(Propositions 1.65 and 1.70), using the published `orbitMapFaithfullyFlat` and
Library fpqc descent. The finiteness and centrality arguments are elementary
fibre-product and point computations, written for this proof. No literature
statement is formalized verbatim.
