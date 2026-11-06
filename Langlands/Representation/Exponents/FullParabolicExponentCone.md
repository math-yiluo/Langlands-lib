# The positive-cone clause for full represented parabolics

This internal unit supports the proof task on the unitarizable-constituent step of
Renard, Théorème VII.1.3. Casselman's criterion in the Library,
`HasPositiveRepresentedJacquetExponents`, also tests full parabolics. This module
proves that test for a representation with a unitary central character. The
published identity-parabolic clause `IdentityParabolicCasselmanConeStatement`
(`Langlands/Representation/Exponents/CasselmanCentralDirections.lean`) covers only
`p = l = 𝟙 G`. This module covers every represented parabolic `p : P ⟶ G` that is an
isomorphism, with an arbitrary rational Levi `l : M ⟶ P`.

Its provenance is the published constructions it combines. It asserts no new source
translation. In the source, the clause for `P = G` holds because the central
character is unitary.

## The statement

`FullParabolicCasselmanConeStatement.{u,v}` is a Prop-valued definition, proved in
this module by `fullParabolicCasselmanCone`. It quantifies over:

- a nonarchimedean local field `k` (Hausdorff), and a connected reductive `G` over `k`;
- the canonical point topology on `G(k)`, assumed locally compact and nonarchimedean;
- an actual represented parabolic `p : P ⟶ G`, with:
  - a rational Levi `l : M ⟶ P` and a geometric unipotent radical `r : U ⟶ P`;
  - the multiplication isomorphism;
  - a split component `a : A ⟶ M`;
  - a compatible root presentation `pres` of `p, l, a`.

It assumes that `p` is an isomorphism. Let `π : SmoothRep.{0,u,v} ℂ G(k)` have a
unitary central character, given as `Nonempty (UnitaryCentralCharacter π.representation)`.
Then every normalized Jacquet exponent `χ` of `π` along `(p, l, r, a)` has normalized
real part in `pres.positiveCone`. The field universe `u` and the carrier universe `v`
are independent. The instance `hG.smooth` is derived from connected reductivity and
supplies the local finite type needed for the cone.

## The proof

1. Cone. `SubgroupFunctor.range_eq_top_of_isIso` shows that the range of an
   isomorphism of group schemes is everything, over any base scheme.
   `ParabolicRootPresentation.simpleRelativeRoots_subset_of_range_eq_top` assumes that
   the Levi range `range (l ≫ p)` is the whole group. The realization field of the
   presentation supplies a standard cocharacter `ζ` with
   `range (l ≫ p) = Dynamic.centralizer (ζ ≫ i)`. So that centralizer is everything,
   and `ζ ≫ i` is central by the published `isCentral_iff_dynamicCentralizer_eq_top`.
   The published `root_restrict_eq_zero_of_isCentral`, applied to the split torus
   `𝔾_m`, gives `ζ ≫ α = 0` for every relative root `α`. Hence `⟨α, ζ⟩ = 0`. A
   standard cocharacter pairs positively with every simple root outside the face `J`,
   so every simple root lies in `J`. The published
   `zero_mem_positiveCone_iff_simpleRoots_subset` then gives
   `zero_mem_positiveCone_of_range_eq_top`, and `zero_mem_positiveCone_of_isIso`
   covers an isomorphism `l ≫ p`. Only the Levi half of the realization is used, so
   no torus-action unipotence input and no trivial-unipotent-radical hypothesis is
   needed.
2. Centrality. `splitComponentPointsMap_mem_center_of_isIso` shows that, through an
   isomorphism `l ≫ p`, each point `a(t)` of the central split component of `M(k)`
   maps into the centre of `G(k)`. The map `l ≫ p` is surjective on rational points,
   since `inv (l ≫ p)` gives preimages, and a surjective homomorphism maps the centre
   into the centre.
3. Real part. `normalizedJacquetExponent_realPart_eq_zero_of_isIso` applies the
   published `normalizedJacquetExponent_norm_eq_one_of_mem_center` at these central
   points. Then `Plancherel.SplitTorus.normalizedRealPart_eq_zero_iff` gives real part
   zero. `normalizedJacquetExponent_mem_positiveCone_of_isIso` combines this with
   step 1.
4. Statement. `fullParabolicCasselmanCone` installs the instances of the statement.
   It obtains `IsIso l` from the published `IsRationalLeviSubgroup.isIso_of_isIso_parabolic`,
   so `l ≫ p` is an isomorphism, and applies step 3.

## Scope

Steps 1 to 3 hold for any parabolic data whose Levi inclusion `l ≫ p` is an
isomorphism. They use no reductivity, and step 1 holds over any field. The ambient
group is affine, and local finite type is assumed for the cone statements. Only the
assembled statement uses connected reductivity, to make the Levi of a full parabolic
an isomorphism. Nothing is asserted about proper parabolics, and the existence of
root presentations is not asserted.
