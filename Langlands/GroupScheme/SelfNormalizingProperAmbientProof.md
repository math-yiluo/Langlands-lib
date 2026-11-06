# Proof of the proper ambient map for self-normalizing subgroups

The theorem `Langlands.GroupScheme.selfNormalizingProperAmbient` proves the published proposition
`Langlands.GroupScheme.SelfNormalizingProperAmbientStatement.{u}` (module
`Langlands.GroupScheme.SelfNormalizingProperAmbientStatement`). The statement covers every
commutative ring `R : Type u`, an affine smooth group scheme `G` over `Spec R`, and a closed
subgroup `i : H ⟶ G` that is smooth with geometrically connected fibres and equals its own
normalizer, tested on all schemes over `Spec R`. It gives a proper, locally finitely presented
`Y` over `Spec R` and a morphism `r : G.X ⟶ Y`. For every test object `T` and all
`g h : T ⟶ G.X`, `g ≫ r = h ≫ r` holds exactly when `g⁻¹ * h` lies in the range of `i`. The
proof uses no further hypotheses. In particular, it never uses geometric connectedness of `G`.

## Provenance

The construction follows the finite-jet argument in Conrad's proof of Theorem 2.3.6(1) (Brian
Conrad, *Reductive group schemes*, 2014, source `conrad-2014-reductive-group-schemes`, printed
pp. 72–74), as described in the Markdown of the statement. Conrad finds an infinitesimal
neighbourhood `H_n` of the identity in `H` whose stabilizer `N_G(H_n)` is `H`. He then takes the
orbit map from `G` into a Grassmannian of quotients of the coordinate module of `G_n`.

The Lean proof takes a different route. It works over the given ring `R` throughout and makes no
Noetherian approximation.

- The stabilization index comes from the key step and the finite generation of the ideal of `H`
  (module `Langlands.GroupScheme.SelfNormalizingAmbient.KeyStep`), not from quasi-compactness over
  a Noetherian base.
- The jet quotients are finite projective because `B ⧸ I` is smooth (module
  `Langlands.RingTheory.Smooth.SectionJets`).
- Ranks that are not constant are handled inside the orbit-map module with a projective
  complement, rather than on clopen strata.

All of these are published Library results, and this module only assembles them.

The supporting modules `Langlands.GroupScheme.SelfNormalizingAmbient.FibreDomain` and
`Langlands.GroupScheme.SelfNormalizingAmbient.Translation` are part of this contribution, and each
has its own Markdown.

## Notation

Throughout, `R` also stands for the ring `CommRingCat.of R`. The Library module
`Langlands.GroupScheme.AffineCorepresented` provides, for the affine group `G`, a group functor
`functor G` on commutative `R`-algebras corepresented by the `R`-algebra `algebra G` through
`corepresentation G`, together with an isomorphism
`groupSchemeIso G : Corepresented.groupScheme (functor G) (corepresentation G) ≅ G`. Write `B` for
`algebra G`, `e` for `corepresentation G`, `Φ` for `groupSchemeIso G` and `G'` for the coordinate
group scheme `Corepresented.groupScheme (functor G) e`. `AffineCoordinates.coordinateHom i` is
`i ≫ Φ.inv : H ⟶ G'`, which is again a closed immersion. For a point `x` of `G'` or `G` over a
test object, `x ≫ Φ.hom` and `x ≫ Φ.inv` abbreviate `x ≫ Φ.hom.hom.hom` and
`x ≫ Φ.inv.hom.hom`, the composites with the underlying morphisms of schemes over `Spec R`. `augIdeal e` is the augmentation ideal
of `B`, and `jetIdeal e I n = I ⊔ augIdeal e ^ (n + 1)` (module
`Langlands.GroupScheme.SelfNormalizingAmbient.Stabilizer`).

## Auxiliary declarations

- `Corepresented.counit_apply_eq_zero hH hb`: if `hH : IsCutOutBy e H J` and `b ∈ J`, then the
  counit `LinearEmbedding.counit e` sends `b` to `0`. This holds because `1 ∈ H R` and the
  counit classifies `1`.
- `Corepresented.finite_projective_quotient_jetIdeal hH n`: if `hH : IsCutOutBy e H J` and
  `B ⧸ J` is smooth over `R`, then `B ⧸ jetIdeal e J n` is a finite projective `R`-module. Proof:
  the counit descends to an `R`-algebra section `ε : B ⧸ J → R`.
  `Algebra.Smooth.finite_projective_quotient_ker_pow` makes `(B ⧸ J) ⧸ (ker ε) ^ (n + 1)` finite
  projective. The kernel of `ε` is the image of `augIdeal e`, so `(ker ε) ^ (n + 1)` is the image
  of `augIdeal e ^ (n + 1)` (`Ideal.map_pow`, `Ideal.map_comap_of_surjective`).
  `DoubleQuot.quotQuotEquivQuotSupₐ` then identifies the double quotient with
  `B ⧸ (J ⊔ augIdeal e ^ (n + 1))`.
- The published `SubgroupFunctor.mem_range_comp_iso_iff i Φ.symm g`
  from `Langlands.GroupScheme.RelativeSelfNormalizerProof`: for an isomorphism `Φ : G' ≅ G` of group
  schemes over `S` and `g : T ⟶ G.X`, the point `g ≫ Φ.inv` lies in the range of `i ≫ Φ.inv`
  exactly when `g` lies in the range of `i`.

## Proof of the main theorem

1. **Smoothness of the coordinate algebra.** The structure morphism of `G'` is the composite of
   the isomorphism `Φ.hom` with the structure morphism of `G` (`Over.w`), so it is smooth.
   `Corepresented.smooth_of_smooth_groupScheme` (module `Translation`) gives
   `Algebra.Smooth R B`.
2. **The ideal of the subgroup.** `Corepresented.exists_ideal_range_smooth` (module
   `Translation`), applied to `coordinateHom i`, gives an ideal `I` of `B` with three
   properties. A point of `G'` lies in the range of `coordinateHom i` exactly when its classifying
   map kills `I`. `B ⧸ I` is smooth over `R`. `k ⊗[R] (B ⧸ I)` is a domain for every field `k`
   over `R`. The Library theorem `isCutOutBy_range` turns the first property into
   `hH : IsCutOutBy e (affineSubgroups (range (coordinateHom i))) I`.
3. **Self-normalization in coordinates.** Let `x` be a point of `G'` that normalizes the range of
   `coordinateHom i`. By `SubgroupFunctor.normalizer_range_eq_comap_of_iso` (applied to
   `Φ.symm`) and `SubgroupFunctor.comp_hom_comp_inv_hom`, the point `x ≫ Φ.hom` normalizes the
   range of `i`. The hypothesis `hN` puts it in the range of `i`, and `mem_range_comp_iso_iff` applied to `Φ.symm`
   brings it back to the range of `coordinateHom i`. With the Library theorem
   `affineSubgroups_normalizer`, which identifies points of the normalizer with `normalizerFamily`,
   this gives
   `normalizerFamily (affineSubgroups (range (coordinateHom i))) A ≤ affineSubgroups (range (coordinateHom i)) A`
   for every `R`-algebra `A`.
4. **Finite generation.** `B` and `B ⧸ I` are of finite presentation over `R`, since both are
   smooth. So the kernel `I` of the surjection `B → B ⧸ I` is finitely generated
   (`Algebra.FinitePresentation.ker_fG_of_surjective`).
5. **Finite stabilization.** Every jet quotient `B ⧸ jetIdeal e I n` is projective
   (`finite_projective_quotient_jetIdeal`). `Corepresented.exists_stabilizes_jetIdeal_iff`
   (module `KeyStep`) gives `N` such that a point `x ∈ functor G A` stabilizes the subfunctor cut
   out by `jetIdeal e I N` exactly when `x ∈ affineSubgroups (range (coordinateHom i)) A`. Its
   hypotheses are `hH`, smoothness and flatness of `B ⧸ I`, projective jet quotients, domain
   field fibres, finite generation of `I`, and step 3.
6. **The orbit map.** `B ⧸ jetIdeal e I N` is finite projective by
   `finite_projective_quotient_jetIdeal`. `B ⧸ augIdeal e ^ (N + 1)` is finite projective by
   `Algebra.Smooth.finite_projective_quotient_ker_pow` applied to the counit of `B`.
   Since `augIdeal e ^ (N + 1) ≤ jetIdeal e I N` (`le_sup_right`),
   `SelfNormalizingAmbient.exists_proper_orbit_map` gives a proper, locally finitely presented
   `Y` and `r' : G'.X ⟶ Y`. Two points `g` and `h` of `G'` satisfy `g ≫ r' = h ≫ r'` exactly
   when `pointsEquiv (functor G) e T (g⁻¹ * h)` stabilizes `jetIdeal e I N`.
7. **Conclusion.** Take `r = Φ.inv.hom.hom ≫ r'`. For `g h : T ⟶ G.X`, apply step 6 to
   `g ≫ Φ.inv.hom.hom` and `h ≫ Φ.inv.hom.hom`. Composition with a group morphism commutes with
   products and inverses (`MonObj.mul_comp`, `GrpObj.inv_comp`), so
   `(g ≫ Φ.inv)⁻¹ * (h ≫ Φ.inv) = (g⁻¹ * h) ≫ Φ.inv`. Steps 5 and 6 and the Library theorem
   `mem_range_iff_mem_affineSubgroups` turn the fibre condition into membership of
   `(g⁻¹ * h) ≫ Φ.inv` in the range of `coordinateHom i`. `mem_range_comp_iso_iff` applied to `Φ.symm` then gives
   membership of `g⁻¹ * h` in the range of `i`.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
