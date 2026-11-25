# Finite-kernel surjective homomorphisms over algebraically closed fields are isogenies

Lean module: `Langlands.GroupScheme.AlgClosedFiniteKernelHomIsogeny`, namespace
`Langlands.GroupScheme.HomIsogeny`.

The Library proves that an endomorphism `f : G ⟶ G` of a smooth, proper, geometrically
connected commutative group over a field is an isogeny when its kernel is finite
(`fieldFiniteKernelIsogeny`). This module proves the analogous criterion for a homomorphism
`f : G ⟶ H` between two different groups over an algebraically closed field. It is needed
for maps `A ⟶ A^∨` from an abelian variety to its dual. The proofs adapt the Library modules
`Langlands.AbelianScheme.FieldFiniteKernelQuasiFinite` and
`Langlands.GroupScheme.TranslationFlatProof`. Their helper lemmas are private, so this module
restates them. Those helpers never used that source and target coincide.

## Provenance

The mathematical claim is the implication (a) ⇒ (d) of Proposition 8.1, p.12, of J. S. Milne,
*Abelian Varieties* (1986 article, author revision January 2, 2022; registered source
`milne-abelian-varieties-1986-author-2022`). There, a surjective homomorphism of abelian
varieties with finite kernel is finite, flat and surjective. Milne's proof gets flatness from
constant fibre dimension. This module uses instead the Library's generic-flatness and
translation route, as in `fieldFiniteSurjectiveEndomorphismFlat`. Surjectivity is a
hypothesis here; it is not derived from dimensions.

## Declarations

### Quasi-finiteness and finiteness

- `finite_kernel_baseChange`, `finite_split_fiber`, `finite_points_over_field`,
  `baseChange_isPullback`, `finite_preimage_image_point`: verbatim restatements of the
  private helpers of `FieldFiniteKernelQuasiFinite`. They hold for any `f : G ⟶ H` over any
  base `S`. Kernel finiteness is stable under base change. Over the residue field of a source
  point `x`, the fibre of `f` through `f x` is a translate of the kernel
  (`kernelFiberIso_inv_structure`). A finite scheme over a field has finitely many points.
  Together these show that the preimage of `{f x}` is finite.
- `locallyQuasiFinite_of_finite_kernel`: if the kernel of `f : G ⟶ H` is finite and the
  underlying morphism is locally of finite type, then the underlying morphism is locally
  quasi-finite. Proof: `LocallyQuasiFinite.of_finite_preimage_singleton`, applying the
  previous lemma to points of the image; other fibres are empty.
- `isFinite_of_finite_kernel`: if the kernel is finite, `G` is proper and `H` is separated
  over the base, then the underlying morphism of `f` is finite. Proof: `f` is proper because
  its composite with the structure map of `H` is the proper structure map of `G`
  (`IsProper.of_comp`). It is locally quasi-finite by the previous lemma, and
  `IsFinite.of_isProper_of_locallyQuasiFinite` concludes.

### Flatness

- `translation_naturality`: right translation by a point `a` of `G` followed by `f` equals `f`
  followed by right translation by `a ≫ f`.
- `rationalPoint_surjective`: over an algebraically closed field, if `G` and `H` are locally
  of finite type and `f` is surjective, every rational point of `H` lifts to a rational point
  of `G`. Proof as in `TranslationFlatProof`: the fibre over the closed point of a rational
  point is a nonempty locally closed set, so it contains a closed point of the Jacobson space
  `G`. That point is rational (`pointOfClosedPoint`), and two rational points agree when they
  agree at the closed point (`ext_of_apply_closedPoint_eq`).
- `flat_restrict_translation`: if `f` is flat over a target open `U`, it is flat over the
  preimage of `U` under right translation by `a ≫ f`. Proof: `morphismRestrict_comp`, and
  translations are isomorphisms.
- `flat_of_flat_restrict`: over an algebraically closed field, with `G` and `H` locally of
  finite type and `f` surjective, flatness over one nonempty target open implies flatness.
  Proof: as in `translationFlat`. Pick a closed point `y` of `U`. If a closed point `x` of `H`
  were outside all the translates `V a`, choose a rational `a` with `a ≫ f = x⁻¹ * y`. Then
  translation by `a ≫ f` sends `x` to `y ∈ U`, a contradiction. Flatness is local on the
  target (`IsZariskiLocalAtTarget.of_iSup_eq_top`).

### The criterion

`isIsogeny_of_finite_kernel_of_surjective`: let `K` be algebraically closed and
`f : G ⟶ H` a homomorphism of group objects over `Spec K`. Assume `G` is proper, `H` is
smooth, geometrically connected and separated, the kernel of `f` is finite, and the
underlying morphism of `f` is surjective. Then `f` is an isogeny, i.e. its underlying morphism
is finite, flat and surjective (`Langlands.GroupScheme.IsIsogeny`).

Proof: finiteness is `isFinite_of_finite_kernel`. The published
`Langlands.AbelianScheme.smoothGeometricIntegrality` makes `H → Spec K` geometrically
integral, so the underlying scheme of `H` is integral
(`GeometricallyIntegral.isIntegral_of_subsingleton`). It is locally Noetherian, being locally
of finite type over a field. The published `Langlands.AlgebraicGeometry.finiteGenericFlat`
gives a nonempty target open over which `f` is flat. `flat_of_flat_restrict` then gives
flatness.
