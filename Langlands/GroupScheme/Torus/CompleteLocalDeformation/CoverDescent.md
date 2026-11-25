# Descent of homomorphisms along a finite étale local splitting cover

Module `Langlands.GroupScheme.Torus.CompleteLocalDeformation.CoverDescent`, namespace
`Langlands.GroupScheme.CompleteLocalDeformation`.

## Main statement

`exists_descent_of_specialFibre`. Let `A` be a noetherian local ring, and let `H` and `G` be
group schemes over `Spec A` with `G → Spec A` an affine morphism. Let
`d : LocalSplittingData A H` be a local splitting cover from
`Torus.CompleteLocalSimultaneousSplitting`. Then `B := d.Carrier` is local, finite and étale over
`A` with a local structure map, and `H_B` is diagonalizable. Assume also that the special
fibre `(G_B)_{k_B}` is diagonalizable (hypothesis `hG`). Let `f₀ : H_k ⟶ G_k` be a homomorphism
of special fibres and `fB : H_B ⟶ G_B` a homomorphism. Assume

`(baseChange spB).map fB ≫ (specialFibreBaseChangeIso G).hom =
  (specialFibreBaseChangeIso H).hom ≫ (baseChange (Spec.algebraMap k k_B)).map f₀`.

Then there is `f : H ⟶ G` with `(baseChange (Spec.algebraMap A B)).map f = fB` and
`(baseChange spA).map f = f₀`. Here `spA` and `spB` are the maps from the spectra of the
residue fields.

`exists_descent_of_specialHomTransport` states the same result with the hypothesis
`(baseChange spB).map fB = specialHomTransport f₀`. This is the form of the descent hypothesis
`hdesc` in `specialFibre_hom_bijective_of_cover` (module `Torus.SpecialFibreHomDescentAssembly`). The instance
`LocalSplittingData.specFlat` records that `Spec B → Spec A` is flat.

Completeness of `A` is not needed here.

## Auxiliary results (pull-back calculus)

These use `Descent.pullHom` and `Descent.pullbackComparison` from the published
`Langlands.GroupScheme.Descent.Data`.

- `hom_ext_baseChange_fst`: two homomorphisms into a base change `(baseChange r).obj G` are
  equal when their projections to `G` are equal.
- `baseChange_map_left_fst`, `pullbackComparison_inv_fst_snd` and `pullHom_left_fst` compute
  these projections.
- `pullHom_pullHom`: pulling back along `q₁` and then along `q₂` is pulling back along any `q`
  with `q₂ ≫ q₁ = q`.
- `baseChange_map_eq_of_pullHom_eq`: equal pullbacks give equal base changes.
- `compatible_of_pullHom_eq`: if the pullbacks of `f` along the two projections of the overlap
  agree, then `f` is compatible with the canonical descent data.
- `baseChange_map_injective`: base change along a flat, surjective, quasi-compact morphism is
  injective on homomorphisms. It follows from `FpqcHomDescent.unique`.
- `specialFibreBaseChangeIso_eq`: the special-fibre comparison `specialFibreBaseChangeIso` is the composite of two
  `pullbackComparison` isomorphisms.

## Proof

Write `p : Spec B → Spec A`, `R := B ⊗[A] B`, and let `iL, iR : Spec R → Spec B` be the maps
induced by the two inclusions. The hypothesis says `pullHom spB fB = pullHom jk f₀` over
`Spec k_B`, where `jk : Spec k_B → Spec k`.

1. *Rigidity on `Spec R`.* Let `I` be the extension of `𝔪_B` to `R` along the left factor.
   The map `B → R → R ⧸ I` factors through `k_B`, giving `κ₁`. The map through the right factor
   also factors, giving `κ₂`. This uses `𝔪_B = 𝔪_A B` (`ResidueExtensionData.map_maximalIdeal`,
   since `B` is unramified over `A`). Both composites `k → k_B → R ⧸ I` are the structure map
   of `R ⧸ I`. So by `pullHom_pullHom` and the hypothesis, the reductions of `pullHom iL fB` and
   `pullHom iR fB` modulo `I` are both `pullHom (κ₁ ≫ jk) f₀`. Over `Spec R`, the source
   `H_R` is diagonalizable as a base change of `H_B`. The reduction of `G_R` modulo `I` is
   diagonalizable as a base change of `(G_B)_{k_B}` along `κ₁`. `R` is finite over the
   noetherian local ring `B`. So `eq_of_baseChange_eq_of_finite` (`HomRigidity.lean`) gives
   `pullHom iL fB = pullHom iR fB`.
2. *Compatibility.* `pullbackSpecIso` gives `e : Overlap p → Spec R` with `e ≫ iL = fst p` and
   `e ≫ iR = snd p`. Pulling the equality of step 1 back along `e` and applying
   `pullHom_pullHom` gives `pullHom (fst p) fB = pullHom (snd p) fB`. By
   `compatible_of_pullHom_eq`, `fB` is compatible with the canonical descent data.
3. *Descent.* `p` is flat (`B` is étale over `A`), surjective and quasi-compact. Hence
   `FpqcHomDescent.hom` gives `f` with base change `fB`.
4. *Special fibre.* `pullHom_map` and the hypothesis give
   `pullHom jk (bc spA f) = pullHom spB (bc p f) = pullHom spB fB = pullHom jk f₀`. So the base
   changes of `bc spA f` and `f₀` along `jk` agree. `jk` is flat and surjective because `k_B` is a
   nonzero vector space over the field `k`. `baseChange_map_injective` then gives
   `bc spA f = f₀`.

## Provenance

This is internal content derived for Conrad, *Reductive group schemes* (2014), Theorem
B.3.2(2). It is the finite étale descent step. Compare SGA 3, Exposé IX, proof of 7.1, which
descends along a finite étale splitting cover and uses uniqueness on the double overlap. Here
uniqueness on the double overlap comes from rigidity modulo the maximal ideal
(`HomRigidity.lean`), not from an adic comparison.
