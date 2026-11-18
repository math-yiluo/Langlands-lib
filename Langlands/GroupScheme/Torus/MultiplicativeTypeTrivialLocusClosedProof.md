# Proof: the trivial locus of a homomorphism from a group of multiplicative type is closed

Worker 488.

The theorem `Langlands.GroupScheme.multiplicativeTypeTrivialLocusClosed.{u}` proves the
unchanged published proposition
`Langlands.GroupScheme.MultiplicativeTypeTrivialLocusClosedStatement.{u}`. It has no additional
parameters or hypotheses:

```lean
theorem multiplicativeTypeTrivialLocusClosed :
    MultiplicativeTypeTrivialLocusClosedStatement.{u}
```

For every scheme `S`, every `S`-group `H` of multiplicative type
(`RelativeMultiplicativeType.IsMultiplicativeType`), every `S`-group `G` whose structure
morphism is separated and every homomorphism `u : H ⟶ G`, the set of points `s ∈ S` at which
the fibre `u_s` over `Spec κ(s)` is the unit homomorphism is closed in `S`. The universe `u`
is arbitrary.

## Source and correspondence

The statement is the closedness half of Corollaire 5.3 of A. Grothendieck, SGA 3, Exposé IX,
*Groupes de type multiplicatif : homomorphismes dans un schéma en groupes*, in the Gille–Polo
recomposed annotated edition, provisional version 1.0 of 8 November 2009. The source is
registered as `sga3-expose-ix-gille-polo-2009`, file
`Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`,
SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`. The statement of
Corollaire 5.3 is on recomposed p.49 (PDF page 19, margin 60) and the closedness argument is on
recomposed p.50 (PDF page 20). I read both pages for this proof.

The source reduces closedness to the kernel `K = Ker(u)`, a closed subscheme of `H` because `G`
is separated. It then cites VIII 6.4, or gives a schematic-density argument. The Lean proof
takes neither route. It uses the route sketched under "Why the statement holds without them" in
the statement's Markdown: reduce along the fppf cover and along affine charts to
`H = Spec B[Λ]` over `Spec B`. The closed condition is then that certain coefficients lie in
the prime ideal of the point, because `B[Λ]` is free over `B`. The proof uses only the
separatedness of `G` and the fact that, fppf-locally on `S`, the scheme underlying `H` is
isomorphic over the base to `Spec` of a group algebra. It does not use that `Λ` is finitely
generated, nor that these isomorphisms respect the group laws.

## Implemented proof

All auxiliary theorems are `private` declarations in the namespace
`Langlands.GroupScheme.MultiplicativeTypeTrivialLocusClosedProof`. They are internal steps of
this proof and add no public API.

The proof works with a general **agreement locus**. Let `p : X ⟶ S` and `x y : X ⟶ Y`. The
agreement locus of `(p, x, y)` is the set of `s : S` with
`pullback.fst p (S.fromSpecResidueField s) ≫ x = pullback.fst p (S.fromSpecResidueField s) ≫ y`,
that is, the points over whose fibre `x` and `y` agree.

### Algebraic and affine helpers

1. `tmul_one_eq_zero_iff`. Let `A` be a free `B`-module with basis `bA` and let `C` be a
   `B`-algebra. Then `a ⊗ₜ 1 = 0` in `A ⊗[B] C` if and only if every coordinate
   `bA.repr a i` maps to zero in `C`. The proof applies the linear equivalence
   `A ⊗[B] C ≃ (I →₀ C)` obtained from `LinearEquiv.rTensor C bA.repr` and
   `finsuppScalarLeft`. It sends `a ⊗ₜ 1` to the function `i ↦ algebraMap B C (bA.repr a i)`.
2. `comp_eq_iff_ker_le`. Let `a b : X ⟶ Y` agree after composition with a separated
   `π : Y ⟶ S`. Let `j` be the second projection of the pullback of the diagonal of `π` along
   `pullback.lift a b h`; `j` is a closed immersion. Then for any `g : T ⟶ X`,
   `g ≫ a = g ≫ b` if and only if `j.ker ≤ g.ker`. Forward: `g` factors through `j` via
   `pullback.lift`, and `Scheme.Hom.le_ker_comp` gives the inequality. Backward:
   `IsClosedImmersion.lift_fac` factors `g` through `j`, and `j ≫ a = j ≫ b` follows from the
   pullback condition composed with the two projections.
3. `ker_le_iff_of_isAffine`. On an affine target, `j.ker ≤ g.ker` if and only if the kernels
   of the global-section ring maps satisfy the same inequality. The proof uses
   `Scheme.ker_of_isAffine` and the order isomorphism `Scheme.IdealSheafData.equivOfIsAffine`.
4. `fromSpecResidueField_preimage_eq_zero_iff`. For `s ∈ Spec B`, the ring map
   `B → κ(s)` underlying `fromSpecResidueField s` kills `c` if and only if `c ∈ s.asIdeal`.
   The closed point of `Spec κ(s)` maps to `s` (`Scheme.fromSpecResidueField_apply`), so the
   prime `s` is the preimage of the maximal ideal of the field `κ(s)`.
5. `SpecMap_appTop_eq_zero_iff`. The map `(Spec.map ψ).appTop` kills `c` if and only if `ψ`
   kills the image of `c` under `Scheme.ΓSpecIso`. This is naturality of `Scheme.ΓSpecIso`
   together with injectivity of the isomorphism.

### Reductions for the agreement locus (section `Locus`)

6. `fst_comp_eq_iff`. Agreement after base change along `c ≫ t` is the same as agreement after
   the iterated base change along `t` and then `c`. The proof cancels the isomorphism
   `pullbackLeftPullbackSndIso`.
7. `fst_eq_iff_comp`. If `c` is flat and surjective, agreement after base change along `t` is
   equivalent to agreement after base change along `c ≫ t`. The projection
   `pullback.fst (pullback.snd p t) c` is the base change of `c`, so it is flat and surjective.
   Hence it is an epimorphism (`Flat.epi_of_flat_of_surjective`) and can be cancelled.
8. `fst_eq_iff_of_isIso`. Agreement is unchanged when `p, x, y` are precomposed with an
   isomorphism `k : X' ⟶ X`. The proof cancels `pullbackRightPullbackFstIso` and uses the
   pullback condition.
9. `preimage_locus`. For `g : S' ⟶ S`, the preimage under `g` of the agreement locus of
   `(p, x, y)` is the agreement locus of `(pullback.snd p g, pullback.fst p g ≫ x,
   pullback.fst p g ≫ y)` on `S'`. For `v ∈ S'`, Mathlib's
   `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField` writes
   `S'.fromSpecResidueField v ≫ g` as `Spec.map (g.residueFieldMap v) ≫
   S.fromSpecResidueField (g v)`. The morphism `Spec.map (g.residueFieldMap v)` is flat
   (a map of fields) and surjective (its target is a point). Steps 6 and 7 then give the
   equality of the two conditions.
10. `isClosed_of_cover`. Let `g i : U i ⟶ S` be a jointly surjective family of open maps. If the
    agreement locus of each base change (as in step 9) is closed in `U i`, then the agreement
    locus of `(p, x, y)` is closed in `S`. By joint surjectivity, its complement is the union
    of the images of the complements of the preimages. Each image is open because `g i` is an
    open map and, by step 9, the preimage is the closed base-changed locus.
11. `isClosed_locus_of_isIso`. If `k : X' ⟶ X` is an isomorphism with `k ≫ p = p₀` and the
    agreement locus of `(p₀, k ≫ x, k ≫ y)` is closed, then so is that of `(p, x, y)`. The two
    sets are equal by step 8.

### The affine free case

12. `isClosed_core`. Let `A` be a `B`-algebra with a `B`-basis `bA`, let `π : Y ⟶ S₀` be
    separated, and let `x y : Spec A ⟶ Y` satisfy `x ≫ π = y ≫ π`. Then the agreement locus of
    `(Spec.map (algebraMap B A), x, y)` is closed in `Spec B`. Let `j` be the closed immersion
    from step 2, and fix `s`. Equip `κ(s)` with the `B`-algebra structure given by
    `Spec.preimage (fromSpecResidueField s)`, so that `fromSpecResidueField s` is
    `Spec.map (algebraMap B κ(s))`. Then `pullbackSpecIso` identifies the fibre product with
    `Spec (A ⊗[B] κ(s))`, whose first projection is `Spec.map` of `includeLeftRingHom`
    (`pullbackSpecIso_inv_fst`). Steps 2, 3, 5, 1 and 4 now show that agreement at `s` is
    equivalent to the following condition: for every global section `c` of `Spec A` with
    `j.appTop c = 0` and every index `i`, the `i`-th coordinate of the image of `c` in `A`
    lies in the prime ideal `s`. So the locus is an intersection of the sets
    `{s | r ∈ s.asIdeal} = PrimeSpectrum.zeroLocus {r}`, each of which is closed.

### Homomorphisms after base change

13. `baseChange_map_left_fst` and `baseChange_map_left_snd`. The underlying morphism of
    `(GroupScheme.baseChange q).map u`, composed with the two pullback projections, equals
    `pullback.fst ≫ u.hom.hom.left` and `pullback.snd`, respectively. Both are
    `pullback.lift_fst` and `pullback.lift_snd`.
14. `baseChange_map_eq_iff`. Two homomorphisms `a b : H ⟶ G` have equal base changes along `t`
    if and only if `pullback.fst H.X.hom t ≫ a.hom.hom.left =
    pullback.fst H.X.hom t ≫ b.hom.hom.left`. The backward direction uses `Grp.hom_ext`,
    `Over.OverMorphism.ext` and `pullback.hom_ext` with step 13.

### Main theorem

Fix `S, H, G`, the multiplicative-type witness, the separatedness of `G.X.hom`, and `u`.

- The Library lemmas `CentralRigidity.hom_eq_one_iff_eq_zero` and
  `CentralRigidity.baseChange_map_zero` (module `Torus.CentralRigidityReduction`) say that
  `f.hom.hom = 1` exactly when `f = 0`, and that base change sends `0` to `0`. With step 14
  they turn the target set into the agreement locus of
  `(H.X.hom, u.hom.hom.left, (0 : H ⟶ G).hom.hom.left)`. Both morphisms composed with
  `G.X.hom` equal `H.X.hom` (`Over.w`).
- Unpack `IsMultiplicativeType H` into an fppf cover `𝒰` of `S` (with flat, locally finitely
  presented members). Apply step 10 to `𝒰`. Each member `𝒰.f i` is flat and locally of finite
  presentation, hence universally open, hence an open map. The members are jointly surjective
  by `𝒰.exists_eq`.
- For each `i`, unpack the diagonalizability of the base change of `H` to `𝒰.X i` as a group
  `Λ` and an isomorphism `e` to `diagonalizable (𝒰.X i) Λ`. Apply step 10 again, now to the
  affine open cover `𝒱 = (𝒰.X i).affineOpenCover`, whose members are open embeddings and
  cover `𝒰.X i`.
- For a chart `a : Spec B ⟶ 𝒰.X i`, compose the base change of `e` along `a`, the Library
  isomorphism `RelativeMultiplicativeType.diagonalizableBaseChangeIso a Λ` and the inverse
  of `Diagonalizable.relativeModelIso B Λ`. The result is an isomorphism `E` from the iterated
  base change of `H` to the affine model `(Diagonalizable.groupScheme B Λ).toGrp`, whose
  underlying scheme is `Spec (AddMonoidAlgebra B Λ)`. The underlying scheme morphism `k` of
  `E.inv` is an isomorphism over `Spec B`, so `k` composed with the structure morphism is
  `Spec.map (algebraMap B (AddMonoidAlgebra B Λ))` (`Over.w`).
- Step 11 transports the problem along `k`. Step 12, with the basis
  `AddMonoidAlgebra.basis Λ B`, the separated morphism `G.X.hom` and the composition equality
  above, proves that the locus is closed.

## Dependencies and verification

The module imports the published target, `Torus.AffineRelativeDiagonalizable` (for
`Diagonalizable.relativeModelIso`, which also brings in `RelativeMultiplicativeType`),
`Torus.CentralRigidityReduction` (for the zero-homomorphism lemmas), and Mathlib's
`AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Morphisms.UniversallyOpen` and
`LinearAlgebra.DirectSum.Finsupp`. The target and every file it imports are unchanged. The
proof introduces no axioms and no replacement statement. In development checks with the task's
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, the module compiles without warnings and
the main theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. Independent
semantic review and official validation are required for acceptance.
