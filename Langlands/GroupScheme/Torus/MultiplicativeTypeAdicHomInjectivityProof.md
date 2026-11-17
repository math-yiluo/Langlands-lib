# Adic determination of homomorphisms from isotrivial groups of multiplicative type

Worker 517.

The theorem `Langlands.GroupScheme.multiplicativeTypeAdicHomInjectivity.{u}` proves the unchanged published proposition `Langlands.GroupScheme.MultiplicativeTypeAdicHomInjectivityStatement.{u}`. It has no additional parameters or hypotheses:

```lean
theorem multiplicativeTypeAdicHomInjectivity :
    MultiplicativeTypeAdicHomInjectivityStatement.{u}
```

For a noetherian commutative ring `A` complete and separated for an ideal `I`, let `H` and `G` be group schemes over `Spec A`, with `G` affine over the base. Suppose `H` becomes diagonalizable after a finite étale surjective base change. If two homomorphisms `H ⟶ G` have equal base changes to `Spec (A / I^(n+1))` for every natural number `n`, the theorem proves that the homomorphisms are equal. The universe `u` is arbitrary.

## Source and correspondence

The source is A. Grothendieck, SGA 3, Exposé IX, *Groupes de type multiplicatif : homomorphismes dans un schéma en groupes*, Théorème 7.1, recomposed pp.56–59 (original margin pp.68–72), in the Gille–Polo recomposed annotated edition, provisional version 1.0 of 8 November 2009. The retained source is registered as `sga3-expose-ix-gille-polo-2009`, file `Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`, SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`. Definition 1.1 on recomposed p.31 (margin p.37) supplies the finite étale splitting meaning of isotriviality. These original passages were read for this proof.

Théorème 7.1 asserts bijectivity of the map from homomorphisms to compatible systems of reductions. The published target and this proof cover its injectivity part. The source's split argument observes on p.57 that the group algebra embeds into its adic completion; its general argument on pp.58–59 passes to a finite flat covering on which the source is diagonalizable. The Lean proof implements coefficientwise separation and descent of equality directly, without constructing an inverse limit or using the source's surjectivity argument. As specified by the published target, the character group witnessing relative diagonalizability is finitely generated. No finite type, flatness or smoothness hypothesis is imposed on the target group.

## Implemented proof

All four auxiliary theorems in the `AdicHomInjectivity` namespace are private. They are internal steps of the proof of the published statement.

1. `hausdorff_groupAlgebra` proves that `AddMonoidAlgebra B Λ` is `I`-adically Hausdorff as an `A`-module whenever the `A`-algebra `B` is Hausdorff. Compose the coefficient linear equivalence with evaluation at each `λ`. These linear maps carry `I^n` times the whole module into `I^n` times `B`. Each coefficient of an element lying in all these submodules therefore vanishes, and coefficient extensionality proves the element is zero.
2. `hom_eq_of_quotient_precomp` detects equality of scheme morphisms from `Spec R` into an affine scheme when `R` is separated. Equality after every quotient precomposition gives equality of the global-section ring maps after all quotients. Naturality of `Scheme.ΓSpecIso` identifies these maps with maps into `R`; `IsHausdorff.StrictMono.funext'`, applied to the strictly increasing exponents `n+1`, proves their equality. Affine extensionality then proves equality of scheme morphisms.
3. `baseChange_map_fst` is the projection identity for a base-changed group homomorphism. It follows from `pullback.lift_fst`.
4. `eq_precomp_of_reductions` applies the previous detection result to any separated `A`-algebra `T` and any morphism `q : Spec T ⟶ H` over `Spec A`. Set `J = I.map (algebraMap A T)`. The quotient map from `A / I^(n+1)` to `T / J^(n+1)` and `q` give a morphism to the relevant pullback of `H`. Compose the given equality of reduced homomorphisms with this morphism and the projection to `G`. The projection identity yields equality after precomposing `q` with every quotient of `T`. Separation for `J` follows from separation for `I` by `IsHausdorff.map_algebraMap_iff`.

For the main theorem, choose a finite étale surjective splitting morphism `p : S' ⟶ Spec A`. Its source is affine, so write `B = Γ(S', ⊤)` and replace the cover by `b : Spec B ⟶ Spec A` using `S'.isoSpec.inv`. The ring map recovered by `Spec.preimage b` equips `B` with its `A`-algebra structure. Finiteness of `b` gives `Module.Finite A B`. Completeness of `A` implies `I ≤ Ideal.jacobson ⊥`; the noetherian finite-module separation theorem `IsHausdorff.of_le_jacobson` consequently proves that `B` is separated for `I`.

Pullback comparison transports the supplied relative diagonalizability to the base change along `b`. Unpack its character group `N` and use the published `Diagonalizable.baseChangeIso` to obtain an isomorphism from the standard diagonalizable group with underlying scheme `Spec T`, where `T = AddMonoidAlgebra B N`, to the base change of `H`. The first helper makes `T` separated for `I`. Compose this isomorphism with the projection to `H` to form `q`. Its structural map is `Spec.algebraMap A T`, by the equation for a morphism over `Spec B` and the pullback condition.

The reduction helper proves equality after precomposition with `q`. Cancel the isomorphism in `q` to get equality after the projection from the base change of `H`. This projection is flat and surjective, because `b` is, hence is an epimorphism by `Flat.epi_of_flat_of_surjective`. Cancel it and use the group-object and over-category extensionality lemmas to conclude equality of the original group homomorphisms.

## Dependencies and verification

The module imports the published target, `Torus.DiagonalizableBaseChange`, and Mathlib's `RingTheory.AdicCompletion.Noetherian`. The target and every file it imports are unchanged. The proof uses the Library's actual base-change functor, actual pullback projections and actual group algebra; it introduces no axioms or replacement statement. Compilation and exact declaration inspection are performed with the task's prepared Lean environment. Independent semantic review and official validation are required for acceptance.
