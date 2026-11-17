# Monic homomorphisms from groups of multiplicative type are closed immersions: proof

Worker 745 wrote this module. It proves

```lean
theorem Langlands.GroupScheme.multiplicativeTypeMonoClosedImmersion :
    MultiplicativeTypeMonoClosedImmersionStatement.{u}
```

for the published statement `Langlands.GroupScheme.MultiplicativeTypeMonoClosedImmersionStatement`
([`MultiplicativeTypeMonoClosedImmersionStatement`](MultiplicativeTypeMonoClosedImmersionStatement.md);
Conrad, *Reductive group schemes* (2014), Lemma B.1.3). For every scheme `S`, every
`G : GroupScheme S` with `IsAffineHom G.X.hom` and `LocallyOfFinitePresentation G.X.hom`,
every `H : GroupScheme S` with `RelativeMultiplicativeType.IsMultiplicativeType H` and every
homomorphism `j : H ⟶ G` with `Mono j.hom.hom`, the underlying morphism of schemes
`j.hom.hom.left` is a closed immersion (`IsClosedSubgroup j`).

The proof does not use the hypothesis `LocallyOfFinitePresentation G.X.hom`, nor that the
character groups in the definition of multiplicative type are finitely generated.

## Route

The route differs from Conrad's. Conrad reduces to a noetherian base, proves properness with
the valuative criterion and concludes with EGA IV₃ 8.11.5. This proof instead uses:

1. Mathlib's `IsClosedImmersion.iff_isProper_and_mono` (Stacks 04XV): a morphism of schemes is
   a closed immersion exactly when it is proper and a monomorphism.
2. fppf locality of properness on the target, from the Library's
   `Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage`
   ([`FppfLocalAtTarget`](../../AlgebraicGeometry/Morphisms/FppfLocalAtTarget.md)) and the
   Library's fpqc descent instance for `IsProper`
   ([`FpqcFiniteDescent`](../../AlgebraicGeometry/Morphisms/FpqcFiniteDescent.md)). This
   reduces the statement to the diagonalizable case.
3. In the diagonalizable case, Zariski locality of closed immersions reduces to an affine base
   `Spec R`. There `H ≅ Spec R[Λ]` and `G = Spec A` for a commutative Hopf algebra `A`. A
   monomorphism of affine schemes corresponds to an epimorphism of rings `A → R[Λ]`. Such a
   Hopf map is surjective by the helper
   [`CommutativeAlgebra/DiagonalHopfEpiSurjective`](../../CommutativeAlgebra/DiagonalHopfEpiSurjective.md),
   so it gives a closed immersion.

## Contents

The auxiliary results are in the namespace `Langlands.GroupScheme.MultiplicativeTypeMono`.

- `epi_of_mono_spec ψ`: for a map `ψ : A ⟶ B` of commutative rings, if `Spec.map ψ` is a
  monomorphism of schemes, then `ψ` is an epimorphism in `CommRingCat`. The functor
  `Scheme.Spec` is faithful, so it reflects monomorphisms, and `ψ.op` is a monomorphism in
  the opposite category.
- `diagonalSource_isClosedImmersion i`: over `Spec R`, let `G` be a group scheme with affine
  total space and `i : diagonalSource R M ⟶ G` a homomorphism from the Hopf spectrum of the
  group algebra `R[M]` (`M` any abelian group) whose underlying scheme map is a monomorphism.
  Then that map is a closed immersion.
  - The Library's `TorusClosedImmersionLocus.diagonalCoordinateMap i` is a bialgebra map
    `φ : A → R[M]`, where `A = AffineCoordinates.hopfAlgebra G`.
    `diagonalCoordinateMap_map` identifies its Hopf spectrum with `i` followed by the
    isomorphism `(AffineCoordinates.hopfSpecIso G).inv`. On underlying schemes, the Hopf
    spectrum of `φ` is `Spec.map φ`. So `Spec.map φ` is the monomorphism `i` followed by an
    isomorphism, hence a monomorphism.
  - By `epi_of_mono_spec`, `φ` is a ring epimorphism. Its range is stable under the
    antipode (the Library's `AffineHomImageHopfAdapter.antipode_mem_range`). The helper
    `DiagonalHopfEpi.surjective_of_epi` then shows that `φ` is surjective.
  - `Spec.map φ` is a closed immersion (`IsClosedImmersion.spec_of_surjective`), and so is
    `i`, since closed immersions are stable under composition with isomorphisms.
- `isClosedSubgroup_of_isDiagonalizable_affine hH j`: over `Spec R`, if `H` is diagonalizable
  (`RelativeMultiplicativeType.IsDiagonalizable`), `G` has affine total space and the
  underlying scheme map of `j : H ⟶ G` is a monomorphism, then `j` is a closed immersion.
  Diagonalizability gives `H ≅ D_{Spec R}(Λ)`. The Library isomorphisms
  `Diagonalizable.hopfSpecIso R Λ` and `Diagonalizable.relativeModelIso R Λ` identify
  `D_{Spec R}(Λ)` with `diagonalSource R Λ`. Applying `diagonalSource_isClosedImmersion` to
  the composite with `j` and cancelling the isomorphism proves the claim.
- `isClosedSubgroup_of_isDiagonalizable hH j`: the same over an arbitrary base `S`, for `G`
  with `IsAffineHom G.X.hom` and `Mono j.hom.hom` in `Over S`.
  - Closed immersion is Zariski local on the target
    (`IsZariskiLocalAtTarget.of_openCover`). Use the cover of `G.X.left` obtained by pulling
    back the affine open cover `S.affineOpenCover.openCover` (members `Spec R_s ⟶ S`) along
    `G.X.hom`.
  - The Library's `TorusIsomorphismLocus.underlying_isPullback b j` identifies the pullback
    of `j.hom.hom.left` along the member over `b : Spec R_s ⟶ S` with the underlying map of
    the base change `(baseChange b).map j`.
  - That base change satisfies the hypotheses of the affine case. Diagonalizability is
    preserved by base change (`IsDiagonalizable.baseChange`). Affineness of `G.X.hom` is
    preserved by pullback, so the base-changed total space is affine over the affine scheme
    `Spec R_s` (`isAffine_of_isAffineHom`). `Over.pullback b` is a right adjoint, so it
    preserves monomorphisms, and a monomorphism in `Over` has a monomorphic underlying map
    (`Over.mono_left_of_mono`).

## Proof of `multiplicativeTypeMonoClosedImmersion`

Let `S`, `G`, `H`, `j` be as in the statement. Choose an fppf cover `𝒰` of `S` with every base
change `H_{S_i}` diagonalizable.

1. The underlying map `j.hom.hom.left` is a monomorphism (`Over.mono_left_of_mono`). By
   `IsClosedImmersion.iff_isProper_and_mono` it remains to prove that it is proper.
2. `IsProper` is local on the target for the fppf precoverage
   (`FppfLocal.isLocalAtTarget_fppfPrecoverage @IsProper`). Its hypotheses are: properness is
   Zariski local on the target and stable under base change (Mathlib), and it descends along
   fpqc, hence fppf, coverings (Library and Mathlib instances). Pull `𝒰` back along `G.X.hom`
   to an fppf cover `𝒱` of `G.X.left` and apply
   `MorphismProperty.IsLocalAtTarget.of_zeroHypercover`. It remains to show that the pullback
   of `j.hom.hom.left` along each member `pullback.fst G.X.hom (𝒰.f i)` is proper.
3. By `TorusIsomorphismLocus.underlying_isPullback`, this pullback agrees, up to an
   isomorphism of sources, with the underlying map of the base change
   `(baseChange (𝒰.f i)).map j`. Its source `H_{S_i}` is diagonalizable. Its target is affine
   over `S_i`, and it is monic over `S_i` (as above). By
   `isClosedSubgroup_of_isDiagonalizable` it is a closed immersion, hence proper.
