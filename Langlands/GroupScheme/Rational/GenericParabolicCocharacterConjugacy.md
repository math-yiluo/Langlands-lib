# Cocharacters of a dynamic parabolic conjugated into a torus

Author: Worker 3784 (formerly Worker 24).

This module proves the helper results for the rational Bruhat decomposition in
[`RationalBruhatProof`](RationalBruhatProof.md). Their main consequence is
`exists_parabolic_conj_into_torus`. Let `i : T ⟶ G` be a maximal split torus of a
connected reductive group over a field, and let `ν` be a cocharacter of `T` whose dynamic
centralizer is the whole-torus centralizer. Then every cocharacter of `G` with values in
`P_G(ν ≫ i)` is conjugate into `T` by a rational point of `P_G(ν ≫ i)`. All declarations
are in `Langlands.GroupScheme` or `Langlands.GroupScheme.Dynamic`. Nothing here is a
statement for review; these are proofs of internal helper results.

Notation: `S` is a base scheme, or `Spec k` for a field `k : Type u`. `χ : 𝔾_m ⟶ G` is a
cocharacter. `iP : P ⟶ G`, `iZ : Z ⟶ G` and `iU : U ⟶ G` are arbitrary
homomorphisms representing the published all-test functors `Dynamic.parabolic χ`,
`Dynamic.centralizer χ` and `Dynamic.unipotent χ` (`hP`, `hZ`, `hU`). The map
`q = Dynamic.limitGroupHom hP hZ : P ⟶ Z` is the published limit homomorphism.

## The limit homomorphism is an fppf quotient

Here `G` has separated structure morphism.

- `Dynamic.smooth_limitGroupHom`: if `U.X.hom` is smooth, the underlying scheme morphism of
  `q` is smooth. *Proof.* The published `Dynamic.multiplicationIso_inv_snd` writes `q` as the
  inverse of the multiplication isomorphism `U × Z ≅ P` followed by the second projection.
  That projection is the base change of `U.X.hom` along `Z.X.hom`. It is therefore smooth.
  Composing it with an isomorphism keeps it smooth.
- `Dynamic.surjective_limitGroupHom`: `q` is surjective. *Proof.* The published
  `Dynamic.centralizerToParabolic_comp_limitGroupHom` says that the inclusion
  `Z ⟶ P` is a section of `q`. `DynamicConnected.surjective_of_section` then applies.
- `Dynamic.isFppfQuotient_limitGroupHom`: if `U.X.hom` is smooth, then
  `RelativeRoot.IsFppfQuotient (range (kernelι q)) q` holds. Flatness and local finite
  presentation follow from smoothness, and surjectivity from the previous item. The kernel
  condition holds by definition.

## The solvable preimage of a split torus

Let `G` be smooth and affine over `Spec k`.

`exists_solvable_limitGroupHom_preimage` takes the following data:

- instance hypotheses that `P` is smooth, connected and affine, `Z` is affine and `U` is
  smooth;
- a split subtorus `z : T ⟶ Z`.

It gives a group scheme `H` and a closed subgroup `j : H ⟶ P` with these properties:

- `H` is smooth, connected, affine and solvable (`IsSolvableGroupScheme`);
- for every homomorphism `a : K ⟶ P` and every `g : K ⟶ T` with `g ≫ z = a ≫ q`, there is
  an `f : K ⟶ H` with `f ≫ j = a`.

*Proof.* By the published `Dynamic.isRepresentedBy_kernel_limitGroupHom`, the kernel
`kernelι q ≫ iP` represents `Dynamic.unipotent χ`. Since `Z` is affine, hence separated,
`kernelι q` is a closed immersion. By `dynamicSmooth` and `dynamicConnected` the kernel is
smooth and connected. By `dynamicUnipotentUnipotenceReduction`, applied to the published
`unitriangularUnipotent` and `unipotentClosedSubgroup`, it is unipotent. The published
`unipotentQuotientSplitTorusPreimageStatement` applies to `P`, this kernel, the fppf
quotient `q` and the split subtorus `z`. It gives `H` and `j`. On points, `H` is the inverse
image `U_G(χ) ⋊ T` of `T`.

## Conjugating a cocharacter of the parabolic into the torus

- `exists_limit_factor_through_torus`: let `i : T ⟶ G` be a maximal split torus with
  `Dynamic.centralizer χ = torusCentralizer i`, and let `z : T ⟶ Z` satisfy `z ≫ iZ = i`.
  Then for every `ψP : 𝔾_m ⟶ P` there is `f : 𝔾_m ⟶ T` with `f ≫ z = ψP ≫ q`.
  *Proof.* The points of `ψP ≫ q ≫ iZ` lie in `range iZ = Dynamic.centralizer χ`, which is
  `torusCentralizer i`. So on every test scheme they commute with the points of `i`.
  `IsMaximalSplitTorus.exists_factor_of_commute`, applied to the split torus `𝔾_m`
  (`isSplitTorus_gm`), factors this map through `i`. The monomorphism `iZ` is then
  cancelled (`IsRepresentedBy.hom_ext`).
- `exists_parabolic_conj_into_torus_of_represented`: let `G` be smooth, affine and connected.
  Let `iP` and `iZ` be closed, let `U` be smooth, and let `i` be a maximal split torus with
  `Dynamic.centralizer χ = torusCentralizer i` and `range i ≤ Dynamic.centralizer χ`. Then
  for every cocharacter `ψ` of `G` with `range ψ ≤ Dynamic.parabolic χ` there are a point
  `p ∈ (Dynamic.parabolic χ)(k)` and `ρ : 𝔾_m ⟶ T` with `ψ ≫ int(p) = ρ ≫ i`.
  *Proof.* `P` is smooth and connected by `dynamicSmooth` and `dynamicConnected`.
  1. Factor `i` through `iZ` as `z`. It is a split subtorus of `Z`.
  2. Factor `ψ` through `iP` as `ψP`.
  3. The previous item gives `f` with `f ≫ z = ψP ≫ q`.
  4. The solvable preimage `j : H ⟶ P` of `z` receives a lift `ψH` of `ψP`. It also
     receives a lift `tH` of `z ≫ centralizerToParabolic`, whose composite with `q` is `z`
     (`centralizerToParabolic_comp_limitGroupHom`) and whose composite with `iP` is `i`.
  5. By `IsMaximalSplitTorus.of_comp`, `tH` is a maximal split torus of `H`.
  6. The published `cocharacterMaximalSplitTorus`, applied to `H`, factors `ψH` through some
     maximal split torus `iS : S ⟶ H`.
  7. The published `solvableMaximalSplitTorusConjugacy` gives `b ∈ H(k)` and `e : S ≅ T`
     with `iS ≫ int(b) = e ≫ tH`.
  8. Set `p = b ≫ j ≫ iP` and `ρ = ζ ≫ e`, where `ζ` is the cocharacter of `S` from step 6.
     Then `innerIso_hom_comp` gives the equation.
- `exists_parabolic_conj_into_torus`: let `G` be connected reductive, `i` a maximal split
  torus and `ν` a cocharacter of `T` with
  `Dynamic.centralizer (groupHom ν ≫ i) = torusCentralizer i`. Then every cocharacter `ψ`
  with `range ψ ≤ Dynamic.parabolic (groupHom ν ≫ i)` satisfies `ψ ≫ int(p) = ρ ≫ i` for
  some `p ∈ P_G(ν ≫ i)(k)` and some `ρ : 𝔾_m ⟶ T`. *Proof.* Apply the previous result to
  the published closed representatives `Dynamic.Affine.parabolicHom`, `centralizerHom` and
  `unipotentHom`. `range_le_centralizer_groupHom_comp` gives the torus containment. The
  representatives are passed as arguments rather than unfolded inside one proof, which keeps
  kernel checking small.

## Scope and provenance

All equalities are equalities of group-scheme homomorphisms, and all memberships are
memberships of points over the stated test schemes. No splitness of `G`, perfectness,
characteristic, infinitude or rational-point hypothesis is used.

This is internal derived content: a composition of the published results named above.
Mathematically, conjugating `ψ` inside the solvable group `U_G(χ) ⋊ T` replaces the
conjugacy of maximal split tori in parabolic subgroups that the Borel–Tits route uses.
