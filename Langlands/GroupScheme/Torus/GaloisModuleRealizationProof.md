# Realization of Galois modules by groups of multiplicative type: proof

Worker 159.

The theorem `Langlands.GroupScheme.multiplicativeTypeGaloisModuleRealization` proves
the proposition `Langlands.GroupScheme.MultiplicativeTypeGaloisModuleRealizationStatement.{u}`
(module `Langlands.GroupScheme.Torus.GaloisModuleRealizationStatement`). It applies the
auxiliary theorem `GaloisModuleRealization.realization_of_diagonalizableCharacter`, which
derives the target from `DiagonalizableCharacterStatement.{u}`, to the published proof
`Langlands.GroupScheme.diagonalizableCharacter` of that statement (module
`Langlands.GroupScheme.Torus.DiagonalizableCharacterProof`). The argument uses only
part 1(b) of `DiagonalizableCharacterStatement`, for the field `L` and the group `M`:
every character of `D_L(M)` is evaluation at exactly one element of `M`.

## The statement

Let `L/k` be a finite Galois extension of fields in the universe `u`, let `M` be a
finitely generated abelian group in the same universe (possibly with torsion), and
let `ρ : Representation ℤ (L ≃ₐ[k] L) M`. The statement asserts a commutative group
scheme `T` over `Spec k`, an isomorphism `i : T_L ≅ D_L(M)` and an additive
isomorphism `e : M ≃+ X^*(T_L)` such that (1) the value of `e m` at a point `x` of
`T_L` is `t(m)`, where `t` is the point `x ≫ i` of `D_L(M)` read as a character of
`M` (`Diagonalizable.characterPointsEquiv`), and (2) `e` intertwines `ρ` with
`characterLattice.galoisRepresentation k L T`. This is the essential surjectivity
in Milne, *Algebraic Groups* (2017), Theorem 12.23 (source ID
`milne-2017-algebraic-groups`), for actions that factor through a finite Galois
extension; the statement's Markdown explains the correspondence.

## The proof

Milne derives Theorem 12.23 from Galois descent. The Lean proof follows the route
of the published torus case `Langlands.GroupScheme.torusGaloisLatticeRealization`
(module `Langlands.GroupScheme.Torus.GaloisLatticeRealizationProof`, by Worker 3483)
and reuses its auxiliary declarations: it realizes `M` as the cokernel of an
equivariant map between permutation lattices and takes `T` to be the kernel of the
corresponding homomorphism of induced tori. Three steps differ from the torus case:
a finite generating set of `M` replaces a basis, the isomorphism `i` is built
explicitly, and bijectivity of `e` comes from the description of the characters
of `D_L(M)` instead of a rank argument. The auxiliary declarations are in the
namespace `Langlands.GroupScheme.GaloisModuleRealization`; none is private.

### Auxiliary declarations

- `sumMap_surjective_of_span`: for a representation `A` on `V` and a family
  `g : I → V` whose `ℤ`-span is everything, the published `sumMap A g` is
  surjective. Its range is a submodule containing every `g i`
  (`sumMap_single`), hence contains their span.
- `charRestrict R a` restricts characters `Multiplicative M →* Γ(U, 𝒪)ˣ` along a
  morphism of test schemes `a : U' ⟶ U` over `Spec R` (postcomposition with
  `Units.map` of `a.left.appTop`).
- `congrPointsEquiv R c U`: for `c : Λ ≃+ M`, the points of `D(Λ)` over `U`,
  read as characters of `M` through `c`
  (`Diagonalizable.characterPointsEquiv` followed by
  `MulEquiv.monoidHomCongrLeft`). `congrPointsEquiv_apply` evaluates it;
  `congrPointsEquiv_naturality` and `characterPointsEquiv_naturality'` show
  that this model and the model `Diagonalizable.characterPointsEquiv R M` of
  `D(M)` are natural for `charRestrict`
  (from `Diagonalizable.characterPointsEquiv_naturality`).
- `diagCongr R c : D(Λ) ≅ D(M)` is `isoOfPointModels` for these two point
  models. `diagCongr_hom`: the point `x ≫ diagCongr` of `D(M)` evaluates at `m`
  as `x` evaluates at `c⁻¹ m` (from `isoOfPointModels_hom`).
- `comp_inv_hom`, `comp_hom_inv`: for an isomorphism `e : G ≅ H` of commutative
  group schemes, moving a point along `e.inv` then `e.hom` (or conversely)
  returns it (from `comp_groupHom_comp`).

### The main argument (`realization_of_diagonalizableCharacter`)

The hypothesis is `hD : DiagonalizableCharacterStatement.{u}`; the final theorem
`multiplicativeTypeGaloisModuleRealization` supplies `diagonalizableCharacter`.

1. `M` is a finitely generated `ℤ`-module (`Module.Finite.iff_addGroup_fg`), so
   `⊤` is spanned by a finite set `S` (`Module.Finite.fg_top`). Let `I = S`,
   `g : I → M` the inclusion, and `π = sumMap ρ g`, which is surjective
   (`sumMap_surjective_of_span`) and equivariant (`sumMap_permRep`). By the
   published `exists_kernel_presentation`, `ker π` is the range of
   `f = sumMap (permRep I) g'` for a finite family `g'` indexed by `I'`.
2. As in the torus case, with `R = permTorus k L I`, `R' = permTorus k L I'` and
   the coordinate equivalences `eR`, `eR'`
   (`WeilGm.productEmbeddingCharacterEquiv`), transport `f` to an equivariant map
   `F : X^*(R'_L) → X^*(R_L)` (`permTorus_equiv_galois`,
   `permTorus_equiv_symm_galois`, `sumMap_permRep`), and obtain `φ : R ⟶ R'`
   over `k` whose base change `φ_L` pulls characters back by `F`
   (`IsSplitTorus.existsUnique_hom_of_equivariant_characterMap`, using
   `permTorus_isSplit`). Put `T = CommGroupScheme.kernel φ`.
3. Let `θ = π ∘ eR : X^*(R_L) → M`; it is surjective and equivariant. The range
   of `characterLattice.comapHom φ_L` is `ker θ`: it is the image of `F`, which
   is `eR⁻¹(range f) = eR⁻¹(ker π)`.
4. The isomorphism `i`: `CommGroupScheme.kernelBaseChangeIso` identifies `T_L`
   with the kernel of `φ_L`; `Diagonalizable.homKernelDiagonalizableIso`
   identifies that kernel with `D_L(Λ)` for
   `Λ = Diagonalizable.homKernelLattice φ_L = X^*(R_L) / range(comapHom φ_L)`;
   and `diagCongr` along `ΛM : Λ ≃+ M` (step 3 and the first isomorphism
   theorem, `QuotientAddGroup.quotientAddEquivOfEq` and
   `QuotientAddGroup.quotientKerEquivOfSurjective`) identifies `D_L(Λ)` with
   `D_L(M)`. `i` is this composite (`CommGroupScheme.isoOfGroupIso`). `ΛM⁻¹`
   sends `θ χ` to the class of `χ` (`hΛM`).
5. The map `e`: restriction along the base-changed inclusion `ι_L : T_L → R_L`
   is `ψ = characterLattice.precompose ι_L`. Since `ι_L` factors as
   `kernelBaseChangeIso` followed by the kernel inclusion of `φ_L`
   (`CommGroupScheme.kernelBaseChangeIso_hom_ι`) and the latter composed with
   `φ_L` is zero (`CommGroupScheme.kernelι_comp`), `ψ` kills
   `range(comapHom φ_L) = ker θ`, so it factors through `ψb : M → X^*(T_L)` with
   `ψb (θ χ) = ψ χ`.
6. Point formula (`hval`, property 1 of the statement for `ψb`): for `m = θ χ`
   and a point `x` of `T_L`, the value of `ψ χ` at `x` is the value of `χ` at the
   point `x ≫ ι_L` of `R_L`. Writing `z` for the image of `x` in `D_L(Λ)`, this
   point is `(z ≫ hk⁻¹) ≫ kernelι`, and
   `Diagonalizable.homKernelDiagonalizableIso_inv` evaluates its value at `χ` as
   `z` evaluated at the class of `χ`. By `diagCongr_hom` and `hΛM` this is the
   point `x ≫ i` of `D_L(M)` evaluated at `ΛM (class of χ) = m`.
7. Bijectivity of `ψb` from part 1(b) of `DiagonalizableCharacterStatement` for
   `L` and `M`: every character of `D_L(M)` is evaluation at exactly one element.
   - Injective: if `ψb m = 0`, then by the point formula (applied to the points
     `y ≫ i⁻¹`, with `comp_inv_hom`) the zero character of `D_L(M)` is
     evaluation at `m`; it is also evaluation at `0` (`comp_groupHom_zero`), so
     uniqueness gives `m = 0`.
   - Surjective: for a character `χ` of `T_L`, the character `i⁻¹ ≫ χ` of
     `D_L(M)` is evaluation at some `m`; by the point formula, `ψb m` and `χ`
     agree on every point (`comp_groupHom_comp`, `comp_hom_inv`), so they are
     equal by `CommGroupScheme.hom_ext_points` (values compared through the
     injective `Gm.pointsEquiv`).

   So `e = AddEquiv.ofBijective ψb` satisfies property 1.
8. Equivariance: as in the torus case, writing `m = θ χ`, both sides of
   `e (ρ σ m) = σ · e m` equal the restriction of `σ χ`, since `θ` is
   equivariant (`permTorus_equiv_galois`, `sumMap_permRep`) and restriction along
   a homomorphism defined over `k` commutes with the Galois action
   (`characterLattice.galoisRepresentation_precompose`).

## Published inputs

Every Library declaration the proof uses, with its module. Names are relative to
`Langlands.GroupScheme` unless written in full.

Theorems and propositions:

- `diagonalizableCharacter` (module
  `Langlands.GroupScheme.Torus.DiagonalizableCharacterProof`), a proof of
  `DiagonalizableCharacterStatement` (module
  `Langlands.GroupScheme.Torus.DiagonalizableCharacterStatement`), the hypothesis of
  `realization_of_diagonalizableCharacter`.
- From `Langlands.GroupScheme.Torus.GaloisLatticeRealizationProof` (namespace
  `GaloisLatticeRealization`): `sumMap_single`, `sumMap_permRep`,
  `exists_kernel_presentation`, `permTorus_isSplit`, `permTorus_equiv_galois`,
  `permTorus_equiv_symm_galois`.
- `IsSplitTorus.existsUnique_hom_of_equivariant_characterMap`
  (`Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent`).
- `Langlands.CommGroupScheme.kernelBaseChangeIso_hom_ι`
  (`Langlands.GroupScheme.Torus.WeilRestrictionNormOneCocharacters`).
- `Langlands.CommGroupScheme.kernelι_comp`
  (`Langlands.GroupScheme.Torus.KernelCocharacters`).
- `Diagonalizable.homKernelDiagonalizableIso_inv`
  (`Langlands.GroupScheme.Torus.HomKernelDiagonalizable`).
- `Diagonalizable.characterPointsEquiv_naturality`
  (`Langlands.GroupScheme.Torus.KernelDiagonalizable`).
- `isoOfPointModels_hom` (`Langlands.GroupScheme.Torus.Split`).
- `comp_groupHom_comp`, `comp_groupHom_zero`, `CommGroupScheme.hom_ext_points`
  (`Langlands.GroupScheme.Torus.Lattice`).
- `characterLattice.galoisRepresentation_precompose`
  (`Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters`).

Definitions and constructions:

- From `Langlands.GroupScheme.Torus.GaloisLatticeRealizationProof`: `Coord`,
  `sumMap`, `permRep`, `permTorus`, `topFamily`.
- `WeilGm.productEmbeddingCharacterEquiv`
  (`Langlands.GroupScheme.Torus.WeilRestrictionProductCharacters`).
- `Langlands.CommGroupScheme.kernel`, `Langlands.CommGroupScheme.kernelι`
  (`Langlands.GroupScheme.Torus.KernelCocharacters`);
  `Langlands.CommGroupScheme.kernelBaseChangeIso`
  (`Langlands.GroupScheme.Torus.WeilRestrictionNormOneCocharacters`);
  `kernelι` (`Langlands.AbelianScheme.Kernel`);
  `Langlands.CommGroupScheme.groupHom`, `Langlands.CommGroupScheme.baseChange`
  (`Langlands.AbelianScheme.GroupScheme`).
- `characterLattice.comapHom`, `Diagonalizable.homKernelLattice`,
  `Diagonalizable.subgroupQuotientMap`,
  `Diagonalizable.homKernelDiagonalizableIso`
  (`Langlands.GroupScheme.Torus.HomKernelDiagonalizable`).
- `Diagonalizable.characterPointsEquiv`
  (`Langlands.GroupScheme.Torus.KernelDiagonalizable`);
  `Diagonalizable.groupScheme` (`Langlands.GroupScheme.Torus.Diagonalizable`).
- `isoOfPointModels`, `IsSplitTorus` (`Langlands.GroupScheme.Torus.Split`);
  `CommGroupScheme.isoOfGroupIso`
  (`Langlands.GroupScheme.Torus.SplitLatticeBaseChange`).
- `characterLattice.precompose`
  (`Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters`);
  `characterLattice.galoisRepresentation`, `algebraBaseMap`
  (`Langlands.GroupScheme.Torus.LatticeGalois`).
- `characterLattice` (`Langlands.GroupScheme.Torus.Lattice`); `Gm.pointsEquiv`
  (`Langlands.GroupScheme.Multiplicative`).

From Mathlib, besides routine lemmas: `Module.Finite.iff_addGroup_fg`,
`Module.Finite.fg_top`, `QuotientAddGroup.quotientAddEquivOfEq`,
`QuotientAddGroup.quotientKerEquivOfSurjective`, `QuotientAddGroup.lift`,
`MulEquiv.monoidHomCongrLeft`, `AddEquiv.ofBijective`.

## Checks

The module compiles against the Library with no errors or warnings (development
check `0210163e-c27c-40b7-b206-baa493caad11` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`), and
`multiplicativeTypeGaloisModuleRealization` depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The module sets
`backward.isDefEq.respectTransparency false` and `maxHeartbeats 800000`, and opens
`CategoryTheory.MonObj` for the group structure on point sets.
