# The second page of the hyperext spectral sequence in a derived category

Author: Worker 61. Built on the Library module
`Langlands.Cohomology.HyperextSpectralSequence` (the opposite t-structure
`opTStructure`, the pieces `heartPiece`, the spectral sequence
`hyperextSpectralSequence` and its page isomorphism `secondPageIso`), and on
Mathlib's derived categories (`DerivedCategory`, its standard t-structure
`DerivedCategory.TStructure.t`, the functors `singleFunctor` and
`homologyFunctor`, the long exact cohomology sequences of distinguished
triangles) and Mathlib's `Abelian.Ext`.

The module identifies the second page of the hyperext spectral sequence for
the standard t-structure on a derived category: for an object `K` of the
derived category and an object `W` of the abelian category placed in degree
zero, the object in position `(p, q)` on page 2 is `Ext^p(H^{-q}(K), W)` for
`p ≥ 0` and zero for `p < 0`. The main step, made precise here, is the
classical fact that `heartPiece TStructure.t K q` is the cohomology object
`H^{-q}(K)` placed in degree `-q`; the module
`Langlands.Cohomology.HyperextSpectralSequence` only explained it. Convergence
of the spectral sequence is not proved.

## Setting

The first part (section `Generic`) works, like
`Langlands.Cohomology.HyperextSpectralSequence`, in a pretriangulated
category `C` (objects in `Type u`, morphisms in `Type v`) with a t-structure
`t` and an object `K`. Degrees follow Mathlib's cohomological conventions:
`t.le n` and `t.ge n` are the objects in degrees `≤ n` and `≥ n`. The
opposite t-structure `opTStructure t` on `Cᵒᵖ` exchanges the halves and
negates degrees, so the truncation `τ_{< q + 1}` for `opTStructure t`
corresponds to the truncation of `K` in degrees `≥ -q` for `t`.

The second part (section `Derived`) takes an abelian category `C` (objects in
`Type u`, morphisms in `Type v`) with `HasDerivedCategory.{w} C`, so that
morphisms of `DerivedCategory C` lie in `Type w` and the hyperext spectral
sequence takes values in `AddCommGrpCat.{w}`. `TStructure.t` is Mathlib's
standard t-structure on `DerivedCategory C`, `H^n` is
`DerivedCategory.homologyFunctor C n`, and `(singleFunctor C n).obj M` is `M`
placed in degree `n`. The Ext groups are Mathlib's `Abelian.Ext`, defined by
`HasExt.{w'} C` as morphisms in the derived category; `secondPageExtIso`
uses `HasExt.{w} C`, the same universe as the morphisms of the derived
category, so that both sides are objects of `AddCommGrpCat.{w}`.

## Two truncation triangles

All of these are generic in `C` and `t`.

| Declaration | Meaning |
| --- | --- |
| `upperPiece t K q` | The image in `C` of `τ_{< q + 1} (op K)` for `opTStructure t`, that is, the truncation of `K` in degrees `≥ -q`. |
| `toUpperPiece t K q : K ⟶ upperPiece t K q` | The image in `C` of the truncation map `τ_{< q + 1} (op K) ⟶ op K`. |
| `heartPieceToUpperPiece t K q : heartPiece t K q ⟶ upperPiece t K q` | The image in `C` of the truncation map `τ_{< q + 1} (op K) ⟶ τ_{≥ q} τ_{< q + 1} (op K)`. |
| `upperTriangle t K q` | The triangle `X ⟶ K ⟶ upperPiece t K q ⟶ X⟦1⟧` of `C` obtained from the truncation triangle of `op K` at `q + 1` for `opTStructure t` by the inverse of Mathlib's `triangleOpEquivalence`. Its first object `X` lies in `t.le (-(q + 1))` (instance `upperTriangle_obj₁_isLE`), and its second morphism is `toUpperPiece t K q` (`upperTriangle_mor₂`, by definition). |
| `heartTriangle t K q` | The triangle `heartPiece t K q ⟶ upperPiece t K q ⟶ Z ⟶ (heartPiece t K q)⟦1⟧` obtained in the same way from the truncation triangle at `q` of `τ_{< q + 1} (op K)`. Its third object `Z` lies in `t.ge (-(q - 1))` (instance `heartTriangle_obj₃_isGE`), and its first morphism is `heartPieceToUpperPiece t K q` (`heartTriangle_mor₁`, by definition). |

`upperTriangle_distinguished` and `heartTriangle_distinguished`: both
triangles are distinguished, by Mathlib's `unop_distinguished` applied to the
distinguished truncation triangles of `opTStructure t`
(`triangleLTGE_distinguished`).

Classically, `upperTriangle` is `τ_{≤ -q-1} K ⟶ K ⟶ τ_{≥ -q} K ⟶` and
`heartTriangle` is `τ_{≤ -q} τ_{≥ -q} K ⟶ τ_{≥ -q} K ⟶ τ_{≥ -q+1} K ⟶`.

The section also contains three elementary additive equivalences of
morphism groups, used below: `precompAddEquiv e Y : (X' ⟶ Y) ≃+ (X ⟶ Y)`,
`f ↦ e.hom ≫ f`, for `e : X ≅ X'`; `postcompAddEquiv X e : (X ⟶ Y) ≃+ (X ⟶ Y')`,
`f ↦ f ≫ e.hom`, for `e : Y ≅ Y'`; and `shiftAddEquiv X Y n :
(X ⟶ Y) ≃+ (X⟦n⟧ ⟶ Y⟦n⟧)`, the action of the shift functor by `n` on
morphisms (bijective because the shift functor is an equivalence).

## The heart piece is the shifted cohomology object

In the derived category:

- `isIso_homologyMap_toUpperPiece` (instance): `H^{-q}` of
  `toUpperPiece TStructure.t K q` is an isomorphism. In the long exact
  cohomology sequence of `upperTriangle`, the first object has zero
  cohomology in degrees `-q` and `-q + 1`, since it lies in degrees
  `≤ -q - 1`; so the map is a monomorphism and an epimorphism (Mathlib's
  `homologySequence_mono_shift_map_mor₂_iff` and
  `homologySequence_epi_shift_map_mor₂_iff`).
- `isIso_homologyMap_heartPieceToUpperPiece` (instance): `H^{-q}` of
  `heartPieceToUpperPiece TStructure.t K q` is an isomorphism, in the same
  way from `heartTriangle`, whose third object has zero cohomology in degrees
  `-q - 1` and `-q`.
- `heartPieceHomologyIso K q : H^{-q}(heartPiece TStructure.t K q) ≅ H^{-q}(K)`
  is the second of these isomorphisms (`H^{-q}` of `heartPieceToUpperPiece`,
  from `H^{-q}(heartPiece TStructure.t K q)` to `H^{-q}(upperPiece TStructure.t K q)`)
  followed by the inverse of the first (`H^{-q}` of `toUpperPiece`, from
  `H^{-q}(K)` to `H^{-q}(upperPiece TStructure.t K q)`).

Objects concentrated in one degree:

- `singleFunctor_hom_ext`: two morphisms
  `(singleFunctor C n).obj A ⟶ (singleFunctor C n).obj B` are equal if they
  induce the same morphism on `H^n`. The proof uses that `singleFunctor C n`
  is full, and Mathlib's natural isomorphism
  `singleFunctorCompHomologyFunctorIso C n : singleFunctor C n ⋙ homologyFunctor C n ≅ 𝟭 C`.
- `chosenSingleIso X n` is an isomorphism from an object `X` lying in degrees
  `≥ n` and `≤ n` to some `(singleFunctor C n).obj Y`, chosen by Mathlib's
  existence statement `exists_iso_singleFunctor_obj_of_isGE_of_isLE`. It is
  only an auxiliary step.
- `isoSingleHomology X n : X ≅ (singleFunctor C n).obj (H^n X)` composes
  `chosenSingleIso X n` with the image under `singleFunctor C n` of the
  isomorphism `Y ≅ H^n((singleFunctor C n).obj Y) ≅ H^n X` given by
  `singleFunctorCompHomologyFunctorIso` and by `H^n` of the inverse of
  `chosenSingleIso X n`.
- `homologyFunctor_map_isoSingleHomology_hom`: `H^n` of
  `isoSingleHomology X n`, followed by the canonical isomorphism
  `H^n((singleFunctor C n).obj (H^n X)) ≅ H^n X`, is the identity.
- `eq_isoSingleHomology_hom`: every morphism
  `X ⟶ (singleFunctor C n).obj (H^n X)` with this property equals
  `(isoSingleHomology X n).hom`.

The last two statements characterize `isoSingleHomology X n` without
reference to the choice: it is the unique morphism inducing the inverse of the
canonical identification on `H^n`. In particular it does not depend on the
isomorphism chosen in `chosenSingleIso`.

Finally:

- `heartPieceIso K q : heartPiece TStructure.t K q ≅ (singleFunctor C (-q)).obj (H^{-q}(K))`
  is `isoSingleHomology` at `n = -q` (the instances `heartPiece_isLE` and
  `heartPiece_isGE` of `Langlands.Cohomology.HyperextSpectralSequence` say
  that `heartPiece TStructure.t K q` lies in degrees `≤ -q` and `≥ -q`),
  followed by the image under `singleFunctor C (-q)` of
  `heartPieceHomologyIso K q`.
- `homologyFunctor_map_heartPieceIso_hom`: `H^{-q}` of `heartPieceIso K q`,
  followed by the canonical isomorphism
  `H^{-q}((singleFunctor C (-q)).obj (H^{-q} K)) ≅ H^{-q} K`, is
  `heartPieceHomologyIso K q`. Together with `singleFunctor_hom_ext` this
  determines `heartPieceIso K q`.

## The second page

Let `W` be an object of `C`, `W₀ = (singleFunctor C 0).obj W`, and
`M = H^{-q}(K)`.

| Declaration | Statement |
| --- | --- |
| `secondPageExtAddEquiv K W p q` | For `p : ℕ`, an additive equivalence `(heartPiece TStructure.t K q ⟶ W₀⟦p + q⟧) ≃+ Ext^p(M, W)`, with `Ext` in any universe `w'`. |
| `secondPageExtIso K W p q` | For `p : ℕ` and `HasExt.{w} C`, the object in position `(p, q)` on page 2 of `hyperextSpectralSequence TStructure.t K W₀` is isomorphic to `AddCommGrpCat.of (Ext^p(M, W))`. |
| `isZero_secondPage_of_neg K W p q hp` | For integers `p < 0` and `q`, the object in position `(p, q)` on page 2 of `hyperextSpectralSequence TStructure.t K W₀` is zero. |

`secondPageExtAddEquiv` sends `f : heartPiece TStructure.t K q ⟶ W₀⟦p + q⟧`
to the following composite of steps:

1. `(heartPieceIso K q).inv ≫ f : (singleFunctor C (-q)).obj M ⟶ W₀⟦p + q⟧`;
2. precomposition with `((singleFunctor C 0).obj M)⟦q⟧ ≅ (singleFunctor C (-q)).obj M`,
   the component at `M` of Mathlib's `(singleFunctors C).shiftIso q (-q) 0`;
3. postcomposition with `W₀⟦p + q⟧ ≅ W₀⟦p⟧⟦q⟧`, the component of
   `shiftFunctorAdd' (DerivedCategory C) p q (p + q)`;
4. the inverse of `shiftAddEquiv`, giving a morphism
   `(singleFunctor C 0).obj M ⟶ W₀⟦p⟧`;
5. the inverse of Mathlib's `Abelian.Ext.homAddEquiv`, which identifies
   `Ext^p(M, W)` with such morphisms.

Each step is an additive equivalence. The result depends on the shift
identifications used in steps 2 and 3; no compatibility with differentials,
with edge maps or with other identifications of `E_2` is claimed.

`secondPageExtIso` is `secondPageIso TStructure.t K W₀ p q` of
`Langlands.Cohomology.HyperextSpectralSequence`, which identifies the page-2
object with `heartPiece TStructure.t K q ⟶ W₀⟦p + q⟧`, followed by
`secondPageExtAddEquiv` viewed as an isomorphism of abelian groups.

`isZero_secondPage_of_neg`: by `secondPageIso` the object is
`heartPiece TStructure.t K q ⟶ W₀⟦p + q⟧`. Here `heartPiece TStructure.t K q`
lies in degrees `≤ -q`, and `W₀⟦p + q⟧` lies in degrees `≥ -(p + q)`
(Mathlib's instance that `W₀` lies in degrees `≥ 0`, and `isGE_shift`). Since
`-q < -(p + q)` when `p < 0`, every such morphism is zero
(`zero_of_isLE_of_isGE`).

So page 2 has the expected shape `E_2^{p,q} = Ext^p(H^{-q}(K), W)`, zero for
`p < 0`. The intended abutment, by `abutmentIso` of
`Langlands.Cohomology.HyperextSpectralSequence`, is the group
`Hom(K, W₀⟦p + q⟧)` of morphisms in the derived category (the hyperext of `K`
and `W` in degree `p + q`). Convergence is not proved; as
explained in that module, classically the spectral sequence converges when
`K` is bounded, that is, when `K` lies in degrees `≥ a` and `≤ b` for some
integers `a` and `b`, and this is not formalized.

## Provenance and interpretation

The module makes precise, for the standard t-structure on a derived
category, the `E_2` terms of the spectral sequences used by Harris. The
quotations below are those of `Langlands.Cohomology.HyperextSpectralSequence`.

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
75-119 (source `harris-1997-drinfeld-cohomology`), Lemma 6 (ii), printed
p.91 (one-based PDF page 17), states a spectral sequence

`E_2^{i,j} = Ext^i_{smooth G_J-modules}(H_c^{2(n-1)-j}(M_N, Q_ℓ)(n-1), A(G_J, C^p)) ⇒ H^{i+j}(S_{C^p N}, Q_ℓ)`,

and its proof, printed p.95 (one-based PDF page 21), obtains it as "the
spectral sequence of composite functors associated to this isomorphism in the
derived category", where `A(G_J, C^p)` is viewed "as a complex concentrated
in degree zero".

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`),
Proposition 4.10, printed p.311 (one-based PDF page 13), states

(4.10.1) `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, L_ℓ(n-1)), 𝒜_ℓ(GJ, ρ, H)) ⇒ H^{i+j}(S̄_{K(N)}, W̃)`,

"Here `Ext^i` denotes the `i`-th derived functor of `Hom` in the category of
smooth `L_ℓ[GJ]`-modules."

Specialization (explanation only). Take for `C` the abelian category of
smooth `G_J`-modules (with `Q_ℓ`, respectively `L_ℓ`, coefficients), for `W`
the coefficient module `A(G_J, C^p)` (respectively `𝒜_ℓ(GJ, ρ, H)`), so that
`W₀` is `W` viewed as a complex concentrated in degree zero, and for `K` an
object of the derived category with
`H^{-q}(K) = H_c^{2(n-1)-q}(M_N)(n-1)`, that is, compactly supported
cohomology shifted by `2(n-1)` and Tate twisted. Then `secondPageExtIso`
gives `E_2^{p,q} = Ext^p(H_c^{2(n-1)-q}(M_N)(n-1), W)`, which has the shape
of Harris's `E_2^{i,j}` with `(i, j) = (p, q)`, and `isZero_secondPage_of_neg`
gives the vanishing for `p < 0`, consistent with `Ext^i = 0` for `i < 0`.
Nothing of this specialization is formalized: no derived category of smooth
modules with its `HasDerivedCategory` and `HasExt` instances, no complex `K`
of Harris, and no comparison of Mathlib's `Abelian.Ext` (morphisms in the
derived category) with Harris's derived functors of `Hom` or with the
Library's `Langlands.Cohomology.SmoothExt`. Classically, in an abelian
category with enough injectives, such as a category of smooth
representations, morphisms in the derived category compute the derived
functors of `Hom`.

The Library module `Langlands.Cohomology.HyperextDegeneration.Statement`
(Worker 3) states the degeneration of the spectral sequence
`Ext^p(H^{-q} K, W) ⇒ Hom(K, W⟦p + q⟧)` as bijectivity of an edge map,
without constructing the spectral sequence. This module neither imports nor
proves that statement, and does not compare its edge map with the spectral
sequence.

## Scope

- The `E_2` identification is made for the standard t-structure on
  `DerivedCategory C` and a second argument `W` placed in degree zero. Other
  second arguments (complexes) are not treated.
- Convergence, differentials and edge maps are not stated.
- No derived category of smooth representations, no cohomology of Harris's
  spaces and no coefficient module of Harris is defined. Equivariance under
  groups acting on `K` and `W` is not stated.

Source registrations: Harris 1997, `harris-1997-drinfeld-cohomology`, SHA-256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`,
Lemma 6 and its proof read in the text layer of printed pp.91 and 95; Harris
1999, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`,
printed p.311 read in the rendered page scan.

Dependencies: `Langlands.Cohomology.HyperextSpectralSequence` and Mathlib
(`Mathlib.Algebra.Category.Grp.Zero`,
`Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`,
`Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`,
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
`Mathlib.Algebra.Homology.DerivedCategory.TStructure`), pinned to Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
