# The hyperext spectral sequence of a t-structure

Author: Worker 61. Built on Mathlib's t-structures
(`Triangulated.TStructure`, its truncation functors and its spectral object
`TStructure.spectralObject`), Mathlib's pretriangulated structure on the
opposite category (`CategoryTheory.Pretriangulated.Opposite`), the homological
functor `preadditiveYoneda.obj B`, and Mathlib's spectral sequence of a
spectral object indexed by `EInt` (`Abelian.SpectralObject.E₂SpectralSequence`).

The module constructs, for a t-structure `t` on a triangulated category `C`
and objects `K` and `B`, the spectral sequence obtained by applying
`Hom(-, B)` to the truncations of `K`. It describes the objects on page 2 and
the intended abutment. Everything is generic in `C`, `t`, `K` and `B`; no
category or complex of Harris is specialized. Convergence is not proved.

## Setting

`C` is a category with objects in `Type u` and morphisms in `Type v`. It is
preadditive, has a zero object and a shift by `ℤ` by additive functors, is
pretriangulated. From `heartPiece_isGE` on it is also triangulated
(`IsTriangulated C`, needed by Mathlib's truncation lemmas and by its spectral
object of a t-structure).
`t : TStructure C` is a t-structure; `t.le n` and `t.ge n` are the objects in
degrees `≤ n` and `≥ n`, with Mathlib's cohomological conventions. `K` and
`B` are objects of `C`. The spectral sequence takes values in
`AddCommGrpCat.{v}`.

## The opposite t-structure

`opTStructure t : TStructure Cᵒᵖ` exchanges the two halves of `t` and negates
degrees: `X` lies in degrees `≤ n` for `opTStructure t` if `X.unop` lies in
`t.ge (-n)`, and in degrees `≥ n` if `X.unop` lies in `t.le (-n)`
(`opTStructure_le_iff`, `opTStructure_ge_iff`, both by definition;
`opTStructure_isLE_iff` and `opTStructure_isGE_iff` restate them for
Mathlib's classes `IsLE`, `IsGE`). `Cᵒᵖ` carries Mathlib's pretriangulated
structure: shifting by `n` on `Cᵒᵖ` corresponds to shifting by `-n` on `C`, and
a triangle of `Cᵒᵖ` is distinguished when it is the image of a distinguished
triangle of `C` under `triangleOpEquivalence` (no signs are introduced). The
axioms are checked from those of `t`:

- closure under isomorphisms and the shift axioms are those of `t` with
  negated degrees;
- orthogonality: a morphism `op X ⟶ op Y` with `X ∈ t.ge 0` and `Y ∈ t.le (-1)`
  is the opposite of a morphism `Y ⟶ X`, which vanishes by
  `t.zero_of_isLE_of_isGE`;
- monotonicity is that of `t`;
- the truncation triangle of `op A` is the image under `op_distinguished` of a
  distinguished triangle `X ⟶ A ⟶ Y ⟶ X⟦1⟧` from `t.exists_triangle A (-1) 0`,
  with `X ∈ t.le (-1)` and `Y ∈ t.ge 0`.

Mathlib has no opposite t-structure; this definition is ours.

## The spectral object and the spectral sequence

Mathlib's `TStructure.spectralObject` attaches to an object `X` a spectral
object indexed by `EInt = WithBotTop ℤ`. Its term on an arrow `a ⟶ b` is the
truncation `τ_{≥ a} τ_{< b} X` (Mathlib's `ω₁`, built from `eTruncLT` and
`eTruncGE`), and its connecting maps come from the truncation triangles.

| Declaration | Meaning |
| --- | --- |
| `hyperextSpectralObject t K B` | The image under `preadditiveYoneda.obj B : Cᵒᵖ ⥤ AddCommGrpCat` (a homological functor on `Cᵒᵖ`) of `(opTStructure t).spectralObject (op K)`, via Mathlib's `SpectralObject.mapHomologicalFunctor`. Its term `H^n(a ⟶ b)` is the group of morphisms in `C` from the `opTStructure t`-truncation of `op K` in degrees `[a, b)`, read in `C`, to `B⟦n⟧`. |
| `hyperextSpectralSequence t K B` | `(hyperextSpectralObject t K B).E₂SpectralSequence`: Mathlib's `E₂CohomologicalSpectralSequence`, with objects indexed by `ℤ × ℤ` and differentials of bidegree `(r, 1 - r)` on page `r ≥ 2`. |

### The pieces of the second page

`heartPiece t K q` is the image in `C` of the `opTStructure t`-truncation
`τ_{≥ q} τ_{< q + 1} (op K)`. It is written with `ω₁` as in the spectral
object; `op_heartPiece` states (by definition) that its opposite is
`((opTStructure t).truncGELT q (q + 1)).obj (op K)`.

- `heartPiece_isLE`: `t.IsLE (heartPiece t K q) (-q)`, from Mathlib's
  `isGE_eTruncGE_obj_obj` for the opposite t-structure.
- `heartPiece_isGE`: `t.IsGE (heartPiece t K q) (-q)`, from Mathlib's instance
  `t.IsLE ((t.truncGELT a b).obj X) (b - 1)` for the opposite t-structure.

Both are instances. So `heartPiece t K q` lies in the heart shifted to degree
`-q`. Classically it is `τ_{≤ -q} τ_{≥ -q} K`, that is, the cohomology object
`H^{-q}(K)` of the heart placed in degree `-q`; this identification is
standard but not formalized here.

### Second page and abutment

| Declaration | Statement |
| --- | --- |
| `secondPageIso t K B p q` | The object in position `(p, q)` on page 2 of `hyperextSpectralSequence t K B` is isomorphic to `AddCommGrpCat.of (heartPiece t K q ⟶ B⟦p + q⟧)`. |
| `abutmentIso t K B n` | The term `H^n(⊥ ⟶ ⊤)` of `hyperextSpectralObject t K B` is `AddCommGrpCat.of (K ⟶ B⟦n⟧)`, by definition (`Iso.refl`). |

`secondPageIso` composes two Mathlib isomorphisms. For the data
`coreE₂Cohomological`, the object in position `(p, q)` on page `r` is the term
`E^{p+q}(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)` of the spectral object
(`spectralSequencePageXIso`); on page 2 this is
`E^{p+q}(q ≤ q ≤ q + 1 ≤ q + 1)`, and `EIsoH` identifies it with
`H^{p+q}(q ⟶ q + 1)`. The last step is the definitional identification of
`H^{p+q}(q ⟶ q + 1)` with morphisms from `heartPiece t K q` to `B⟦p + q⟧`.

`H^n(⊥ ⟶ ⊤)` is the term of the spectral object attached to the whole
object, since `τ_{≥ ⊥}` and `τ_{< ⊤}` are the identity functors. It is the
intended abutment `Hom(K, B⟦p + q⟧)` in total degree `p + q`. Mathlib provides
no convergence theory for these spectral sequences, and convergence is not
proved here. Classically, if `K` is bounded for `t`, that is, `K` lies in
`t.ge a` and `t.le b` for some integers `a` and `b`, then the truncation
filtration of `K` is finite and the spectral sequence converges to
`Hom(K, B⟦p + q⟧)`; this is not formalized. Boundedness cannot be replaced by
the weaker condition that only finitely many `heartPiece t K q` are nonzero,
because no boundedness or nondegeneracy is assumed of `t`. For example, for
the degenerate t-structure in which `t.le n` contains every object and
`t.ge n` only the zero objects, every `heartPiece t K q` is zero, so the second
page vanishes, while for nonzero `K` and `B = K` the term
`Hom(K, K⟦0⟧)` is nonzero.
The differentials are those constructed by Mathlib; they are not described
further here.

## Provenance and interpretation

The construction is a generic, t-structure form of the spectral sequences
used by Harris. Its specialization to Harris's setting is explained here
only; nothing of that setting is defined.

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
75-119 (source `harris-1997-drinfeld-cohomology`), Lemma 6 (ii), printed
p.91 (one-based PDF page 17), states a spectral sequence

`E_2^{i,j} = Ext^i_{smooth G_J-modules}(H_c^{2(n-1)-j}(M_N, Q_ℓ)(n-1), A(G_J, C^p)) ⇒ H^{i+j}(S_{C^p N}, Q_ℓ)`.

In the proof, printed p.95 (one-based PDF page 21), after an isomorphism in
the derived category between `Rf_* Q_ℓ` and
`RHom(Rp_! Q_ℓ(n-1), A(G_J, C^p))` "where we view `A(G_J, C^p)` as a complex
concentrated in degree zero", Harris writes: "Now the spectral sequence (*)
is just the spectral sequence of composite functors associated to this
isomorphism in the derived category." Passing to the limit over `C^p` gives
(8) on the same page.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`),
Proposition 4.10, printed p.311 (one-based PDF page 13), read in the rendered
page scan: "There is a spectral sequence of `𝒪`-modules

(4.10.1) `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, L_ℓ(n-1)), 𝒜_ℓ(GJ, ρ, H)) ⇒ H^{i+j}(S̄_{K(N)}, W̃)`.

Here `Ext^i` denotes the `i`-th derived functor of `Hom` in the category of
smooth `L_ℓ[GJ]`-modules." The finite-level spectral sequences (4.9) on the
same page have the same shape.

Specialization (explanation only). Take for `C` the derived category of the
abelian category of smooth `G_J`-modules (with `Q_ℓ`, respectively `L_ℓ`,
coefficients), for `t` its standard t-structure, for `B` the coefficient
module `A(G_J, C^p)` (respectively `𝒜_ℓ(GJ, ρ, H)`) placed in degree zero, and
for `K` an object with `H^{-q}(K) = H_c^{2(n-1)-q}(M_N)(n-1)`, that is,
compactly supported cohomology shifted by `2(n-1)` and Tate twisted. Then,
by the classical description of `heartPiece` above, `secondPageIso` gives
`E_2^{p,q} = Hom(H^{-q}(K)⟦q⟧, B⟦p + q⟧) = Ext^p(H^{-q}(K), B)`, which is
Harris's `E_2^{p,q}`, and the abutment `Hom(K, B⟦p + q⟧)` is the
`RHom`-cohomology that Harris identifies with the cohomology of the Shimura
variety through his derived-category isomorphism. None of these
identifications is formalized: neither the derived category of smooth
modules, nor the identification of `heartPiece` with the shifted cohomology
object, nor the comparison of `Hom` in the derived category with `Ext`, nor
Harris's geometric isomorphism.

Harris describes his spectral sequence as that "of composite functors". The
construction here filters `K` by its t-truncations, which is the usual
hypercohomology spectral sequence of `RHom(-, B)`. The two have the same
`E_2` terms and abutment after the identifications above; no comparison of
the constructions is formalized.

The Library module `Langlands.Cohomology.HyperextDegeneration.Statement`
(Worker 3) states the degeneration of this spectral sequence as a bijectivity
of an edge map, without constructing the spectral sequence. This module
neither imports nor proves that statement.

## Scope

- Only Mathlib is imported. The module defines no derived category of smooth
  representations, no cohomology of Harris's spaces and no coefficient
  module of Harris.
- Convergence, the edge maps and the differentials beyond Mathlib's
  construction are not stated.
- The identification of `E_2^{p,q}` with `Ext^p(H^{-q}(K), B)` for the
  standard t-structure on a derived category is not made here.
- Equivariance under groups acting on `K` and `B` (Harris's
  `GG(A_f^{ℓ,p})`-equivariance) is not stated.

Source registrations: Harris 1997, `harris-1997-drinfeld-cohomology`, SHA-256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`,
Lemma 6 and its proof read in the text layer of printed pp.91 and 95; Harris
1999, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`,
printed p.311 read in the rendered page scan.

Dependencies are Mathlib only (`Mathlib.Algebra.Homology.SpectralObject.SpectralSequence`,
`Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated`,
`Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`,
`Mathlib.CategoryTheory.Triangulated.Yoneda`), pinned to Lean 4.34.0 and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
