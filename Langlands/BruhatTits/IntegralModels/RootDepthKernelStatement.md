# Kernels between actual root-depth models

`UnramifiedRootDepthKernelStatement` is a proposition at arbitrary universe `u`.
It isolates the root-group kernel input in the proof of Kaletha–Prasad
Proposition 8.4.15. It asserts the conclusion of Lemma C.5.3 for arbitrary
supplied presentations of the root models, with the generic compatibility
needed to identify the natural depth map. This file supplies a statement,
not its proof.

Let `F` be a nonarchimedean local field, put `K = inertiaFixedField F` and
`O = fixedFieldIntegers F`, and let `G` be an affine group scheme over `K`.
The supplied `C : MaximalUnramified.BuildingData F G` records that `G` is
connected reductive, its maximal split torus, and compatible apartment and
centralizer data for the actual integer-valued valuation of `K`. No existence
of `C` is asserted. Fix an apartment point `x`, any relative root
`a : relativeRoots C.i`, and real depths `r ≤ s`.

The inputs `U` and `V` are the published `RootFiltrationModelData` at depths
`r` and `s`, respectively. Each includes a generic group, a homomorphism
representing the actual relative-root subgroup on every test scheme, an
affine flat integral model with smooth geometrically connected fibres, and
the exact image of its integral points in `G(K)`. The images are the supplied
apartment filtration groups at those depths. The statement does not replace
the models by these point groups.

The homomorphism `f : V.rootGroup → U.rootGroup` is required to satisfy
`f ≫ U.inclusion = V.inclusion`. Since both inclusions represent the same
root subgroup on every test scheme, this specifies the generic depth
inclusion, allowing different choices of generic representatives. For every
actual integral-model homomorphism `φ : V.model.Hom U.model f`, the conclusion
is that the scheme-theoretic kernel of `φ.specialFibreMap` is smooth, has
connected underlying scheme, and is unipotent over the actual residue field
of `O`. `specialFibreMap` is residue base change; `kernel` is the group-scheme
pullback along the target's unit. `IsUnipotent` is the published predicate on
all finite-dimensional coefficient representations. Connectedness in the
conclusion is `ConnectedSpace`, rather than an additional assertion about
every base change.

The source Lemma C.5.3 concerns the natural map from the constructed depth
`s` model to the depth `r` model. Its proof uses the explicit additive,
trace-zero and unitary models of Facts C.2.1 and C.3.1 and Lemma C.4.4,
assembled by restriction of scalars in Proposition C.5.1. Here the presentation
invariance also uses the smooth-model point-determination and extension
results of Section 2.10, together with generic rigidity: smooth models over
the strictly Henselian ring `O` with the same specified integral points are
compatibly isomorphic. Thus the scope of the statement includes that
comparison step. It is restricted to these maximal unramified integers; it
asserts no corresponding result over an arbitrary domain or for arbitrary
nested subgroups.

Existence of root models, existence of the compatible maps, identification
of integral root subgroups in an ambient model, and an ordered open cell
remain separate obligations. In particular, this proposition does not assert
or prove the kernel theorem for the full parahoric models.

Sources:

- Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), registered
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  Proposition C.5.1 and Lemma C.5.3, printed pp. 703–705 / PDF pp. 734–736;
  Corollaries 2.10.10–2.10.11 and Remark 2.10.19, printed pp. 124–127 /
  PDF pp. 155–158; Proposition 8.4.15, printed pp. 306–307 / PDF
  pp. 337–338, for the intended consumer.
- Authors' corrections of 1 November 2024, registered
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:
  PDF pp. 37–38, for the corrected Chapter 8 setting used by that consumer.
  These corrections do not amend Lemma C.5.3.
