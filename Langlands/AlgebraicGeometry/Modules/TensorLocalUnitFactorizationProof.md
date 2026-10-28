# Proof of local unit factorization for a tensor-invertible pair

This module proves the published proposition
`Langlands.Scheme.Modules.TensorLocalUnitFactorizationStatement` from
`Langlands.AlgebraicGeometry.Modules.TensorLocalUnitFactorizationStatement`,
which it imports unchanged.

## Main result

`Langlands.Scheme.Modules.tensorLocalUnitFactorization` is the theorem

```lean
theorem tensorLocalUnitFactorization (X : AlgebraicGeometry.Scheme.{u}) :
    TensorLocalUnitFactorizationStatement X
```

for an arbitrary universe `u`, with no hypothesis on `X`. Thus for all
`M N : X.Modules`, every `e : M ⊗ N ≅ 𝟙_ X.Modules` and every `x : X`, it
gives an open `W` with `x ∈ W` and morphisms
`s : 𝟙_ W.toScheme.Modules ⟶ M.restrict W.ι` and
`t : 𝟙_ W.toScheme.Modules ⟶ N.restrict W.ι` such that `IsIso (s ⊗ₘ t)`.
Here `⊗` and `⊗ₘ` are the published localized monoidal structure.

## Imports

- `Langlands.AlgebraicGeometry.Modules.TensorLocalFiniteDecompositionProof`,
  for the published theorem `tensorLocalFiniteDecomposition`.
- `Langlands.AlgebraicGeometry.Modules.TensorSections` and
  `Langlands.AlgebraicGeometry.Modules.StructureUnitScalars`. They provide the
  section morphisms `Langlands.SchemeModule.sectionHom` with
  `sectionHom_app_one`, and the scalar endomorphisms of the structure module:
  `structureEndValue`, `structureEnd_ext`, `structureMulHom`,
  `structureEndValue_mulHom` and `structureAutOfUnit`.
- `Langlands.AlgebraicGeometry.Modules.RestrictTensorProof`, for the
  published theorem `restrictTensorComparison X :
  RestrictTensorComparisonStatement X`. The comparison
  `restrictTensorHom W M N : tensorObj (M.restrict W.ι) (N.restrict W.ι) ⟶
  (tensorObj M N).restrict W.ι` is defined in the published
  `Langlands.AlgebraicGeometry.Modules.RestrictTensor`, and the statement is
  in `Langlands.AlgebraicGeometry.Modules.RestrictTensorStatement`. This proof
  uses the two clauses of the theorem:
  `(restrictTensorComparison X W M N).1`, that `restrictTensorHom W M N` is an
  isomorphism, and `(restrictTensorComparison X W M N).2`, its value on
  sheafified pure tensors of sections. It also uses the published lemma
  `tensorSheafifyUnit_comp_tensorHomEquiv_symm` from the same module: for
  module sheaves `P Q T` and a presheaf map `f : P.val ⊗ Q.val ⟶ T.val`,
  `tensorSheafifyUnit P Q ≫ ((tensorHomEquiv P Q T).symm f).val = f`.

## Auxiliary lemmas

All are in namespace `Langlands.Scheme.Modules`. `tensorObj`, `tensorMap`,
`tensorSheafifyUnit` and `tensorLeftUnitor` are the explicit sheafified tensor
constructions of `Tensor` and `PullbackTensor`. `structureSheaf Y` is the
structure module.

- `tensorLeftUnitor_hom_eq`: `(tensorLeftUnitor P).hom` is the transpose under
  `tensorHomEquiv` of the presheaf left unitor `(λ_ P.val).hom`. This is the
  adjunction's `homEquiv_counit`.
- `tensorLeftUnitor_hom_app_one` and `tensorLeftUnitor_inv_app_one`: over any
  open `V`, the left unitor of `tensorObj (structureSheaf Y) (structureSheaf Y)`
  sends the sheafified pure tensor of `1` with `1` to `1`, and its inverse
  sends `1` back to that sheafified pure tensor. The first follows from
  `tensorLeftUnitor_hom_eq`, the published
  `tensorSheafifyUnit_comp_tensorHomEquiv_symm` and
  `1 • 1 = 1`. The second
  applies `hom_inv_id` to that element.
- `tensorUnitValue E V m n` is the scalar
  `E.val.app (op V) ((tensorSheafifyUnit M N).app (op V) (m ⊗ₜ n)) : Γ(X, V)`,
  for `E : tensorObj M N ⟶ structureSheaf X`, `m ∈ M(V)` and `n ∈ N(V)`.
  `tensorUnitValue_res` states that it commutes with restriction to `W ≤ V`,
  by naturality of `tensorSheafifyUnit M N` and of `E.val`.
- `sectionHom_app_top_one`: `sectionHom P s` sends `1 ∈ Γ(Y, ⊤)` to `s`. This
  is `sectionHom_app_one` with the identity restriction.
- `structureEndValue_restrictTensor`: for `E`, an open `W`, and global
  sections `mW` of `M.restrict W.ι` and `nW` of `N.restrict W.ι`, consider the
  endomorphism of the structure module of `W`

  ```text
  (tensorLeftUnitor 𝒪_W).inv ≫ tensorMap (sectionHom _ mW) (sectionHom _ nW)
    ≫ restrictTensorHom W M N ≫ (restrictFunctor W.ι).map E
    ≫ (restrictUnitIso W.ι).hom.
  ```

  Its value `structureEndValue _ ⊤` on `1` is
  `(W.ι.appIso ⊤).hom (tensorUnitValue E (W.ι ''ᵁ ⊤) mW nW)`. The proof
  follows `1` through the composite. It uses `tensorLeftUnitor_inv_app_one`,
  then `tensorSheafifyUnit_naturality` with `sectionHom_app_top_one`, then
  the value clause `(restrictTensorComparison X W M N).2` at `⊤`. At `⊤`, `(restrictFunctor W.ι).map E` acts as
  `E` at `W.ι ''ᵁ ⊤` and `(restrictUnitIso W.ι).hom` acts as
  `(W.ι.appIso ⊤).hom`; the final step is `rfl`.
- `isIso_tensorMap_sectionHom_of_isUnit`: if `E` is an isomorphism and
  `tensorUnitValue E (W.ι ''ᵁ ⊤) mW nW` is a unit, then
  `tensorMap (sectionHom _ mW) (sectionHom _ nW)` is an isomorphism. Let
  `R` be the composite
  `restrictTensorHom W M N ≫ (restrictFunctor W.ι).map E ≫ (restrictUnitIso W.ι).hom`.
  It is an isomorphism as a composite of the isomorphism
  `restrictTensorHom W M N` (clause `(restrictTensorComparison X W M N).1`),
  the image of `E` under a functor, and an isomorphism `hom`. By `structureEnd_ext`, `structureEndValue_restrictTensor`
  and `structureEndValue_mulHom`,
  `(tensorLeftUnitor _).inv ≫ tensorMap _ _ ≫ R` equals multiplication by the
  unit `(W.ι.appIso ⊤).hom (tensorUnitValue …)`, namely
  `(structureAutOfUnit _).hom`. Hence `tensorMap _ _ ≫ R` equals
  `(tensorLeftUnitor _).hom ≫ (structureAutOfUnit _).hom`, which is an
  isomorphism. Cancelling the isomorphism `R` on the right
  (`isIso_comp_right_iff`) gives the claim.

`structureEndValue_restrictTensor` is compiled with
`set_option backward.isDefEq.respectTransparency false`, a local elaboration
option that changes no statement.

## Proof of the main theorem

Fix `M`, `N`, `e` and `x`.

1. **The pairing and the preimage of one.** Let
   `E := (localizedTensorIso X M N).symm ≪≫ e : tensorObj M N ≅ structureSheaf X`.
   Let `z := E.inv` applied to `1 ∈ Γ(X, ⊤)`; `z` is a global section of the
   sheafified tensor `tensorObj M N`.
2. **Finite expansion.** The published theorem
   `tensorLocalFiniteDecomposition X M N ⊤ z x` gives an open `V` with
   `x ∈ V`, a number `k`, and sections `s i ∈ M(V)`, `t i ∈ N(V)` such that
   `(tensorSheafifyUnit M N).app (op V) (∑ i, s i ⊗ₜ t i)` is the restriction
   of `z` to `V`. No section of the sheafified tensor is identified with an
   algebraic tensor of sections beyond this local equation.
3. **The scalar terms sum to one.** Apply `E.hom` at `V`. The unit component
   and `E.hom` are additive (`map_sum`), and `E.hom` commutes with restriction.
   Also `E.hom z = 1` by `E.inv_hom_id`, and restriction maps preserve `1`.
   Hence `∑ i, tensorUnitValue E.hom V (s i) (t i) = 1` in `Γ(X, V)`.
4. **A unit germ.** Apply the germ map `X.presheaf.germ V x` to this sum. The
   stalk at `x` is a local ring, and the germs of the terms sum to one, which
   is a unit. Mathlib's `IsLocalRing.exists_of_isUnit_sum` gives an index `i`
   such that the germ of `a := tensorUnitValue E.hom V (s i) (t i)` is a unit.
   Only scalars in `Γ(X, V)` pass to the stalk; no tensor/stalk comparison
   is used.
5. **Shrinking.** Let `W := X.basicOpen a`. Then `x ∈ W` by
   `X.mem_basicOpen`, and `W.ι ''ᵁ ⊤ ≤ V`. Restrict `s i` and `t i` to
   `W.ι ''ᵁ ⊤`. The results are global sections `mW` of `M.restrict W.ι` and
   `nW` of `N.restrict W.ι`. By `tensorUnitValue_res`, their scalar is the
   restriction of `a` to `W.ι ''ᵁ ⊤`. That restriction is a unit, since `a`
   is a unit on its basic open (`isUnit_res_basicOpen`) and ring maps
   preserve units.
6. **The tensor of the section morphisms.** Take
   `s := sectionHom (M.restrict W.ι) mW` and
   `t := sectionHom (N.restrict W.ι) nW`. Their source is the structure
   module of `W`, which is the monoidal unit `𝟙_ W.toScheme.Modules`.
   `isIso_tensorMap_sectionHom_of_isUnit` shows that `tensorMap s t` is an
   isomorphism.
7. **Back to the monoidal tensor.** Naturality of
   `localizedTensorNatIso W.toScheme : tensor W.toScheme.Modules ≅ tensorFunctor W.toScheme`
   at the pair `(s, t)` gives
   `(s ⊗ₘ t) ≫ φ_(M|_W, N|_W) = φ_(𝒪_W, 𝒪_W) ≫ tensorMap s t`, where `φ` is
   that natural isomorphism. The right side is an isomorphism, so
   `(s ⊗ₘ t) ≫ φ_(M|_W, N|_W)` is one. Cancelling `φ` on the right gives
   `IsIso (s ⊗ₘ t)`.

The witnesses are `W`, `x ∈ W`, `s` and `t`.

## Relation to the source

The source is the registered
`stacks-local-freeness-invertibility-sections-2026-10-21` (file `01CR.html`).
Step 2 is the local finite pure-tensor expansion of the preimage of one in
the proof of Lemma 17.25.2 (tag 0B8K). That lemma is proved here only in the
form of the published `tensorLocalFiniteDecomposition`. The converse proof
of Lemma 17.25.4 (tag 0B8M) uses finite presentation and spreads a stalk
basis via Lemma 17.11.7. This proof does not follow that route. It uses the
unit-pairing argument above, which needs only that the stalks of `𝒪_X` are
local rings, and that holds for every scheme. The proposition is the internal
interface specified by Worker 124. This module proves only the invertibility
of `s ⊗ₘ t`; individual invertibility of `s` or `t`, local freeness of
rank one, and the reverse implication are not proved here.

## Verification

The development check of this module, compiled against Library commit
`a2f65909`, which contains the published definitions, statement and proof of
the restriction comparison, passes with zero errors and zero warnings at the
default heartbeat limit. The theorem depends
only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
