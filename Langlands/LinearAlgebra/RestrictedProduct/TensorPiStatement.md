# Tensoring a finitely presented module with an arbitrary product: statement

Author: Worker 376.

`RestrictedProduct.TensorPiComparison` is a proposition target. It is not a
theorem, and nothing in this module assumes it. The module states the target
and proves nothing.

## The target

```
def RestrictedProduct.TensorPiComparison.{uR, uM, uι, uN} : Prop :=
  ∀ (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] {ι : Type uι} (N : ι → Type uN)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)],
    Function.Bijective (TensorProduct.piRightHom R R M N)
```

The proposition says the following. Let `R` be a commutative ring and `M` a
finitely presented `R`-module. Let `ι` be any index type and `N i` any family
of `R`-modules. Then Mathlib's canonical `R`-linear map

```
TensorProduct.piRightHom R R M N : M ⊗[R] (Π i, N i) →ₗ[R] Π i, M ⊗[R] N i
```

is bijective. On pure tensors this map is `m ⊗ f ↦ (i ↦ m ⊗ f i)`. This formula
is Mathlib's `TensorProduct.piRightHom_tmul`, which holds by `rfl`.

The four universe parameters `uR`, `uM`, `uι` and `uN` of the ring, the module,
the index type and the coordinate family are independent. All parameters are
quantified inside the proposition, so the definition itself has no arguments,
and its full unapplied type is `Prop`. The binders follow the source section
variables (below): `R`, `M` and `N` are explicit and `ι` is implicit. A proof
`h : TensorPiComparison` is applied as `h R M N`. Its instance arguments are
found by instance search.

Mathlib's `piRightHom` has two scalar rings, `R` and `S`, and needs an
`R`-algebra `S`, an `S`-module structure on `M` and `IsScalarTower R S M`. The
target uses it with `S := R`. A `pp.explicit` print of the elaborated body in a
private check shows exactly what gets inserted. The algebra is `Algebra.id R`.
The one hypothesis `[Module R M]` is used for both module arguments. The
scalar-tower argument is found by instance search. So the map in the target is
the plain `R`-linear map, with no extra scalar structure.

## What is not assumed

- There is no finiteness hypothesis on `ι`. It may be infinite, and it may be
  empty.
- `M` is assumed finitely presented, and nothing more. There is no freeness,
  projectivity or flatness hypothesis on `M`, and none on the `N i`.
- There is no hypothesis that some tensor equivalence or bijection exists. The
  map is Mathlib's existing `piRightHom`, not a new map or an equivalence.

`R` is a commutative ring, and `M` and the `N i` are additive commutative
groups. These are the source hypotheses. Mathlib's `piRightHom` itself is
defined more generally, over commutative semirings and for additive
commutative monoids, but the target keeps the source's hypotheses.

For a finite index type, Mathlib already proves the bijection: the map is the
underlying map of the equivalence `TensorProduct.piRight`
(`Mathlib/LinearAlgebra/TensorProduct/Pi.lean`, lines 90–101). Mathlib's
docstring for that file notes that `piRightHom` is not an isomorphism in
general. At the project's Mathlib pin, a text search finds no theorem on the
bijectivity of `piRightHom` for finitely presented modules. Searches of the
Library and of TaskHub found no existing owner of this target.

## Source and how the target relates to it

The source is `FLT/DedekindDomain/FiniteAdeleRing/TensorPi.lean` of
ImperialCollegeLondon/FLT at commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`, copyright 2025 Madison Crim, author
Madison Crim. It is retained in registered source
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) under
`ImperialCollegeLondon--FLT/source`. The file's SHA-256,
`baf10f3f6816d33871de201c671e12c75a5e6f8b5c761d3d23965ebcdc01c6e5`, matches the
snapshot's `SHA256SUMS.json`. All 275 lines of the file were read.

- [Lines 182–184](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorPi.lean#L182-L184)
  are the section variables: `(R M : Type*) [CommRing R] [AddCommGroup M]
  [Module R M] [h : Module.FinitePresentation R M] {ι : Type*}
  (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]`. Each
  `Type*` gives a separate universe. The target quantifies exactly these
  hypotheses, with the same binder kinds and four independent universes. It
  drops only the unused instance name `h`.
- [Lines 199–270](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorPi.lean#L199-L270)
  define `tensorPiEquivPiTensor' : M ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (M ⊗[R] N i)`
  as `IsTensorProduct.equiv (f := TensorProduct.piRightHomBil R R M N)`
  applied to a proof. Mathlib defines `IsTensorProduct f` as
  `Function.Bijective (TensorProduct.lift f)`, and `IsTensorProduct.equiv` is
  `LinearEquiv.ofBijective` of that lift. The proof (lines 202–270) sets
  `i₃ := TensorProduct.piRightHom R R M N` (line 207). It applies the five
  lemma to a finite presentation `Rᵐ → Rⁿ → M → 0` and the finite free case
  `tensorPiEquivPiTensor`, and ends with `Function.Bijective i₃` (lines
  267–270). So the source equivalence is the packaging of exactly one
  mathematical assertion: the bijectivity of `piRightHom R R M N`. That
  assertion is this target. A private check confirms that the target, applied
  to `R M N`, has type `IsTensorProduct (TensorProduct.piRightHomBil R R M N)`.
  This is the hypothesis that the source passes to `IsTensorProduct.equiv`.
- [Lines 272–273](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorPi.lean#L272-L273)
  give the pure-tensor formula `tensorPi_equiv_piTensor'_apply`,
  `m ⊗ₜ n ↦ (i ↦ m ⊗ₜ n i)`, proved by `rfl`.

The docstring at line 186 says that tensoring with a finitely presented module
commutes with arbitrary products. The heading and summary of the module
docstring (lines 13–16) speak of finite free modules, which fits the unprimed
`tensorPiEquivPiTensor`. Its list of definitions (lines 20–21) adds the primed
version for finitely presented modules. The target follows the actual
hypotheses of the primed declaration, lines 182–184, and not the docstrings.

Mathlib already defines the canonical map and its pure-tensor formula,
[`Mathlib/LinearAlgebra/TensorProduct/Pi.lean`, lines 43–63](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/LinearAlgebra/TensorProduct/Pi.lean#L43-L63).
There, `piRightHomBil` is the bilinear map at lines 46–52, `piRightHom` is its
lift at lines 54–57, and `piRightHom_tmul` is the formula at lines 59–62. The
target uses these declarations directly and copies none of them.

## Scope and later phases

This is a statement task. The module contains no proof of the target, no
equivalence and none of the auxiliary source declarations:
`Module.FinitePresentation.exists_fin_exact`, `directSumPiEquivPiSum`, the
finite free equivalence `tensorPiEquivPiTensor` and its helpers, the
five-lemma argument, `tensorPiEquivPiTensor'`, and the two `_apply` lemmas.
The analogue of `tensorPiEquivPiTensor'`, for example
`LinearEquiv.ofBijective (TensorProduct.piRightHom R R M N) h`, can be
packaged only after an exact proof of this target has been independently
accepted and published. That packaging belongs to a later phase of parent
task `2ff17b0a-7a93-4668-a2e6-b740e4205e6d`. In the source, that equivalence
is used in `lTensorPrincipalEquiv`
(`FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean`, lines
130–131), where the coordinates are submodules `N' i`, and its formula is
used at lines 167 and 215 of the same file.

The target is placed in the namespace `RestrictedProduct` because it serves
the parent's restricted-product tensor equivalence. It does not mention
restricted products. It does not import
`Langlands.LinearAlgebra.RestrictedProduct.Tensor`, and it is independent of
the maps defined there. Its only imports are
`Mathlib.Algebra.Module.FinitePresentation`, for `Module.FinitePresentation`,
and `Mathlib.LinearAlgebra.TensorProduct.Pi`, for `piRightHom`. The target
makes no topological or norm claim.

## Checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) built the module
with no errors or warnings (diagnostic `dbf38c8e-482f-484b-981d-e82b62c2f9a6`).
Its inspection of `RestrictedProduct.TensorPiComparison` reports kind
`definition`, level parameters `uR`, `uM`, `uι`, `uN`,
`statement_returns_prop: true`, and axioms `propext`, `Classical.choice` and
`Quot.sound`. A private probe module (diagnostic
`ffcf0f96-2991-4dd1-ac14-ac0be47d0b32`) printed the elaborated body with
`pp.explicit`. It also checked that `TensorPiComparison.{0, 1, 2, 3}`, applied
to `R M N`, has type `IsTensorProduct (TensorProduct.piRightHomBil R R M N)`,
and that the target applies at `ℤ`, `ℤ` and the constant family `fun _ : ℕ ↦ ℤ`.
The module has no `sorry`, `admit` or new axiom.

## Provenance and modification notice

The Lean file keeps the source's Apache-2.0 header, with its copyright line
and author. It adds a notice of Worker 376's modifications. The source
declaration packages a bijectivity proof as an equivalence. This module
instead states that bijectivity as a `Prop`-valued definition, built from
Mathlib's `piRightHom` and the source hypotheses at lines 182–184. The
universe names are explicit, the `module`/`public import`/`@[expose] public
section` keywords become plain imports, and all proofs and auxiliary
declarations are left out. None of the audit's compatibility patches (a)–(d)
applies, and no other adaptation was needed. No Anthropic derivative code is
used. The upstream root Apache-2.0 `LICENSE` is retained at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The source snapshot has no `NOTICE` file. The public audit
[finite-adele base change](../../../notes/reuse/finite-adele-base-change-audit.md),
sections 2–6 and Appendix B, describes the surrounding source closure.
