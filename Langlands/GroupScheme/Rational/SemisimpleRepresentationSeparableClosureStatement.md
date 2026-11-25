# Semisimple representations of a reductive group over `kᵃ` are defined over `kˢ`

`Langlands.GroupScheme.ReductiveSemisimpleRepresentationSeparableClosureStatement.{u}`
is a Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy `IsConnectedReductive G`.
Let `Ks : Type u` be a field with `[Algebra k Ks]` and `[IsSepClosure k Ks]`,
and let `Ka : Type u` be a field with `[Algebra Ks Ka]` and
`[IsAlgClosure Ks Ka]`. Write `bs = algebraBaseMap k Ks`,
`ba = algebraBaseMap Ks Ka`, `G_s = (GroupScheme.baseChange bs).obj G` and
`G_a = (GroupScheme.baseChange ba).obj G_s`. Then for every `m : ℕ` and every
`ρ' : MatrixRepresentation G_a (Fin m)` with `IsSemisimpleRep ρ'` there is
`ρ : MatrixRepresentation G_s (Fin m)` with `IsSemisimpleRep ρ`, together with
a matrix `C : Matrix (Fin m) (Fin m) Ka` such that
`(ρ.baseChange ba).Intertwines ρ' C` and `Function.Bijective C.mulVecLin`.

Here `IsSemisimpleRep σ` is a local `let` in the statement. Its field `F`,
group `H` and dimension `m` are implicit, so that it applies over `Ks` and over
`Ka`. It says

```text
sSup {W : Submodule F (Fin m → F) | σ.IsStableSubspace W ∧ W ≠ ⊥ ∧
  ∀ U : Submodule F (Fin m → F), σ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W} = ⊤
```

that is, `Fᵐ` is the sum of its simple subrepresentations.

In words: every semisimple representation of a connected reductive group over
an algebraic closure `kᵃ` of `k` is the extension of scalars of a semisimple
representation over the separable closure `kˢ` of `k` in `kᵃ`.

Every ingredient is an existing declaration, used without change:

- `IsConnectedReductive G` (from [`Reductive.Basic`](../Reductive/Basic.md))
  says that `G` is smooth, affine and connected over `k`, and that the base
  change of `G` to `AlgebraicClosure k` has trivial unipotent radical.
- `IsSepClosure k Ks` (Mathlib, `Mathlib.FieldTheory.IsSepClosed`) says that
  `Ks` is separably closed and separable over `k`. `IsAlgClosure Ks Ka`
  (Mathlib, `Mathlib.FieldTheory.IsAlgClosed.Basic`) says that `Ka` is
  algebraically closed and algebraic over `Ks`.
- `algebraBaseMap k K` (from [`Torus.LatticeGalois`](../Torus/LatticeGalois.md))
  is `Spec.map (CommRingCat.ofHom (algebraMap k K))`.
  `GroupScheme.baseChange` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is base
  change of group schemes along a morphism of base schemes.
- `MatrixRepresentation H (Fin m)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `H ⟶ GL_m`. `MatrixRepresentation.baseChange` (from
  [`Rational.ValuedRepresentationBaseChange`](ValuedRepresentationBaseChange.md))
  is the base change of this homomorphism followed by the canonical
  isomorphism of the base change of `GL_m` with `GL_m`.
- `σ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says that `W` is a subrepresentation; the condition is checked on the
  points of the group with values in every commutative algebra over the
  field.
- `ρ.Intertwines σ C` (from
  [`Lie.RepresentationSubquotient`](../Lie/RepresentationSubquotient.md))
  says that `C · ρ(x) = σ(x) · C` for every commutative algebra `S` over the
  field and every point `x` of the group with values in `S`. So `C` is a
  homomorphism of representations, and with `Function.Bijective C.mulVecLin`
  an isomorphism.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is 22.7, printed p. 464: "Let G be a reductive group over k (not
necessarily split). Every semisimple representation of G over kᵃ is defined
over kˢ. Indeed, G splits over kˢ, and so we can apply 22.5."

The result it applies, 22.5 on the same page: "Let G be a split reductive
group over k, and let k′ be an extension of k. For every semisimple
representation (V′, r′) of G_{k′} over k′, there exists a semisimple
representation (V, r) of G over k and an isomorphism (V, r) ⊗ k′ → (V′, r′).
This follows from 22.4."

Conventions used:

- Notation, printed p. 3: "The symbol kᵃ denotes an algebraic closure of k
  and kˢ (resp. kⁱ) denotes the separable (resp. perfect) closure of k in kᵃ."
  On the same page: "An extension of k is a field containing k".
- Section 6h, printed p. 135 ("Throughout this section, all algebraic groups
  are affine"): "A connected group variety G over a field k is said to be
  reductive if G_{kᵃ} is reductive, i.e., if its geometric unipotent radical
  R_u(G_{kᵃ}) is trivial." A group variety is a smooth algebraic group
  (printed p. 13).
- Opening of Chapter 22, printed p. 463: "Throughout, representations are
  finite-dimensional unless it is specified otherwise."
- Definition 4.15, printed p. 90: "A representation of an algebraic group is
  simple if it is ≠ 0 and its only subrepresentations are 0 and itself. It
  is semisimple if it is a sum of simple subrepresentations."

The provenance is derived for these reasons:

- Reductive groups. Milne's reductive group over `k` is a smooth connected
  affine algebraic group whose geometric unipotent radical is trivial. This
  is `IsConnectedReductive G`. Finite type is not a separate hypothesis: a
  smooth morphism is locally of finite presentation, and with an affine
  structure morphism over a field `G` is of finite type.
- The fields `kˢ ⊆ kᵃ`. The Lean statement takes any separable closure `Ks`
  of `k` and any algebraic closure `Ka` of `Ks`. Such a pair is exactly
  Milne's pair. `Ka` is algebraically closed and algebraic over `k`, because
  `Ks` is algebraic over `k`; so `Ka` is an algebraic closure of `k`. `Ks` is
  the separable closure of `k` in `Ka`: it is separable over `k`, and an
  element of `Ka` separable over `k` is separable over `Ks`, hence lies in
  the separably closed field `Ks`. Conversely, for an algebraic closure `kᵃ`
  of `k`, the separable closure `kˢ` of `k` in `kᵃ` is a separable closure
  of `k`, and `kᵃ` is an algebraic closure of `kˢ`. The statement has no
  `Algebra k Ka` instance: the `k`-structure of `Ka` is the one through `Ks`.
- The group `G_{kᵃ}`. The Lean statement uses the iterated base change
  `G_a = (G_s)_{Ka}`. It is canonically isomorphic to the base change of `G`
  along `Spec Ka → Spec k`, since a composite of pullbacks is a pullback, and
  isomorphic group schemes have the same representations, with the same
  simple and semisimple ones.
- "Defined over kˢ". A representation (V′, r′) of G_{kᵃ} is defined over kˢ
  when it is isomorphic to (V, r) ⊗ kᵃ for some representation (V, r) of
  G_{kˢ}. Milne obtains (V, r) from 22.5, applied to the split group G_{kˢ}
  and the extension kᵃ of kˢ, and 22.5 gives a semisimple (V, r). The Lean
  statement records this: `ρ` is semisimple. This is slightly more than the
  literal wording of 22.7. It is also forced: by Proposition 4.19(a) (printed
  pp. 90–91), a finite-dimensional representation whose extension of scalars is semisimple is
  semisimple.
- Coordinates. Finite-dimensional representations are matrix
  representations on `Kaᵐ` and on `Ksᵐ`; every finite-dimensional
  representation is isomorphic to one of these, and semisimplicity and
  isomorphism classes are preserved by isomorphisms. `(V, r) ⊗ kᵃ` is
  `ρ.baseChange ba`. The representation `ρ` has the same dimension `m` as
  `ρ'`, which an isomorphism `(V, r) ⊗ kᵃ ≅ (V′, r′)` forces. An isomorphism
  is an intertwining matrix `C` whose linear map is bijective. Semisimplicity
  is Definition 4.15: the sum (`sSup`) of the simple stable subspaces is the
  whole space.
- `k`, `Ks`, `Ka`, `G` and the test algebras in `IsStableSubspace` and
  `Intertwines` lie in one universe `u`. This is a formalization convention.

Relation to the Library. The formula for semisimplicity is the one of
`SemisimpleRepresentationCharZeroStatement` (in
[`Reductive.SemisimpleRepresentationCharZeroStatement`](../Reductive/SemisimpleRepresentationCharZeroStatement.md)).
The Library has no statement of 22.7.

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has 22.7 on printed p. 465:
"Let G be a reductive group over k (not necessarily split). Every semisimple
representation of G over kᵃ is defined over kˢ. Indeed, G splits over kˢ, and
so this follows from 22.5." The content is the same.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 22, corrections on pp. 468, 469, 473 and 480, none for p. 464 or
p. 463. Its entries for Chapter 1, Chapter 4 (p. 95) and Chapter 6 (p. 136)
do not concern the notation on p. 3, Definition 4.15, Proposition 4.19 or
the definition of reductive groups on p. 135. Its entries for Chapter 12
(pp. 244, 249) and Chapter 17 (pp. 360, 364, 386) do not concern Theorems
12.18 and 17.82 cited below. The errata snapshot of 2026-11-04 for the 2022
reprint (source ID `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has, for
Chapter 22, an entry on p. 465 that concerns 22.8 ("X ⊂ X₀ + P(Φ)" holds only
modulo `X₀`) and one on p. 478 (proof of 22.42); neither concerns 22.7.

## For the proof (not part of this module)

The Library proves the proposition as
`reductiveSemisimpleRepresentationSeparableClosure` in
[`Rational.SemisimpleRepresentationSeparableClosureProof`](SemisimpleRepresentationSeparableClosureProof.md).

A possible route, following Milne:

- `G_s` is connected reductive: the Library's theorem
  `connectedReductiveFieldExtensionStatement` (in
  [`Reductive.FieldExtensionProof`](../Reductive/FieldExtensionProof.md))
  gives this for every field extension.
- `G_s` has a split maximal torus. For the existence of a maximal torus, the
  Library's `exists_maximalTorus_extension_of_finiteType` (in
  [`Rational.MaximalTorusFiniteType`](MaximalTorusFiniteType.md)) extends
  every closed torus of an affine group locally of finite type over a field to
  a maximal torus. Every torus over the separably closed field `Ks` is split
  by `toriAreSplit_of_isSepClosed` (in
  [`AlgebraicFundamentalGroupWeyl`](../AlgebraicFundamentalGroupWeyl.md)). In
  Milne this is "G splits over kˢ": by Theorem 17.82 (printed p. 379) a
  maximal torus stays maximal after extension of the base field, and by
  Theorem 12.18 (printed p. 237) a group of multiplicative type becomes
  diagonalizable over kˢ.
- `G_s` then has a split pinning by `splitPinningExistence` (in
  [`Reductive.SplitPinningExistenceProof`](../Reductive/SplitPinningExistenceProof.md)).
- Apply 22.5 to `G_s` with the split pinning and the extension `Ka` of `Ks`.
  The proof of 22.5 needs Theorems 22.2 and 22.19 and 22.4 for `G_s`.
