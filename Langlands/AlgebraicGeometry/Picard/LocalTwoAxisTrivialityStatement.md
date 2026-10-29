# Local triviality detected by two section axes and one fibre

Worker 606 designed this statement interface and its first Markdown draft
(shared draft revision 1 of task `39e84a50-12a4-4e68-a013-c5e551c531c5`).
Worker 950 rechecked it against the original source and prepared it for
publication.

`Langlands.AlgebraicGeometry.Picard.LocalTwoAxisTrivialityStatement.{u}` is a
`Prop`-valued definition. This module states the local criterion and supplies
no proof. A separate exact-target proof of this proposition is still required.

## Exact interface

The only external parameter is the universe `u`. Everything else is quantified
inside the proposition, in this order.

- An arbitrary scheme `S : Scheme.{u}`. There is no quasi-separatedness,
  quasi-compactness, noetherian, reducedness, normality or connectedness
  hypothesis on `S`; in particular `S` may be nonreduced.
- Two objects `X Y : Over S` of the slice category, that is, schemes
  `X.left` and `Y.left` with structure morphisms `f = X.hom` and `g = Y.hom`
  to `S`. Each of `f` and `g` is assumed `Smooth`, `IsProper` and
  `GeometricallyConnected`; these are Mathlib's actual properties of scheme
  morphisms. No group structure, projectivity, polarization or cohomological
  hypothesis is assumed.
- Sections `x₀ : Over.mk (𝟙 S) ⟶ X` and `y₀ : Over.mk (𝟙 S) ⟶ Y` in
  `Over S`. Their underlying scheme morphisms `σ = x₀.left : S ⟶ X.left` and
  `τ = y₀.left : S ⟶ Y.left` satisfy `σ ≫ f = 𝟙 S` and `τ ≫ g = 𝟙 S` by the
  commutativity condition of `Over`; they are exactly sections of `f` and `g`.
- A line bundle `L : LineBundle (X ⨯ Y).left`. Here `X ⨯ Y` is the
  categorical product in `Over S`, so `P = (X ⨯ Y).left` is the fibre product
  `X ×_S Y` with structure morphism `(X ⨯ Y).hom`. `LineBundle` is the
  Library's full subcategory of `P.Modules` of locally free rank-one sheaves
  of modules (`Langlands.AlgebraicGeometry.Picard.LineBundle`), and `L.obj` is
  the underlying sheaf of `O_P`-modules.
- A point `s : S`.

All isomorphisms below are isomorphisms in Mathlib's actual categories
`T.Modules` of sheaves of modules over the structure sheaf of a scheme `T`,
asserted with `Nonempty`. The pullback along a scheme morphism `φ` is Mathlib's
functor `Scheme.Modules.pullback φ`, and "trivial" means isomorphic to
`Langlands.Scheme.Modules.structureSheaf T`, which is
`SheafOfModules.unit T.ringCatSheaf`, the structure sheaf as a module over
itself. No substitute triviality predicate, Picard group, cohomology data or
chosen trivializing data is introduced.

### Face coordinates

For `T : Over S` write `!T = Over.mkIdTerminal.from T : T ⟶ Over.mk (𝟙 S)`;
its underlying scheme morphism is the structure map `T.hom`. The two axes are
the `S`-morphisms

```text
prod.lift (𝟙 X) (!X ≫ y₀) : X ⟶ X ⨯ Y,   x ↦ (x, τ(f x)),
prod.lift (!Y ≫ x₀) (𝟙 Y) : Y ⟶ X ⨯ Y,   y ↦ (σ(g y), y),
```

that is, the source's `1 × τ : X → X ×_S Y` and `σ × 1 : Y → X ×_S Y`. The
statement uses their underlying scheme morphisms (`.left`).

### Hypotheses and conclusion

The three hypotheses are

1. the pullback of `L.obj` along `(prod.lift (𝟙 X) (!X ≫ y₀)).left` is
   isomorphic to `structureSheaf X.left`;
2. the pullback of `L.obj` along `(prod.lift (!Y ≫ x₀) (𝟙 Y)).left` is
   isomorphic to `structureSheaf Y.left`;
3. the pullback of `L.obj` along `(X ⨯ Y).hom.fiberι s` is isomorphic to the
   structure sheaf of `(X ⨯ Y).hom.fiber s`. In Mathlib this fibre is the
   scheme-theoretic fibre `pullback (X ⨯ Y).hom (S.fromSpecResidueField s)`
   over `Spec (S.residueField s)`, that is `P ×_S Spec κ(s)`, and `fiberι s` is
   its first projection to `P`. It is not a set of points or the reduced
   preimage.

The conclusion is that there exists an open `U : S.Opens` with `s ∈ U` such
that the pullback of `L.obj` along `pullback.fst (X ⨯ Y).hom U.ι` is isomorphic
to the structure sheaf of `pullback (X ⨯ Y).hom U.ι`. This fibre product is the
base change `P_U = P ×_S U` along the open immersion `U.ι : U ⟶ S`, and its
first projection is the open immersion `P_U ⟶ P`. Thus `L` becomes trivial on
the whole scheme `P_U`, including any nilpotent structure of `S` over `U`, not
only on fibres or on a reduced subscheme.

## Original source

The Stacks Project, More on Morphisms, Section "Theorem of the cube"
(tag 0BEZ), Lemma `lemma-pic-of-product` (tag 0BF3; Lemma 37.33.7 on the
current web page), in the retained file `more-morphisms.tex`, lines 9621–9650.
Registered source `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, folder SHA-256
`b97dd26d238af5bb18d082504515f27f5316b6b87c2a7d68ca8630e7862ad48e`. Its
hypotheses refer to Lemma `lemma-diagonal-picard-flat-proper` (tag 0BDP,
lines 9198–9215), and its proof uses Lemma
`lemma-H1-O-multiple-picard-flat-proper` (tag 0BF2, lines 9518–9619).

The source lemma reads: let `f : X → S` and `g : Y → S` satisfy the hypotheses
of 0BDP, let `σ`, `τ` be sections of `f`, `g`, let `s ∈ S` and let `L` be an
invertible sheaf on `X ×_S Y`; if `(1 × τ)^*L` on `X`, `(σ × 1)^*L` on `Y` and
`L|_{(X ×_S Y)_s}` are trivial, then `L` is trivial over `(X ×_S Y)_U` for some
open neighbourhood `U` of `s`. The Lean statement has exactly these data,
hypotheses and conclusion, with invertible sheaves read as locally free
rank-one modules (on a scheme these are the same objects).

Errata: the source folder's README records two typographical comments on tag
0BDP, both fixed in 2025 and not affecting this statement. Worker 606 found no
comments on the 0BF2 and 0BF3 pages on 2026-10-28; Worker 950 rechecked both
pages the same day ("Comments (0)") and found the live 0BF3 statement identical
to the retained one. No project errata file exists for this source.

## Specialization of the source hypotheses

The hypotheses of 0BDP on a morphism `f : X → S` are: flat, proper and of
finite presentation, and `O_T → p_* O_{X_T}` is an isomorphism for every
`T → S`, where `p : X_T → T` is the base change. The Lean statement assumes
instead that `f` is smooth, proper and geometrically connected. This is a
specialization, so the source lemma covers the Lean statement:

- smooth implies flat and locally of finite presentation;
- proper implies quasi-compact and separated, hence quasi-separated, so `f` is
  of finite presentation;
- smooth, proper and geometrically connected morphisms are stable under base
  change, and the published theorem
  `Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`
  (module `Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof`),
  applied to each base change `p : X_T → T`, says that `p.app V` is an
  isomorphism for every open `V` of `T`. That is the structure-sheaf
  condition `O_T ≅ p_* O_{X_T}`.

These comparisons only explain why the hypotheses specialize those of the
source. They do not prove the local criterion, and the Lean statement assumes
none of them as extra hypotheses.

## Source proof route

These remarks describe the source proof and the obligations of a future proof;
they are not formalized here. The source proof applies Künneth on the fibre
(Varieties, Lemma `varieties-lemma-kunneth`, tag 0BED) to see that
`H^1(X_s ×_κ(s) Y_s, O) → H^1(X_s, O) ⊕ H^1(Y_s, O)` is injective, and then
applies 0BF2 to the two axes. The proof of 0BF2 uses the infinitesimal
information carried by the axes: perfect direct images whose formation commutes
with arbitrary base change (Derived Categories of Schemes, Lemma
`perfect-lemma-flat-proper-perfect-direct-image-general`, tag 0B91), local
representatives by finite free complexes, and the degree-one comparison above,
to lift the fibre trivialization to a section of `L` near the fibre. The
Library does not yet contain these cohomological tools over an arbitrary base.

## Why the two axis hypotheses are needed

Fibre triviality alone, even on all geometric fibres, does not give local
triviality over a nonreduced base. Informal example: let `k` be a field, `E` a
smooth proper geometrically connected curve over `k` of genus at least one with
a rational point, and `S = Spec k[ε]/(ε²)`. Take `X = E ×_k S` with the
constant section and `Y = S` with the identity section. On `X` the sequence
`1 → O_E → O_X^× → O_E^× → 1`, `b ↦ 1 + εb`, is split, so the line bundles on
`X` that are trivial on the closed fibre `E` form `H^1(E, O_E) ≠ 0`. A
nontrivial such `L` is trivial on the only fibre and all its geometric fibres,
but `S` has one point, so the only neighbourhood is `S` itself and `L` is not
trivial on `P_U = P`. Here the first axis hypothesis fails. The statement
therefore keeps both full axis hypotheses as actual module isomorphisms.
