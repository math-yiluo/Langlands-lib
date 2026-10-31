# Universal perfect models compatible with closed restrictions

The Prop-valued declaration
`Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsStatement.{u}`
states that the actual derived sections of a line bundle on a smooth proper
family over an affine base have one bounded finite projective model computing
every base change, and that restriction to a smooth closed subscheme is
represented by a chain map of such models, compatibly with every base change.
This file supplies a statement only; it proves nothing. Worker 950 prepared it
as a prerequisite of the proof task `e969f1c2-7aa6-4731-abaa-2f7455f32265`
(`Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement`).

## Complete statement

The file locally selects Mathlib's `HasDerivedCategory.standard`, as the
published `UniversalPerfectSectionsStatement` does. Write
`Q = DerivedCategory.Q`, `ι = DerivedCategory.Plus.ι`,
`RΓ(f', M) = ι.obj ((DerivedPlus.derivedComplex (DerivedSections.relativeGlobalSections f')).obj M)`
for `f' : X' ⟶ Spec T` and an `𝒪_{X'}`-module `M`, and
`K ⊗ T = (ModuleComplex.baseChange φ.hom).obj K` for `φ : R ⟶ T`.

For every `R : CommRingCat.{u}`, `X : Scheme.{u}` and `f : X ⟶ Spec R` with
`Smooth f` and `IsProper f`, and every
`L : Langlands.AlgebraicGeometry.Picard.LineBundle X`, there are:

1. a cochain complex `K : CochainComplex (ModuleCat.{u} R) ℤ` with
   `ModuleComplex.IsStrictlyPerfect K` (bounded, with finite projective terms);
2. a family `α` of isomorphisms in the derived category `D(T)`: for every
   `T : CommRingCat.{u}`, `φ : R ⟶ T`, scheme `X'`, and morphisms
   `p : X' ⟶ X`, `f' : X' ⟶ Spec T` with
   `IsPullback p f' f (Spec.map φ)` (that is, `X'` is a fibre product of `f`
   and `Spec.map φ` with projections `p` and `f'`), an isomorphism
   `α … : Q.obj (K ⊗ T) ≅ RΓ(f', (Scheme.Modules.pullback p).obj L.obj)`;

such that for every scheme `Y` and morphism `g : Y ⟶ X` with
`IsClosedImmersion g` and `Smooth (g ≫ f)` there are:

3. a cochain complex `K'` of `R`-modules with `IsStrictlyPerfect K'`;
4. a chain map `ψ : K ⟶ K'`;
5. a family `β` of isomorphisms in `D(T)`: for all data `T, φ, X', p, f'` and
   `hX : IsPullback p f' f (Spec.map φ)` as in item 2, every scheme `Y'` and
   morphisms `q : Y' ⟶ Y`, `g' : Y' ⟶ X'` with `hY : IsPullback q g' g p`, an
   isomorphism
   `β … : Q.obj (K' ⊗ T) ≅ RΓ(f', (pushforward g').obj ((pullback g').obj ((pullback p).obj L.obj)))`,
   where `pushforward` and `pullback` are `Scheme.Modules.pushforward` and
   `Scheme.Modules.pullback`;

and, for all such data `T, φ, X', p, f', hX, Y', q, g', hY`, the square

```lean
DerivedCategory.Q.map ((ModuleComplex.baseChange φ.hom).map ψ) ≫
    (β T φ X' p f' hX Y' q g' hY).hom =
  (α T φ X' p f' hX).hom ≫
    DerivedCategory.Plus.ι.map
      ((DerivedPlus.derivedComplex (DerivedSections.relativeGlobalSections f')).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app
          ((Scheme.Modules.pullback p).obj L.obj)))
```

commutes. The order of quantifiers matters: `K` and `α` are chosen once, before
any closed subscheme `Y`; then `K'`, `ψ` and `β` are chosen for each `Y`. So the
same isomorphisms `α` serve every closed restriction.

## Conventions

- `DerivedSections.relativeGlobalSections f'` is the published functor
  `Scheme.Modules.pushforward f' ⋙ moduleSpecΓFunctor` from all
  `𝒪_{X'}`-modules to `T`-modules. `DerivedPlus.derivedComplex F` places an
  object in degree zero and applies the right derived functor of `F` on bounded
  below derived categories; its cohomology in degree `n ≥ 0` is the published
  `relativeCohomology f' n`, and it has none in negative degrees.
- The closed-restriction map is the derived image of the actual adjunction unit
  `M ⟶ g'_* g'^* M` of `Scheme.Modules.pullbackPushforwardAdjunction g'` at
  `M = p^* L`. It is a morphism of `𝒪_{X'}`-modules, so its derived image is a
  morphism `RΓ(X', M) ⟶ RΓ(X', g'_* g'^* M)` in `D(T)`. The target is written
  with the direct image `g'_*` on `X'` rather than as cohomology on `Y'`. This is
  the form used by the hypotheses of `FibreFrameLiftingStatement`.
- `ModuleComplex.baseChange φ.hom` is ordinary termwise extension of scalars.
  Since `K` and `K'` have finite projective terms, it computes the derived
  tensor product `K ⊗^L_R T`.
- The base changes are quantified over every pullback square, not only the
  chosen fibre product `pullback f (Spec.map φ)`. A user may therefore apply
  the statement directly to a scheme-theoretic fibre `X.hom.fiber s` or to an
  open part `pullback X.hom U.ι`, without transporting along an isomorphism of
  schemes.
- Universes: rings, schemes and modules lie in an arbitrary universe `u`; there
  are no noetherian, reducedness, connectedness or base-point hypotheses.
  Properness of `g ≫ f` is not assumed because it follows from `IsProper f` and
  `IsClosedImmersion g`.

## Source and specialization

Registered source `stacks-perfect-complexes-a04446e5` (Stacks Project, git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`), file `perfect.tex`, chapter
*Derived Categories of Schemes*:

- Lemma `lemma-flat-proper-perfect-direct-image-general` (tag 0B91), lines
  7525–7544: for `f : X → S` proper of finite presentation and an
  `𝒪_X`-module `𝒢` of finite presentation, flat over `S`, `Rf_*𝒢` is perfect
  and its formation commutes with arbitrary base change.
- Lemma `lemma-base-change-tensor-perfect` (tag 0A1H), lines 7395–7441, of
  which 0B91 is a special case, and Remark `remark-explain-perfect-direct-image`
  (tag 0A1I), lines 7443–7455: over an affine base `Spec R` there is a finite
  complex `M•` of finite projective `R`-modules with
  `RΓ(X_{R'}, 𝒢_{R'}) = M• ⊗_R R'` functorially in the `R`-algebra `R'`.

Registered source `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, file
`more-morphisms.tex` at the same commit: the proofs of Lemma
`lemma-H1-O-picard-flat-proper` (tag 0BF1), lines 9453–9516, and Lemma
`lemma-H1-O-multiple-picard-flat-proper` (tag 0BF2), lines 9543–9619, apply 0B91
to `E = Rf_*ℒ` and `Eᵢ = Rfᵢ_*ℒᵢ` and then use "a map `E → Eᵢ` in `D(𝒪_S)`
whose formation commutes with change of base", represented by a map of the
finite free representatives. This statement isolates the smooth closed-immersion
specialization of that input, before the later choice of local minimal models.

Specialization. Smoothness gives flatness and local finite presentation, and
properness gives quasi-compactness and quasi-separatedness, so `f` and `g ≫ f`
are proper of finite presentation. A line bundle `L` is of finite presentation
and flat over `R`, and so is `g^*L` on `Y`. Higher direct images along a closed immersion vanish (the published
`closedImmersionHigherDirectImageVanishing`), so `RΓ(X', g'_* 𝒢) = RΓ(Y', 𝒢)`
and the target
`RΓ(X', g'_* g'^* p^* L)` is the base change of `RΓ(Y, g^*L)` along `φ`, because
`g'^* p^* L ≅ q^* g^* L`. The functoriality of the source comparison in the
coefficient sheaf gives the derived restriction map and its compatibility with
base change. Because `K` is bounded with projective terms, a morphism
`Q.obj K ⟶ Q.obj K'` in `D(R)` is represented by a chain map `ψ`, unique up to
homotopy. The Lean statement keeps only what the 0BF1/0BF2 argument uses:
one model `K` with base-change isomorphisms `α`, and for each smooth closed
subscheme a model `K'`, a chain map `ψ` and base-change isomorphisms `β` making
the base-changed square commute. It is a specialized statement design derived
from the source, not a transcription of its full generality.

## Relation to existing statements

The published `UniversalPerfectSectionsStatement` (Worker 1013) asserts only
objectwise `Nonempty` isomorphisms for the chosen fibre product
`pullback f (Spec.map φ)`. Objectwise isomorphisms do not identify restriction
maps, so that statement does not provide the chain maps `ψ` and the commuting
squares asserted here. Specialized to the canonical square
`IsPullback.of_hasPullback f (Spec.map φ)`, the family `α` has the shape of the
base-change isomorphisms of that statement. The current Library also contains `universalPerfectSections`, which proves that
objectwise statement. This file proves no relation between the two statements;
objectwise existence alone supplies no restriction compatibility.

## Scope

This is a statement only. It does not assert naturality of `α` in `T`, nor any
statement about minimal models, degree-one cohomology or line bundle
triviality; those belong to other statements, in particular the pure algebra
statement `Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement`
proposed alongside it.
