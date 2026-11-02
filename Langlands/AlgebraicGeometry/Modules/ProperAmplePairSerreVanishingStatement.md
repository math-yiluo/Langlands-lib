# Serre vanishing for two ample line bundles on a proper scheme over a field

`Langlands.AlgebraicGeometry.Modules.ProperAmplePairSerreVanishingStatement`
is a universe-polymorphic `Prop`-valued definition. It states a two-bundle
form of Serre vanishing for an actual proper scheme over a field. The
one-bundle theorem is the Stacks Project, Lemma 30.16.1 (4), tag
[0B5T](https://stacks.math.columbia.edu/tag/0B5T). The two-bundle form with
one threshold for both exponents is not printed in the cited sources. It is
derived content, and its derivation is given below. The module states the
proposition only. It supplies no proof and adds no axiom.

## Statement

For every universe `u`, every field `K : Type u`, every scheme `X` with a
proper morphism `f : X ⟶ Spec K`, every quasi-coherent `M : X.Modules` with
finitely generated sections over every affine open, and all ample line bundles
`L₁ L₂ : LineBundle X`, there is `n₀ : ℕ` such that

```text
Hⁱ(X, (M ⊗ L₁^{⊗a}) ⊗ L₂^{⊗b}) = 0   for all a ≥ n₀, b ≥ n₀ and i > 0.
```

The threshold `n₀` depends on `K`, `X`, `f`, `M`, `L₁` and `L₂`. It does not
depend on `a`, `b` or `i`. Degree zero is not constrained.

## Complete checked type

The source declaration is

```lean
def ProperAmplePairSerreVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f →
      ∀ (M : X.Modules), M.IsQuasicoherent →
        (∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(M, U.1)) →
          ∀ (L₁ L₂ : LineBundle X), L₁.IsAmple → L₂.IsAmple →
            ∃ n₀ : ℕ, ∀ a b : ℕ, n₀ ≤ a → n₀ ≤ b → ∀ i : ℕ, 0 < i →
              IsZero ((DerivedSections.relativeCohomology f i).obj
                (Langlands.Scheme.Modules.tensorObj
                  (Langlands.Scheme.Modules.tensorObj M
                    (Langlands.Scheme.Modules.tensorPow L₁.obj a))
                  (Langlands.Scheme.Modules.tensorPow L₂.obj b)))
```

inside `namespace Langlands.AlgebraicGeometry.Modules`, with
`open CategoryTheory CategoryTheory.Limits AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard`. The module imports only
`Langlands.AlgebraicGeometry.Modules.DerivedSections`,
`Langlands.AlgebraicGeometry.Modules.Tensor`,
`Langlands.AlgebraicGeometry.Picard.Ample` and
`Mathlib.AlgebraicGeometry.Morphisms.Proper`. The body is the one in the task
specification, unchanged. With `pp.fieldNotation false`, `pp.proofs true` and
`pp.funBinderTypes true`, `#print` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` reports:

```text
def Langlands.AlgebraicGeometry.Modules.ProperAmplePairSerreVanishingStatement.{u} : Prop :=
∀ (K : Type u) [inst : Field K] (X : AlgebraicGeometry.Scheme) (f : X ⟶ AlgebraicGeometry.Spec ↧K),
  AlgebraicGeometry.IsProper f →
    ∀ (M : AlgebraicGeometry.Scheme.Modules X),
      SheafOfModules.IsQuasicoherent M →
        (∀ (U : ↑(AlgebraicGeometry.Scheme.affineOpens X)),
            Module.Finite
              ↑(CategoryTheory.Functor.obj
                  (AlgebraicGeometry.PresheafedSpace.presheaf
                    (AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                      (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                        (AlgebraicGeometry.Scheme.toLocallyRingedSpace X))))
                  (Opposite.op ↑U))
              ↑(CategoryTheory.Functor.obj (AlgebraicGeometry.Scheme.Modules.presheaf M) (Opposite.op ↑U))) →
          ∀ (L₁ L₂ : Langlands.AlgebraicGeometry.Picard.LineBundle X),
            Langlands.AlgebraicGeometry.Picard.LineBundle.IsAmple L₁ →
              Langlands.AlgebraicGeometry.Picard.LineBundle.IsAmple L₂ →
                ∃ (n₀ : ℕ),
                  ∀ (a b : ℕ),
                    n₀ ≤ a →
                      n₀ ≤ b →
                        ∀ (i : ℕ),
                          0 < i →
                            CategoryTheory.Limits.IsZero
                              (CategoryTheory.Functor.obj
                                (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology f i)
                                (Langlands.Scheme.Modules.tensorObj
                                  (Langlands.Scheme.Modules.tensorObj M
                                    (Langlands.Scheme.Modules.tensorPow
                                      (CategoryTheory.ObjectProperty.FullSubcategory.obj L₁) a))
                                  (Langlands.Scheme.Modules.tensorPow
                                    (CategoryTheory.ObjectProperty.FullSubcategory.obj L₂) b)))
```

and `#check` reports type `Prop`. Here `↧K` is `CommRingCat.of K`. The
`lean_check` inspection reports `statement_returns_prop: true` and only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Library objects used

The statement uses only published definitions and Mathlib. It introduces no
new data, structure, certificate or axiom.

- `Spec (CommRingCat.of K)` is Mathlib's spectrum of the field `K`.
  `IsProper f` is Mathlib's proper morphism: separated, universally closed
  and locally of finite type. Universally closed morphisms are
  quasi-compact, so `X` is of finite type over `K`, hence noetherian,
  separated and of finite Krull dimension.
- `X.Modules` is Mathlib's category of sheaves of `𝒪_X`-modules.
  `M.IsQuasicoherent` is Mathlib's `SheafOfModules.IsQuasicoherent`. The
  third hypothesis says that `Γ(M, U)` is a finite `Γ(X, U)`-module for every
  affine open `U`. It is the coefficient predicate already used by the
  published `ProperCoherentCohomologyFiniteStatement`.
- `LineBundle X` is the full subcategory of `X.Modules` cut out by
  `IsLocallyFreeRankOne`: every point has an open neighbourhood `U` with
  `M.restrict U.ι ≅ 𝒪_U`. These are the invertible sheaves. `L.obj` is the
  underlying sheaf of modules.
- `L.IsAmple` is the published predicate of `Picard.Ample`:

  ```text
  CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
    x ∈ L.sectionOpen s ∧ IsAffineOpen (L.sectionOpen s)
  ```

  Here `L.powSections n` is the global sections of `tensorPow L.obj n`, and
  `L.sectionOpen s` is the largest open on which `s` trivializes that power.
  `Picard/Ample.md` identifies this with Stacks Definition 28.27.1, tag
  [01PS](https://stacks.math.columbia.edu/tag/01PS).
- `Langlands.Scheme.Modules.tensorObj M N` is the sheafification of the
  sectionwise tensor product of the underlying presheaves of modules
  (`Modules/Tensor`). It is the usual `M ⊗_{𝒪_X} N`.
- `Langlands.Scheme.Modules.tensorPow N n` is the right-associated tensor
  power: `tensorPow N 0 = structureSheaf X` and
  `tensorPow N (n + 1) = tensorObj N (tensorPow N n)`.
- The coefficient is `tensorObj (tensorObj M (tensorPow L₁.obj a))
  (tensorPow L₂.obj b)`, that is `(M ⊗ L₁^{⊗a}) ⊗ L₂^{⊗b}` with this exact
  bracketing. The Library's isomorphisms such as `tensorAssociator`,
  `tensorRightUnitor` and `tensorPowAddIso` are canonical isomorphisms, not
  equalities. A proof that rebrackets must transport the vanishing along
  them.
- `DerivedSections.relativeCohomology f i` is by definition
  `(relativeGlobalSections f).rightDerived i`, where
  `relativeGlobalSections f = Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor`.
  It is a functor from `X.Modules` to `ModuleCat K`, computed with injective
  resolutions in the abelian category `X.Modules`. Its value is the
  `K`-module `Hⁱ(X, -)`, with `K` acting through `f`.
- `IsZero` is categorical zero in `ModuleCat K`. A module is a zero object
  exactly when its only element is zero.

No cohomology module, vanishing fact, projective embedding, section or
comparison isomorphism is supplied as a hypothesis.

## Comparison with the cited sources

The sources are in registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`: Stacks Project LaTeX at
commit `a04446e57ec1fbc252a871afcec7752fb2807b14`. The file `coherent.tex`
has SHA-256
`702ca51850d0f9a615888dc0ced8100e104c98961e05a48b32c3ddf6eda61604`, which
was rechecked on 2026-11-01. Each tag below was checked against `tags.txt`
in the same folder.

- *One-bundle theorem.* Lemma 30.16.1, tag 0B5T (`coherent.tex` line 4329):
  "Let `R` be a Noetherian ring. Let `X → Spec(R)` be a proper morphism. Let
  `L` be an ample invertible sheaf on `X`. Let `F` be a coherent
  `O_X`-module." Part (3) says that `H^p(X, F)` is a finite `R`-module. Part
  (4) says: "If `p > 0`, then `H^p(X, F ⊗_{O_X} L^{⊗d}) = 0` for all `d`
  large enough." Here `R = K` is noetherian.
- *Coherence.* Tag [01XZ](https://stacks.math.columbia.edu/tag/01XZ)
  (`coherent.tex` line 2225). On a locally noetherian scheme, `F` is coherent if and only if
  for every affine open `Spec(A) = U ⊂ X` we have `F|_U = M~` with `M` a
  finite `A`-module. `X` is noetherian here. A quasi-coherent module on an
  affine `U` is the sheaf associated to its sections over `U`. So the
  hypotheses on `M` say exactly that `M` is coherent. This comparison is
  mathematics, not a Library theorem, and the statement does not use it.
- *Ampleness.* `LineBundle.IsAmple` is Stacks 01PS (registered as
  `stacks-invertible-picard-ampleness-2026-10-21`; see `Picard/Ample.md`).
- *Cohomology.* Stacks tag 01DZ (`cohomology.tex` lines 62–72) defines
  `H^i(X, F)` of an `O_X`-module by an injective resolution in `Mod(O_X)`,
  as an `O_X(X)`-module. This is the Library's `relativeCohomology`. The
  `R`-module structure in 0B5T comes through `R → O_X(X)`, as the
  `K`-module structure comes through `f` here. Tag 01F1 (`cohomology.tex`
  line 2175) shows that it agrees with the cohomology of the underlying
  abelian sheaf. So no comparison theorem is needed between the source
  cohomology and the Library's.
- *Uniformity in the degree.* In 0B5T (4) the bound on `d` may depend on
  `p`. Here one `n₀` serves every `i > 0`. This is harmless, because
  `Hⁱ(X, G) = 0` for every quasi-coherent `G` and every `i > dim X`. The
  Library proves this as `noetherianSeparatedQuasicoherentVanishing`. So
  only the finitely many degrees `1 ≤ i ≤ dim X` need a bound.
- *Two bundles.* The registered sources state Serre vanishing for one ample
  bundle. Searches of `coherent.tex` Sections 30.16–30.17 and
  `varieties.tex` found no two-bundle form. The multi-bundle numerical
  polynomial lemmas in `varieties.tex` (from line 10206) concern Euler
  characteristics only.
  The proof of Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
  Proposition 6.13 (i) (printed pp.123–124 / PDF pp.136–137) uses
  algebraic equivalence and translations instead. So the two-bundle form is
  derived content.

The two forms are related as follows. Taking `L₁ = L₂ = L` gives the
one-bundle conclusion for coherent `M` and all `d ≥ 2n₀`, after the canonical
isomorphism `(M ⊗ L^{⊗a}) ⊗ L^{⊗b} ≅ M ⊗ L^{⊗(a+b)}`. The converse is not a
specialization. One-bundle vanishing for the ample `L₁ ⊗ L₂` covers only the
diagonal `a = b`. One-bundle vanishing for `M ⊗ L₂^{⊗c}` and `L₁` gives a
threshold that depends on `c`. The derivation below supplies the uniform
threshold.

## Derivation of the two-bundle form

This is the mathematical justification of the statement. It is not part of
the Lean module. Write `F(a, b) = (F ⊗ L₁^{⊗a}) ⊗ L₂^{⊗b}` for a coherent
`F`. Call `F` *good* if some `n₀` gives `Hⁱ(F(a, b)) = 0` for all
`a, b ≥ n₀` and `i > 0`. Every coherent `F` is good, by strong induction on
the dimension of the closed set `Supp F`. This is finite because `X` is of
finite type over `K`.

1. If `Supp F` is empty, then `F = 0`, so `F(a, b) = 0`.
2. Otherwise, the set `Ass(F)` of associated points is finite, because `X`
   is noetherian (Stacks tag 05AF, listed in the registered `tags.txt` as
   `divisors-lemma-finite-ass`; the Divisors chapter text is not in the
   registered folder). By Stacks Lemma 28.30.6,
   tag [09NV](https://stacks.math.columbia.edu/tag/09NV) (registered as
   `stacks-ample-section-opens-comments-2026-10-28`, file `09NV.html`), with
   `E = Ass(F)` and `W = X`, there are `d₁ ≥ 1` and
   `s₁ ∈ Γ(X, L₁^{⊗d₁})` with `X_{s₁}` affine and `Ass(F) ⊂ X_{s₁}`. In the
   same way there are `d₂ ≥ 1` and `s₂ ∈ Γ(X, L₂^{⊗d₂})`.
3. Multiplication by `s_j` is a map `F → F ⊗ L_j^{⊗d_j}`. It is an
   isomorphism over `X_{s_j}`. Its kernel is a subsheaf of `F`, so its
   associated points lie in `Ass(F) ⊂ X_{s_j}`, where the kernel vanishes.
   So the kernel has no associated points and is zero. The cokernel `Q_j`
   is coherent and supported in `Supp F \ X_{s_j}`. This closed set contains
   no generic point of an irreducible component of `Supp F`, since those
   points are associated points of `F`. So
   `dim Supp Q_j < dim Supp F`. By induction there is `m` with
   `Hⁱ(Q_j(a, b)) = 0` for `j = 1, 2`, all `a, b ≥ m` and all `i > 0`.
4. Tensoring with the invertible `L₁^{⊗a} ⊗ L₂^{⊗b}` is exact. After
   canonical rebracketing this gives short exact sequences
   `0 → F(a, b) → F(a + d₁, b) → Q₁(a, b) → 0` and
   `0 → F(a, b) → F(a, b + d₂) → Q₂(a, b) → 0`. By the long exact
   sequence, the maps `σ₁ : Hⁱ(F(a, b)) → Hⁱ(F(a + d₁, b))` and
   `σ₂ : Hⁱ(F(a, b)) → Hⁱ(F(a, b + d₂))` are surjective for all `i ≥ 1` and
   `a, b ≥ m`.
5. Fix `i ≥ 1` and `a, b ≥ m`. The `K`-vector space `Hⁱ(F(a, b))` is finite
   dimensional, by 0B5T (3) (in the Library, `properCoherentCohomologyFinite`).
   Lemma 30.17.4, tag [01XR](https://stacks.math.columbia.edu/tag/01XR)
   (`coherent.tex` line 4709), says: if `X` is quasi-compact and
   quasi-separated and `X_s` is affine, then every class `ξ` in
   `H^p(X, G)` with `p > 0` and `G` quasi-coherent satisfies `s^n ξ = 0` in
   `H^p(X, G ⊗ L^{⊗n})` for some `n ≥ 0`. Apply it to the invertible sheaf
   `L₁^{⊗d₁}`, its section `s₁`, and `G = F(a, b)`. Taking `n` large enough
   for a basis gives one `t` such that multiplication by `s₁^t` is zero on
   `Hⁱ(F(a, b))`. That map is the `t`-fold composite of `σ₁`, so it is also
   surjective. Hence `Hⁱ(F(a + t d₁, b)) = 0`. Since `σ₁` and `σ₂` stay
   surjective for `a, b ≥ m`, it follows that
   `Hⁱ(F(a + t d₁ + v d₁, b + u d₂)) = 0` for all `u, v ≥ 0`.
6. Let `D = dim X`. Degrees `i > D` vanish for every quasi-coherent sheaf,
   by `noetherianSeparatedQuasicoherentVanishing`. Apply step 5 to the
   finitely many triples with `1 ≤ i ≤ D`, `m ≤ a < m + d₁` and
   `m ≤ b < m + d₂`. Let `T` be the largest exponent `t` obtained. Every
   `a' ≥ m + T d₁` and `b' ≥ m` can be written `a' = a + k d₁` with `k ≥ T`
   and `b' = b + u d₂` with `(a, b)` in that box. So `n₀ = m + T d₁`
   works, and `F` is good.

Applying this to `F = M` gives the statement.

An alternative route works only when `X` is smooth over `K`. On `X ×_K X` the
bundle `L₁ ⊠ L₂` is ample, and the published
`CoherentFieldExternalTensorKunnethStatement` (proved as
`coherentFieldExternalTensorKunneth`) computes `Hⁱ(L₁^{⊗a} ⊠ L₂^{⊗b})`. Then
`M` is reached through the diagonal. The published Künneth statement assumes
`Smooth` and `IsProper` and covers line bundles only. The general Künneth
formula over a field, Stacks Lemma 33.29.1, tag
[0BED](https://stacks.math.columbia.edu/tag/0BED) (`varieties.tex`
line 5442), needs only quasi-compactness and affine diagonal, but it is not
in the Library in that generality. So the dévissage above is the route that
covers every proper `X`.

## Proof obligations for the later exact proof

After independent acceptance and publication, a separate exact-target proof
must have this entire named proposition as its type, with no extra outer
hypotheses. Following the derivation, it needs the following. None of it is
proved here, and the list of Library material is a pointer, not a claim of
sufficiency.

- One-bundle Serre vanishing is not in the Library. The derivation does not
  use it.
- Finiteness of associated points of a coherent module, injectivity of
  multiplication by a section that is nonzero at the associated points, and
  the drop in dimension of the cokernel's support. The Library's
  `coherentIntegralIdealFiltration` (filtration by integral closed ideal
  sheaves) may serve as an alternative dévissage.
- Sections with affine nonvanishing locus. The proved
  `ampleFiniteSetSection` gives `E ⊂ X_s ⊂ W`, but it omits the affineness
  of `X_s` in 09NV. The proof of 09NV first takes an affine open `U ⊂ W`
  containing `E` (Lemma 28.30.5); then `X_s ⊂ U` is the nonvanishing locus
  of a section on an affine scheme, hence affine.
- The section-killing lemma 01XR for the Library's `relativeCohomology`,
  through 09MR (`coherent.tex` line 4648,
  `H^p(X_s, F) = colim_n H^p(X, F ⊗ L^{⊗n})`) and the vanishing of
  quasi-coherent cohomology on the affine `X_s` (tag 01XB). Pointers:
  `lineBundleSectionClearing` (the degree-zero analogue),
  `affinePushforwardCohomologyIso`, `lineBundleProjectionFormula`.
- Finite dimensionality from `properCoherentCohomologyFinite`, vanishing
  above the dimension from `noetherianSeparatedQuasicoherentVanishing`, and
  long exact sequences for `relativeCohomology`.
- Canonical isomorphisms for rebracketing tensor powers
  (`tensorAssociator`, `tensorPowAddIso`, `tensorRightUnitor`) and the
  transport of `IsZero` along them.

Substantial missing inputs need separate definitions, statements and
unconditional proofs, in dependency order. Conditional assembly is not a
proof of this proposition.

## Scope

The statement covers every universe `u`, every field in every
characteristic, every proper `X` (smooth or not, reduced or not, connected or
not, possibly empty) and every coherent `M`. It adds no smoothness,
projectivity, dimension index, section or vanishing hypothesis. The exponents
are natural numbers. Negative exponents, degree zero, and the relative form
over a noetherian base ring are not stated. For `L₁ = L₂` the statement
contains one-bundle Serre vanishing for all exponents `d ≥ 2n₀`. Publication
records a target for a later proof; it is not a vanishing theorem.

## Role and authorship

This is a prerequisite of task `6a5c4a64-6809-4f94-b35e-87cbc8a8b432`, owned
by Worker 1147 and Worker 1137, which proves the published
`Langlands.AbelianScheme.AmpleLineBundleHigherCohomologyVanishingStatement`.
That proof writes `ψ_k^* L ≅ L^{C(k+1,2)} ⊗ ((−1)^* L)^{C(k,2)}` on an
abelian variety by the theorem of the cube. It applies this statement with
`M` the structure sheaf, `L₁ = L` and `L₂ = (−1)^* L`, in which both
exponents grow. The consumer is not used to justify this statement.

Worker 1222 wrote the Lean declaration and this Markdown. The body follows
the task specification without change.
