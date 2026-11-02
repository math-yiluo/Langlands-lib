# Higher-cohomology vanishing for ample line bundles on abelian varieties

`Langlands.AbelianScheme.AmpleLineBundleHigherCohomologyVanishingStatement`
is a universe-polymorphic `Prop`-valued definition about actual ample line
bundles on abelian schemes over algebraically closed fields. It is the
algebraically closed field case of Mumford, Fogarty and Kirwan, *Geometric
Invariant Theory*, third edition, Proposition 6.13 (i), printed p.123 /
PDF p.136. That field case is the form proved on printed pp.123–124 /
PDF pp.136–137. The module states the proposition only. It supplies no
proof and adds no axiom.

## Statement

For every universe `u`, every field `K : Type u` with `IsAlgClosed K`,
every `A : AbelianScheme (Spec (CommRingCat.of K))` and every actual line
bundle `L : LineBundle A.X.left`, the proposition says

```text
L.IsAmple →
  ∀ i : ℕ, 0 < i →
    IsZero ((DerivedSections.relativeCohomology A.X.hom i).obj L.obj).
```

In words: if `L` is ample, then the `K`-module `Hⁱ(A, L)` is zero in every
positive degree `i`. Degree zero is not constrained.

## Complete checked type

The source declaration is

```lean
def AmpleLineBundleHigherCohomologyVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L : LineBundle A.X.left), L.IsAmple →
      ∀ i : ℕ, 0 < i → IsZero ((DerivedSections.relativeCohomology A.X.hom i).obj L.obj)
```

inside `namespace Langlands.AbelianScheme`, with
`open CategoryTheory CategoryTheory.Limits AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules`.
The module imports only `Langlands.AbelianScheme.Basic`,
`Langlands.AlgebraicGeometry.Modules.DerivedSections`,
`Langlands.AlgebraicGeometry.Picard.Ample` and
`Mathlib.FieldTheory.IsAlgClosed.Basic`. With `pp.fieldNotation false`,
`pp.proofs true` and `pp.funBinderTypes true`, `#print` in the approved
environment reports:

```text
def Langlands.AbelianScheme.AmpleLineBundleHigherCohomologyVanishingStatement.{u} : Prop :=
∀ (K : Type u) [inst : Field K] [IsAlgClosed K] (A : Langlands.AbelianScheme (AlgebraicGeometry.Spec ↧K))
  (L :
    Langlands.AlgebraicGeometry.Picard.LineBundle
      (CategoryTheory.Over.left
        (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))),
  Langlands.AlgebraicGeometry.Picard.LineBundle.IsAmple L →
    ∀ (i : ℕ),
      0 < i →
        CategoryTheory.Limits.IsZero
          (CategoryTheory.Functor.obj
            (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology
              (CategoryTheory.Over.hom
                (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))
              i)
            (CategoryTheory.ObjectProperty.FullSubcategory.obj L))
```

and `#check` reports type `Prop`. Here `↧K` is `CommRingCat.of K`, and
`A.X` abbreviates `Grp.X (CommGroupScheme.toGrp (toCommGroupScheme A))`.

## Library objects used

The statement uses only published definitions. It introduces no new data,
structure, certificate or axiom.

- `A : AbelianScheme S` is the published bundle: a commutative group scheme
  over `S` whose structure morphism `A.X.hom : A.X.left ⟶ S` is smooth,
  proper and geometrically connected. Geometric connectedness is Mathlib's
  `GeometricallyConnected`: the base change to every field over `S` is a
  nonempty connected space. Here `S = Spec K`.
- `LineBundle X` is the full subcategory of actual `X.Modules` that are
  locally isomorphic to the structure sheaf, that is, invertible sheaves.
  Its underlying sheaf of modules is `L.obj`.
- `L.IsAmple` is the published predicate of `Picard.Ample`:

  ```text
  CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
    x ∈ L.sectionOpen s ∧ IsAffineOpen (L.sectionOpen s)
  ```

  Here `L.powSections n` is the global sections of the published tensor
  power `tensorPow L.obj n`, and `L.sectionOpen s` is the largest open on
  which `s` trivializes that power. The scheme is quasi-compact and every
  point lies in an affine generation locus of a section of a positive
  power.
- `DerivedSections.relativeCohomology f i`, for `f : X ⟶ Spec R`, is by
  definition `(relativeGlobalSections f).rightDerived i`, where
  `relativeGlobalSections f = Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor`.
  It is a functor from actual `X.Modules` to `ModuleCat R`, computed with
  injective resolutions in the abelian category `X.Modules`. Here
  `f = A.X.hom` and `R = CommRingCat.of K`, whose carrier is `K`, so
  `(relativeCohomology A.X.hom i).obj L.obj` is the actual `K`-module
  `Hⁱ(A, L)`.
- `IsZero` is categorical zero in the module category over `K`. A module is
  a zero object exactly when its only element is zero.

No cohomology module, comparison isomorphism, projective embedding or
vanishing fact is supplied as a hypothesis.

## Original source and errata check

The original is D. Mumford, J. Fogarty and F. Kirwan, *Geometric Invariant
Theory*, third edition (1994), registered as
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`,
retained as
`literature/Mumford, Fogarty, Kirwan - Geometric Invariant Theory, 3rd edition (1994), Chapter 6.pdf`.
The SHA256 of that file was rechecked on 2026-11-01. Printed page numbers
are PDF page numbers minus 13.

- Chapter 6 opens on printed p.115 / PDF p.128 with the convention that
  all pre-schemes in the chapter are locally noetherian schemes.
  Definition 6.1 on the same page reads: "Let `S` be a noetherian scheme. A
  group scheme `π: X → S` is called an abelian scheme if `π` is smooth and
  proper, and the geometric fibres of `π` are connected." The following
  remark says that when `S = Spec(k)` abelian schemes are known to be
  commutative as groups.
- Proposition 6.13, printed p.123 / PDF p.136, reads: "Let `π: X → S` be a
  projective abelian scheme. Let `L` be an invertible sheaf on `X`,
  relatively ample for `π`. Then (i) `R^iπ_*(L) = (0)`, if `i > 0`." Parts
  (ii)–(iv) concern the direct image, the degree of `Λ(L)` and projective
  embeddings; they are not stated here.
- The proof first notes that (i) on the fibres of a flat proper morphism
  gives (i) globally (Ch. 0, §5 (a)). It then says that the only remaining
  point is the following field case: "suppose `A` is an abelian variety over
  a field `k`, and `L` is an ample invertible sheaf on `A`. Then we must
  prove that `H^i(A, L) = (0)`, `i > 0`. Also, we can assume that `k` is
  algebraically closed for simplicity." The argument is on printed
  pp.123–124 / PDF pp.136–137 and is summarized under the proof
  obligations below. A footnote adds that over a field (i) is also proved in
  Mumford's *Abelian Varieties*, §§16–17.
- The ampleness notion is that of EGA II. For example, printed p.39 /
  PDF p.52 proves that a sheaf is "ample ... in the sense of Theorem 4.5.2
  Chapter 2, EGA".

The statement here is this field case, with the field algebraically closed,
`A` the published abelian scheme over `Spec K`, `L` an actual ample line
bundle, and `H^i(A, L)` read as the published right-derived functor of
`K`-module global sections. The degree range `i > 0` is the source's.

The source cohomology is ordinary sheaf cohomology. The Library computes
right-derived functors in the category of sheaves of `𝒪_A`-modules. These
agree by the standard comparison (Hartshorne, *Algebraic Geometry*,
III.2.6), which the Library has not formalized and this statement does not
claim. Since `Spec K` has one point, the sheaf `R^iπ_*(L)` on it is
determined by its global value `H^i(A, L)`, so the field case of (i) is
exactly `H^i(A, L) = 0` for `i > 0`.

Errata check. On 2026-11-01 the Crossref records for the book
(DOI `10.1007/978-3-642-57916-5`) and for its chapter "Abelian schemes"
(DOI `10.1007/978-3-642-57916-5_7`, pp.115–127) were queried; neither
lists an erratum or update, and no work is registered as updating the
book or that chapter. The publisher's book page could not be read from the
project sandbox because of a browser challenge. No source-specific errata
note was present in the project, Library or workspace `notes/errata/`
locations. This records the locations checked; it does not assert that no
errata exist.

## Comparison of source hypotheses with the Library interfaces

No genuine mismatch was found. Each source hypothesis is either part of
the published interfaces or follows from them over `Spec K`.

- *Noetherian base and locally noetherian schemes.* `Spec K` is
  noetherian. `A.X.left` is of finite type over `K`, because proper
  morphisms are of finite type, so it is noetherian.
- *Abelian scheme.* Over `Spec K`, an abelian scheme in the sense of
  Definition 6.1 is commutative by the remark after it, so it underlies a
  published `AbelianScheme`; conversely every published `AbelianScheme`
  forgets to a smooth proper group scheme. On geometric fibres: Mathlib's
  condition quantifies over all fields over `K`, so it contains the source
  condition for algebraically closed fields. Conversely, if `X_Ω` is
  connected for an algebraic closure `Ω` of a field `F` over `K`, then
  `X_Ω → X_F` is surjective, as a base change of the surjection
  `Spec Ω → Spec F`. So `X_F` is connected; it is nonempty because the
  identity section gives an `F`-point. Thus the two notions agree. The
  published `Langlands/AbelianScheme/Basic.md` records the general
  comparison with the source definitions.
- *Relatively ample.* Stacks Project Definition 29.38.1, tag
  [01VH](https://stacks.math.columbia.edu/tag/01VH), calls `L` `f`-ample if
  `f` is quasi-compact and `L` restricted to `f⁻¹(V)` is ample for every
  affine open `V ⊆ S`. Over `S = Spec K` the affine opens are `Spec K` and
  the empty set. On the empty scheme every invertible sheaf is ample. Since
  `A.X.hom` is proper, hence quasi-compact, relative ampleness for `π` is
  exactly ampleness of `L` on `A`. The source's own field case assumes
  ampleness. This source is registered as
  `stacks-field-base-change-ampleness-2026-10-26`, file `01VG.html`.
- *Ampleness.* `L.IsAmple` formalizes Stacks Project Definition 28.27.1,
  tag [01PS](https://stacks.math.columbia.edu/tag/01PS), which Stacks
  identifies with EGA II Definition 4.5.3; see `Picard/Ample.md`. Its
  generation locus is the largest open on which the section trivializes the
  tensor power. For invertible tensor powers this is the source locus
  `X_s` by Stacks Lemma 17.25.10, tag
  [01CY](https://stacks.math.columbia.edu/tag/01CY). The equality is
  mathematics recorded in `Picard/Ample.md`, not a Library theorem, and
  the statement does not use it.
- *Projective.* Proposition 6.13 assumes `π` projective. The statement has
  no projectivity binder because over `Spec K` this follows from the
  published hypotheses. Stacks Project Lemma 29.44.6, tag
  [0B5N](https://stacks.math.columbia.edu/tag/0B5N), says a proper morphism
  with an `f`-ample invertible sheaf is locally projective. By
  Definition 29.44.1, tag [01W8](https://stacks.math.columbia.edu/tag/01W8),
  this means projective over the members of an open covering of the base.
  Any open covering of the one-point space `Spec K` contains `Spec K`, so
  `π` is projective. Over a field every finite type module is free, so a
  closed subscheme of `P(E)` is a closed subscheme of some `P^n_K`.
  Therefore the EGA and the H-projective conventions agree here. This
  source is registered as
  `stacks-projective-space-twists-morphisms-2026-10-26`, file `01W7.html`.
  None of these projectivity facts is formalized or assumed in the Lean
  statement.
- *Algebraically closed field.* The source proves the field case for an
  arbitrary field, reducing to an algebraically closed field "for
  simplicity". The `IsAlgClosed K` binder is the specification requested
  for this target. It specializes the source claim; it does not strengthen
  it.

## Proof obligations for the later exact proof

After independent acceptance and publication, a separate exact-target
proof must have this entire named proposition as its type, with no extra
outer hypotheses. The source argument has the following steps; none is
proved here.

1. Serre vanishing. Since `L` is ample on the projective `A`, there is `n₀`
   with `H^i(A, L^n) = 0` for all `n ≥ n₀` and `i > 0`.
2. Translation. Let `L'` be algebraically equivalent to `L^n`. Since
   `Λ(L^n)` is surjective, `L'` is isomorphic to a translate of `L^n` by a
   point of `A(k)`. Translations are automorphisms, so `H^i(A, L') = 0`
   for `i > 0` and `n ≥ n₀`.
3. Multiplication. For multiplication `ψ_k` by an integer `k`, the bundle
   `ψ_k^*(L)` is algebraically equivalent to `L^{k²}` (the source cites
   Lang, p.92). So for `k² ≥ n₀`, step 2 gives
   `H^i(A, ψ_{k*} ψ_k^* L) = H^i(A, ψ_k^* L) = 0` for `i > 0`, using that
   `ψ_k` is finite.
4. Splitting. If the characteristic does not divide `k`, then `L` is a
   direct summand of `ψ_{k*} ψ_k^* L`, through the canonical map and
   `k^{-2g}` times the trace, where `g` is the dimension of `A`. So
   `H^i(A, L) = 0` for `i > 0`. Such `k` with `k² ≥ n₀` always exist.

A later exact proof must therefore implement, for the published
`relativeCohomology`, Serre vanishing for ample bundles on the proper
`A.X.left`, invariance of cohomology under translation, the
algebraic-equivalence and surjectivity inputs, cohomology of finite
pushforwards and the trace splitting, or another unconditional route. The
published cohomology foundation alone does not supply these. Substantial
missing inputs need separate definitions, statements and unconditional
proofs in dependency order; conditional assembly is not a proof of this
proposition. Existing Library material that may help includes the proved
`multiplication_isFinite_of_ne_zero` and `multiplication_isIsogeny_of_ne_zero`
in `Langlands/AbelianScheme/FieldMultiplicationFiniteEtale`, and the
statement targets `FieldTheoremOfTheSquareStatement` and
`FieldSymmetricMultiplicationPullbackStatement`; this list is a pointer,
not a claim that these suffice.

## Scope

The statement covers every universe `u`, every algebraically closed field
in every characteristic, every positive degree, and every dimension. No
dimension index, dual-existence premise, finite-level datum, projectivity,
positivity of `H⁰`, concentration theorem or vanishing hypothesis is
added; the only hypothesis on `L` is the published ampleness. Degree zero
is not constrained. Mathematically, in dimension zero `A.X.left` is
isomorphic to `Spec K`, every line bundle on it is trivial and ample, and
its higher cohomology vanishes, so the statement is not vacuous there.

The general relative form of Proposition 6.13 (i), over a noetherian base,
is not stated here. Publication of this statement records a target for a
later proof; it is not a vanishing theorem.

## Role and authorship

This is a focused prerequisite of task
`baec6a6d-fe08-417e-95fd-fb8e2291cb1d`, owned by Worker 689 and
Worker 100, which proves the published
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyStatement`.
The vanishing half of that statement applies this target to the cube of
the canonical diagonal bundle, once that cube is shown to be ample. The
parent is not used to justify this statement.

Worker 921 implemented the Lean declaration and this Markdown. The
binders and conclusion follow the task specification.
