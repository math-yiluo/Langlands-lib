# Invariant cohomology of equivariant sheaves as derived `Hom` from the trivial representation

Author: Worker 16.

This module declares, in the namespace
`Langlands.Cohomology.EquivariantComposite`, one auxiliary definition and
three theorem-statement definitions. The statements are propositions, not
proofs: the isomorphisms and their naturality are their conclusions, and
nothing is supplied as data or as a hypothesis about cohomology. No proof is
given here; the truth arguments below explain why the statements hold.

Invariant sections are a composite functor: sections, a representation of
`G`, followed by `G`-invariants. Grothendieck's Tohoku, Chapter V, Theorem
5.2.1, derives this composite for ordinary sections. Berkovich's Corollary
1.5.2(i) asserts the analogue with compact supports. Both state a spectral
sequence `E_2^{p,q} = H^p(G, H^q(…)) ⇒ H^{p+q}(…; G, F)`. The propositions
below state the composite-functor identification behind these spectral
sequences, in derived-category form. The derived invariant sections of `F` in
degree `n` are the morphisms, in the derived category of representations,
from the trivial representation to the `n`-th shift of the derived section
complex of `F`. The isomorphisms are natural in `F`. The spectral sequence
itself is not constructed or stated here (see "Not stated here").

## Setting

`R`, `G` and `X` lie in one universe `u`, as required by the imported
modules. `R` is a commutative ring, `G` a group and `X` a topological space
with a left action `MulAction G X` for which every `g` acts continuously
(`ContinuousConstSMul G X`). So each `g` acts by a homeomorphism, with
inverse `g⁻¹`.

Declarations of other modules that are used:

- `TopologicalSheaf G X (ModuleCat R)` (module
  `Langlands.Sheaf.Equivariant.Topological`): the Library's category of
  `G`-equivariant sheaves of `R`-modules on `X`. These are presheaves on the
  transport category of opens whose underlying presheaf is a sheaf;
  morphisms commute with restriction and with transport by `G`.
- `EquivariantDerivedSections.invariantGlobalDerived R G X n` (module
  `Langlands.Cohomology.EquivariantDerivedSections`, Worker 13): the `n`-th
  right derived functor, computed with injective resolutions of equivariant
  sheaves, of the invariant global sections `F ↦ Γ(X, F)^G`. It takes values
  in `ModuleCat R`. This is Tohoku's `H^n(X; G, F) = R^n Γ_X^G(F)` (5.2.3).
- `EquivariantDerivedComplex.globalComplex R G X` (module
  `Langlands.Cohomology.EquivariantDerivedComplex`, Worker 13): the derived
  global section complex `RΓ(X, F)`. It is an object of the bounded below
  derived category `DerivedCategory.Plus (Rep R G)`. It is
  `DerivedPlus.derivedComplex` of the section representation, that is,
  Mathlib's `rightDerivedFunctorPlus` applied to `F` placed in degree `0`. Its
  cohomology in degree `q` is the derived global sections `H^q(X, F)` as a
  representation (`globalComplexHomologyIso`).
- `HasStableNeighbourhoods G X` (module
  `Langlands.Sheaf.Equivariant.SmoothPart`): every open neighbourhood of
  every point contains an open neighbourhood of that point stable under some
  open subgroup of `G`.
- `SmoothTopologicalSheaf R G X` (module `Langlands.Sheaf.Equivariant.Smooth`):
  the full subcategory of smooth equivariant sheaves. In these, every section
  is, near every point, fixed by an open subgroup stabilizing a neighbourhood
  of that point. Under the standing hypotheses of the imported modules
  (`IsTopologicalGroup G`, `HasStableNeighbourhoods G X`) it is abelian with
  enough injectives.
- `SmoothSheafCohomology.invariantCompactDerived R G X n` (module
  `Langlands.Cohomology.SmoothSheafCohomology`, Worker 13): the `n`-th right
  derived functor, computed with injective resolutions in the smooth
  category, of the invariant compactly supported sections
  `F ↦ Γ_c(X, F)^G`. A section has compact support when its support, the
  closed set of points where its germ is nonzero, is compact. Worker 13's
  Markdown explains why this has the shape of Berkovich's
  `H^n_c(X(G), F)`.
- `SmoothSheafDerivedComplex.compactComplex R G X` (module
  `Langlands.Cohomology.SmoothSheafDerivedComplex`, Worker 13): the derived
  compact section complex `RΓ_c(X, F)` in
  `DerivedCategory.Plus (SmoothRep R G)`. Its cohomology in degree `q` is the
  derived compact sections in the smooth category
  (`compactComplexHomologyIso`).
- Mathlib: `Rep R G` (representations), `Rep.trivial R G R` (the trivial
  representation on `R`), `HasDerivedCategory` (a choice of model of the
  derived category), `DerivedCategory.singleFunctor C 0` (an object placed in
  degree `0`), `DerivedCategory.Plus.ι` (the inclusion of the bounded below
  derived category) and `ShiftedHom A B n`. The last is by definition
  `A ⟶ B⟦n⟧` and carries the additive group structure of the preadditive
  derived category. `f⟦n⟧'` is the image of a morphism `f` under the shift
  functor.

The auxiliary definition `trivialSmoothRep R G` is the trivial representation
`Representation.trivial R G R` packaged as a smooth representation
(`Langlands.SmoothRep.of`). Its smoothness obligation, that every vector is
fixed by an open subgroup, is proved in the definition: the whole group `G`
is an open subgroup fixing every vector. It is introduced here because the
Library has no trivial smooth representation over a general commutative
ring.

## Declarations

| Declaration | Hypotheses | Conclusion |
| --- | --- | --- |
| `EquivariantGlobalCompositeStatement` | `R` a commutative ring, `G` a group, `X` a topological space with an action of `G` by continuous maps; any models `HasDerivedCategory.{w}` of equivariant sheaves and `HasDerivedCategory.{w'}` of `Rep R G`; `n : ℕ`. | There is a family `e F` of additive isomorphisms, one for each equivariant sheaf `F`, from `(invariantGlobalDerived R G X n).obj F` to `ShiftedHom (single₀ (Rep.trivial R G R)) (ι (globalComplex F)) n`. The family is natural: for `f : F ⟶ F'`, `e F' (H^n(f) x) = e F x ≫ (ι (globalComplex.map f))⟦n⟧'`. |
| `CompactGroupCompactCompositeStatement` | `R` a commutative ring, `G` a compact topological group, `X` a topological space with an action of `G` by continuous maps and `HasStableNeighbourhoods G X`; any models of the derived categories of `SmoothTopologicalSheaf R G X` and of `SmoothRep R G`; `n : ℕ`. | The same, for smooth sheaves: a natural family of additive isomorphisms from `(invariantCompactDerived R G X n).obj F` to `ShiftedHom (single₀ (trivialSmoothRep R G)) (ι (compactComplex F)) n`. |
| `EquivariantCompositeStatements` | — | The conjunction of the two. |

In classical notation the two conclusions read

```
H^n(X; G, F)   ≅ Hom_{D(Rep R G)}(R, RΓ(X, F)[n]),
H^n_c(X; G, F) ≅ Hom_{D(SmoothRep R G)}(R, RΓ_c(X, F)[n]),
```

naturally in `F`, where `R` is the trivial representation in degree `0`.

Conventions and choices:

- The propositions quantify over all models of the derived categories. Any
  two models are equivalent, so for each choice of universes `w`, `w'` the
  statement does not depend on the model. The universes `w`, `w'` of the
  morphisms of the two derived categories are independent level parameters.
  Mathlib's `HasDerivedCategory.standard` supplies a model, and the test below
  uses it.
- The isomorphisms are additive (`≃+`), not `R`-linear. Mathlib's derived
  categories carry no `R`-linear structure here, so the `R`-module structure
  of the morphism groups is not stated.
- The degree `n` ranges over `ℕ`, where the derived functors on the left are
  defined. For negative `n` the right side vanishes, since the section
  complexes have cohomology only in degrees `≥ 0`.
- Only existence of a natural family is asserted, not that it is the
  canonical comparison map.

## Truth argument

Both statements are instances of Grothendieck's composite-functor principle.
Invariants are morphisms from the trivial representation:
`M^G ≅ Hom_{Rep R G}(R, M)` naturally in `M`. In Mathlib this is the
adjunction `Rep.invariantsAdjunction`, trivial representations ⊣ invariants.
The same holds in `SmoothRep R G` with `trivialSmoothRep R G`. So the right
derived functors of `(-)^G` are `Ext^p(R, -) = Hom_D(R, -⟦p⟧)`. Let `Φ` be the
section functor (`Γ` or `Γ_c`) and `F → I^•` an injective resolution. It
suffices to show that every `Φ(I^k)` is acyclic for `Hom(R, -)`. Then
`Φ(I^•)` represents the derived section complex. For a bounded below complex
`C` of such acyclic objects, `Hom_D(R, C⟦n⟧) = H^n(Hom(R, C))`. To see
this, truncate `C` stupidly above degree `n + 1`, which does not change
`Hom_D(R, C⟦n⟧)`. Then induct on the length of the bounded complex using the
`Ext` vanishing. So
`Hom_D(R, Φ(I^•)⟦n⟧) = H^n(Φ(I^•)^G) = R^n(Φ^G)(F)`. Both sides are computed
functorially from the same resolutions, which gives naturality in `F`.

**Global sections.** The section representation `Γ(X, -)` from equivariant
sheaves to `Rep R G` has an exact left adjoint. It sends a representation `M`
to the constant sheaf `M_X`, with `G` acting on `X` and on `M`. Hence `Γ(X, -)`
sends injective equivariant sheaves to injective representations. This is
Tohoku's Corollary to Proposition 5.1.3: "si A est un G-faisceau abélien
injectif, alors Γ(A) est un G-module injectif". Injective representations are
acyclic for `Hom(R, -)`.

**Compact supports, `G` compact.** Let `I` be an injective smooth sheaf.

1. Every `s ∈ Γ_c(X, I)` is fixed by an open subgroup `H`. This is the
   smoothness of compact sections, proved in the Library by
   `CompactSections.isSmooth_representation_of_isSmoothSheaf`. As `G` is
   compact, `H` has finite index, so the orbit `G·s` is finite. The union of
   the supports of the `g·s` is then a closed, compact, `G`-stable set `K`.
   Hence `Γ_c(X, I)` is the directed union of the subrepresentations
   `Γ_K(X, I)` of sections supported in `K`. Here `K` runs over the closed,
   compact, `G`-stable subsets.
2. For such `K`, with inclusion `i : K → X`, `Γ_K(X, -)` is right adjoint to
   `M ↦ i_*(M_K)`. This is the extension by zero of the constant sheaf on `K`
   with its `G`-action. That sheaf is smooth: near a point of `K` a section is
   a constant `m`, and the open subgroups fixing `m` and stabilizing a small
   neighbourhood are given by smoothness of `M` and `HasStableNeighbourhoods`.
   The functor is exact. So `Γ_K(X, I)` is injective in `SmoothRep R G`.
3. Smooth representations of a compact group are representations of its
   profinite quotient by the intersection of its open normal subgroups.
   There, `Ext^p(R, -)` is continuous-cochain cohomology and commutes with
   filtered colimits. So `Ext^p(R, Γ_c(X, I)) = colim_K Ext^p(R, Γ_K(X, I)) = 0`
   for `p > 0`.

Continuity of the action map `G × X → X` is not used, and is not assumed.

**The compact-support statement fails for noncompact `G`.** Let
`G = Multiplicative ℤ`, discrete, act on `X = ℤ`, discrete, by translation.
Then every equivariant sheaf is smooth and `HasStableNeighbourhoods` holds.
Let `F` be the constant sheaf `R` with `R ≠ 0`.

- An invariant section with compact support has a finite `G`-stable support,
  hence empty support, so it is zero. The functor `Γ_c(X, -)^G` is zero, and
  so are all its derived functors.
- On a discrete space `Γ_c(X, -)` is the exact direct-sum functor. So
  `RΓ_c(X, F)` is the regular representation `R[G]` in degree `0`. Then
  `Hom_D(R, R[G]⟦1⟧) = H^1(ℤ, R[ℤ]) = R[t, t⁻¹]/(t - 1) ≅ R ≠ 0`.

So the isomorphism fails in degree `1`. The same example (a discrete
`ℤ`-indexed family of points of a `k`-analytic space, with `ℤ` acting by
translation) contradicts Berkovich's spectral sequence for that discrete
group: `E_2^{1,0} = H^1(ℤ, R[ℤ]) ≠ 0`, all other `E_2` terms vanish, and the
abutment `H^1_c(X(G), F)` is `0`. This is why
`CompactGroupCompactCompositeStatement` assumes `CompactSpace G`.

## Source correspondence

**Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J.
9 (1957), Chapter V, §§5.1–5.2** (registered source
`provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`,
file SHA-256
`7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`). The
following passages were read in the original, with the formulas checked
visually.

- §5.1, printed p.195 (PDF p.77): a group `G` acts on a space `X`, not
  necessarily faithfully. `G`-sheaves are sheaves on which `G` acts
  compatibly with its action on `X`. The Lean statement takes an arbitrary
  group acting by homeomorphisms and the Library's equivariant sheaves of
  `R`-modules.
- Corollary to Proposition 5.1.3, printed p.198 (PDF p.80): `Γ` of an
  injective `G`-sheaf is an injective `G`-module. This is the input of the
  global truth argument.
- (5.2.1)–(5.2.2), printed p.199 (PDF p.81): `Γ_X^G(A) = Γ_X(A)^G` and
  `Γ_X^G = Γ^G Γ_X = Γ_Y f_*^G`.
- (5.2.3) and Theorem 5.2.1 with (5.2.5), printed p.200 (PDF p.82):
  `H^n(X; G, A) = R^n Γ_X^G(A)`, and the second spectral functor with
  `II_2^{p,q}(A) = H^p(G, H^q(X, A))`. It comes from applying Theorem 2.4.1 to
  the composite `Γ^G Γ_X`.

The Lean statement is the derived-category form of that composite: the
identification `R(Γ^G ∘ Γ_X) ≅ RHom(R, RΓ_X(-))`. The spectral sequence II is
its hyperext spectral sequence. Changes, all derived reformulations or
generalizations:

- Coefficients are sheaves of modules over a commutative ring `R`, with
  `R = ℤ` giving Tohoku's abelian `G`-sheaves.
- `H^p(G, -)`, Tohoku's derived functors of invariants on `G`-modules,
  appears as `Ext^p_{Rep R G}(R, -)`. For `R = ℤ` these coincide.
- The spectral sequence is replaced by the composite isomorphism from which
  it is derived.
- Tohoku's first and third spectral sequences, through the orbit space `Y`,
  are not treated.

**Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(unfinished manuscript, 1995–1996)** (registered source
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
The following passages were read in the original, and p.12 was checked
visually.

- §1.1, printed p.2: a `G`-space is an analytic space with a continuous
  action of a topological group `G`. Continuity means continuity into the
  automorphism group, whose topology is given by the stabilizers of
  coverings. The Lean analogue is `HasStableNeighbourhoods` on a topological
  space.
- §1.5, printed p.11: `Γ_{c,X(G)}(F)`, the sections over `X(G)` (the
  invariant sections) with compact support, and its derived functors
  `H^q_c(X(G), F)`.
- Corollary 1.5.2(i), printed pp.11–12: there is a spectral sequence
  `E_2^{p,q} = H^p(G, H^q_c(X, b^*F)) ⇒ H^{p+q}_c(X(G), F)`.

Changes and source gap:

- The analytic étale site is replaced by the ordinary topology of `X`, with
  the Library's smooth equivariant sheaves. This is the same transport made
  by Worker 13's `SmoothSheafCohomology`. Coefficients are `R`-modules.
- The source asserts the spectral sequence for every topological group `G`.
  The example above shows that this fails for noncompact `G`, so the
  statement is restricted to compact `G`. No proof is printed beyond "the
  general case follows from Proposition 1.5.1". The restriction is a
  correction of the source, not a weakening of something true.
- `H^p(G, -)` on discrete `G`-modules appears as `Ext^p` in smooth
  representations. On the `E_2` page this yields
  `H^p(G, H^q_c(X{G}, F))`, cohomology derived in the smooth category. The
  first claim of Corollary 1.5.2(i), `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`
  (comparison with derived functors computed without the group), is not
  stated here. Neither is the spectral sequence itself.

**Use in Harris.** Harris, *Galois properties of cohomological automorphic
forms on GL(n)* (1999), §2, printed p.304 (registered source
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`), quotes
Berkovich's resolutions of torsion étale sheaves on `U(ẽ)` by étale sheaves in
smooth `S(ẽ)`-modules. These resolutions are acyclic for the compactly
supported section functor (Facts 3–4, Lemma 2.2), and Harris computes
compactly supported cohomology with its group action through them. This
module states the abstract derived-functor identification for invariants
over an ordinary topological space. Harris's analytic spaces, the groups
`S(ẽ)` and Harris's resolutions are not treated.

## Nonvacuity and checks

A private test file, not part of this module, compiled the following over it:

```lean
open CategoryTheory Langlands.Sheaf.Equivariant Langlands.Cohomology.EquivariantComposite

example (G X : Type) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] :
    IsTopologicalGroup G ∧ CompactSpace G ∧ HasStableNeighbourhoods G X :=
  ⟨inferInstance, inferInstance, inferInstance⟩

example (G X : Type) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] :
    HasStableNeighbourhoods G X := inferInstance

example (h : EquivariantGlobalCompositeStatement.{1, 1, 0})
    (R G X : Type) [CommRing R] [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] (n : ℕ) : True := by
  let := HasDerivedCategory.standard (TopologicalSheaf G X (ModuleCat.{0} R))
  let := HasDerivedCategory.standard (Rep.{0} R G)
  obtain ⟨_e, _he⟩ := h R G X n
  trivial

example (h : CompactGroupCompactCompositeStatement.{1, 1, 0})
    (R G X : Type) [CommRing R] [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] (n : ℕ) : True := by
  let := HasDerivedCategory.standard (SmoothTopologicalSheaf R G X)
  let := HasDerivedCategory.standard (Langlands.SmoothRep.{0, 0, 0} R G)
  obtain ⟨_e, _he⟩ := h R G X n
  trivial
```

So the hypotheses of the compact statement hold for every finite discrete
group acting on any space. Stable neighbourhoods also hold for every
continuous action of a nonarchimedean group, for example a compact open
subgroup of `GL_n(ℚ_p)`. Both
statements apply to concrete data with Mathlib's standard derived categories,
with morphism universes `w = w' = 1` over `u = 0`.

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), over Library
commit `e449cde988d4e97ab280b8d4d11262887ccc26e0`:

- Diagnostic `7b1f23b2-025e-4c5d-a4f0-d181308c4e32` compiled the module with
  no errors or warnings. It inspected `EquivariantCompositeStatements`:
  `statement_returns_prop: true`, level parameters `w, w', u`, axioms
  `propext`, `Classical.choice`, `Quot.sound`.
- Diagnostics `a0d3e444-1906-4598-bc3c-87118db7e64e` and
  `feef6399-237d-4918-a4a1-b3ab03861a85` inspected the two component
  propositions (`statement_returns_prop: true`). Their sources differ from the
  final module only in the module docstring.
- Diagnostic `f4d28c2b-3267-4585-adf3-61bb44404ff4` compiled the test file
  above with no errors or warnings.

## Dependencies

Library commit `e449cde988d4e97ab280b8d4d11262887ccc26e0`:

- `Langlands.Cohomology.EquivariantDerivedComplex` (Worker 13):
  `globalComplex`. It imports `EquivariantDerivedSections` with
  `invariantGlobalDerived`, and `Langlands.Sheaf.Equivariant` with
  `TopologicalSheaf`.
- `Langlands.Cohomology.SmoothSheafDerivedComplex` (Worker 13):
  `compactComplex`. It imports `SmoothSheafCohomology` with
  `invariantCompactDerived`, and the smooth sheaf and smooth representation
  modules with `SmoothTopologicalSheaf`, `HasStableNeighbourhoods` and
  `Langlands.SmoothRep`.
- Mathlib `RepresentationTheory.Rep.Basic` (`Rep.trivial`).

## Not stated here

- The spectral sequences of Tohoku's (5.2.5) II and of Berkovich's
  Corollary 1.5.2(i) themselves. They follow from these identifications
  through the hyperext spectral sequence of `Hom(R, -)` applied to the
  truncations of the section complex. The companion module
  `Langlands.Cohomology.HyperextConvergence.HalfBoundedStatement` states the
  second page and the abutment of that covariant spectral sequence, obtained
  in the opposite derived category, and its convergence; its section
  "Application" explains how they combine with the statements here.
- Tohoku's spectral sequences through the orbit space (`I_2` of (5.2.5) and
  the third one), and Proposition 5.2.2.
- The first claim of Berkovich's Corollary 1.5.2(i) and its part (ii), and
  the comparison of smooth-category derived functors with those computed in
  all equivariant sheaves.
- Canonicity of the isomorphisms, `R`-linearity, and the analytic étale
  site.
