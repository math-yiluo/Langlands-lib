# Acyclic resolutions and right-derived comparison

Author: Worker 3.

This pair defines six propositions and their conjunction. It contains no
theorem proof or axioms. The original-source checks below establish the intended
meaning of the statements; their proofs and independent publication remain
separate obligations.

## Mathematical content

Let C and D be abelian categories, with independent object and morphism
universes. A right resolution of A is a nonnegatively graded cochain complex K
with an augmentation from the complex consisting of A in degree zero.
The augmentation is required to be a quasi-isomorphism. Thus it identifies
H^0(K) with A and forces positive-degree cohomology of K to vanish; it does not
assert anything about the cohomology after applying a functor.

The six component propositions are:

1. `ResolutionLiftStatement`: for any such resolution and any injective
   resolution I of A, an augmentation-compatible cochain map K to I exists.
   Any two such maps are homotopic. The source terms need not be injective.
   This statement needs only the chosen I, not enough injectives globally.
2. `AcyclicResolutionComparisonStatement`: assume C has injective resolutions,
   F is an additive left-exact functor C to D, and every term K^i is F-acyclic,
   meaning R^(n+1)F(K^i) is zero for every natural number n. Every lift to I
   becomes a quasi-isomorphism after applying F. The induced comparison from
   H^n(F(K)) to R^nF(A) is an isomorphism for every n.
3. `ResolutionComparisonIndependenceStatement`: the comparison to R^nF(A)
   agrees for any two injective resolutions and compatible lifts.
4. `ResolutionComparisonNaturalityStatement`: a cochain map g:K to L lifting
   f:A to B commutes with these comparisons and the actual map R^nF(f).
5. `ResolutionComparisonTransformationStatement`: a natural transformation
   alpha:F to G commutes with the comparison and the actual derived natural
   transformation R^n(alpha).
6. `AcyclicResolutionEquivarianceStatement`: a monoid acts on the actual
   object A and complex K, and the augmentation is equivariant. With the
   hypotheses of component 2, each comparison is the underlying map of an
   isomorphism in the category of monoid actions. The chosen lift from K to I
   is an ordinary cochain map; equivariance of that lift is not a hypothesis.

Components 3-5 concern equality of maps, so their formulations
require additivity but do not unnecessarily require acyclicity or left
exactness. The transformation statement compares functors with the same source
and target categories; it does not purport to cover every change-of-ring or
change-of-site square.

`AcyclicResolutionComparisonStatements` is their conjunction. Each component
is a `def` returning `Prop`, with its conclusion asserted only inside that
proposition. Defining the conjunction requires no proof of a component.

## Actual constructions and directions

The Lean objects are `CochainComplex C Nat`,
`CochainComplex.single₀ C`, `InjectiveResolution A`, and the existing
`Functor.rightDerived`. The latter is defined through injective resolutions,
the homotopy category, and its actual homology functor.

For a lift phi:K to I and degree n, the comparison is exactly

    H^n(F(K)) --H^n(F(phi))--> H^n(F(I)) --> R^nF(A).

The second arrow is `(I.isoRightDerivedObj F n).inv`. There is no arbitrary
comparison morphism or supplied isomorphism field. The isomorphism used here
is Mathlib's already constructed identification for an injective resolution;
the new assertion is that the first arrow is invertible for an acyclic
resolution.

`PreservesFiniteLimits F` expresses left exactness in the abelian setting.
Acyclicity is written using `IsZero` of the actual positive-degree right-derived
objects. It is a hypothesis to be proved separately for the eventual geometric
terms, not a definition of a Godement resolution or a hidden assumption of the
comparison theorem.

Naturality states

    H^n(F(g)) ; comparison_L = comparison_K ; R^nF(f).

Transformation compatibility states

    H^n(alpha_K) ; comparison_G = comparison_F ; R^n(alpha)_A.

Component 6 uses Mathlib's `Action`, with an actual monoid homomorphism into
endomorphisms of the object or complex, and `Functor.mapAction` on the two
displayed functors. For a monoid the operators are endomorphisms; if the monoid
is a group they are automorphisms. The equivariant augmentation is part of the
input mathematical data. The conclusion existentially quantifies an actual
isomorphism of these actions and requires its underlying map to equal the
comparison above. Thus it neither assumes the desired equivariance nor merely
asserts that the two action objects are accidentally isomorphic.

The algebraic equivariance assertion follows from component 4 by applying its
naturality identity to each monoid operator, then using component 2 for
invertibility. It does not assume the existence of an equivariant injective
resolution. No geometric action, topology, smoothness, Galois continuity,
cohomology group, filtration, or comparison functor is postulated. Actual
geometric actions and their topological properties remain separate work.

## Original-source correspondence

The primary sources are Cartan and Eilenberg, *Homological Algebra* (1956),
and Grothendieck, *Sur quelques points d'algebre homologique* (1957).
Cartan and Eilenberg work with modules. Grothendieck Section 2.3, printed
p.143, explicitly transfers the Chapter V construction to abelian categories,
subject to the existence of the required injective or projective resolutions.
The Lean statements use that abelian-category formulation.

| Lean component | Original location and correspondence |
| --- | --- |
| `ResolutionLiftStatement` | Cartan–Eilenberg V.1, Proposition 1.1a, p.78 (PDF p.100). An acyclic right complex maps to an injective right complex over a specified map of modules, uniquely up to homotopy. The Lean target specializes that map to the identity of A and the target to an injective resolution. The source proof is the dual of Proposition 1.1, pp.76–77; the source states the right-complex version without repeating that proof. |
| `AcyclicResolutionComparisonStatement` | Grothendieck Section 2.4, Remark 3 after Theorem 2.4.1, p.148 (PDF p.30). A right resolution by F-acyclic objects computes R^nF(A), and the comparison is explicitly the map induced by a lift to an injective resolution. This gives invertibility both of the induced cohomology maps and of the displayed composite with the injective-resolution identification. |
| `ResolutionComparisonIndependenceStatement` | Cartan–Eilenberg V.3, pp.82–83, especially equation (2) on p.83: the canonical map from the cohomology of a resolution after applying the functor to the derived functor is independent of the lift by V.1.1a and homotopy invariance. Independence from the chosen injective resolution is part of the preceding construction of the derived functor. Grothendieck 2.3, p.143, supplies the abelian-category scope. |
| `ResolutionComparisonNaturalityStatement` | Cartan–Eilenberg V.3, pp.82–83: the induced map depends only on the resolved-object morphism. Applying V.1.1a to the two composites of lifts gives the displayed naturality square. Grothendieck 2.5.2 and its proof, pp.149–150, also explicitly use comparison with an injective resolution to identify canonical, functorial comparison maps. |
| `ResolutionComparisonTransformationStatement` | Cartan–Eilenberg V.4, p.87, paragraph immediately before Proposition 4.4: a natural transformation of functors induces the derived transformation by application to resolutions and passage to cohomology. Together with the comparison of V.3, equation (2), naturality of alpha on a lift gives the square in the Lean definition. No acyclicity or left-exactness condition is needed for this identity of maps. |
| `AcyclicResolutionEquivarianceStatement` | Derived consequence of the preceding comparison and object-naturality statements: apply naturality to each monoid operator, then use invertibility of the underlying comparison. This is an algebraic consequence of the cited construction, not a separately quoted geometric theorem. |

The grading and homotopy conventions were also checked. Cartan–Eilenberg
IV.3, pp.58–59, uses cochain differentials of degree +1 and a homotopy s
of degree -1 satisfying ds+sd=g-f. Mathlib's `Homotopy f g` instead writes
f=dh+hd+g. The correspondence is h=-s. Since component 1 asserts only
existence of a homotopy, these conventions give exactly the same assertion.
Cartan–Eilenberg IV.5, pp.62–64, explains the action of additive functors
on complexes and homotopies; V.3 uses it for independence.

The comparison chosen here is the lift-induced map. Grothendieck p.148
distinguishes it from iterated connecting homomorphisms by a possible sign;
Cartan–Eilenberg V.7.1, pp.92–93, supplies the sign calculation in its
displayed setting. No equality with an unsigned iterated connecting map is
asserted by this pair.

Grothendieck Proposition 2.5.2, pp.149–150, concerns a resolving functor
and its bicomplex comparison. It is not simply the same statement as
component 2. The direct locator for component 2 is the p.148 remark.
Propositions 2.5.1–2.5.2 explain the uniqueness and comparison of the
resolving-functor model; Example a on p.150 supplies the exact-endofunctor
and iterated-cokernel construction relevant to the separate Godement
construction work.

EGA III, first part (1961), Chapter 0, 11.4.1 defines right resolutions;
11.4.3–11.4.5 explain hypercohomology and acyclic computation;
Lemma 11.5.2.4, printed p.38 (continuous p.382), states computation of right
derived functors by an acyclic resolution and explicitly refers to Tohoku
2.5.2. Remark 11.5.4 distinguishes bounded-below arguments from extensions
requiring additional colimit hypotheses. The present pair uses only
nonnegative complexes.

Registered EGA source:
`provided-bca66cf9ddf1864d04cd9ab13db3799e640164f5476bbe9ed23714ccc825ed03`;
folder fingerprint
`fb65e01feda254662655043bb84b343601696054c02f2c05f42548e66042f1d4`.
The actual file is
`Grothendieck--Preliminaires (EGA III-1, Chapitre 0, sections 8-13)--1961.pdf`,
SHA256 `24cb7a75e125f44022411d4b2a86afd2453ab45876945e0ee02b5dd8d5dc5655`.
The relevant text, 11.4.1 through 11.5.4, was read from the retained original.
Printed p.38 (PDF page 34) was also rendered and visually checked, including
the explicit reference from Lemma 11.5.2.4 to Tohoku Proposition 2.5.2.

Registered Tohoku source:
`provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`,
SHA256 `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`.
Retained file:
`literature/Grothendieck 1957 Tohoku original- acyclic resolutions and derived comparison.pdf`.
This 103-page scan contains both instalments, printed pp.119–183 and
185–221, with an intervening blank page. Printed page = PDF page + 118.
The actual retained bytes were verified. Printed pp.136–153 were read,
including Sections 2.1–2.5 and their proofs; pp.143 and 148–150 were
visually checked. No claim is made to have read the entire paper in this
verification.

Registered Cartan–Eilenberg source:
`provided-4e029ea5216cb6ce6bfc05060277910b86f223b69bc92c508711e3760612bd4e`,
SHA256 `1e0915f23ec4a4bd638f469561931f5659a7a47faf92d48468bd290ddd726365`.
Retained file:
`literature/Cartan-Eilenberg 1956 original- resolution comparison and derived functors.pdf`.
This is the 1956 Princeton printing, with 421 PDF pages. The imprint
year was checked on the page image because the OCR misreads it.
For printed pp.1–390, PDF page = printed page + 22.
The actual retained bytes were verified. Chapter V, pp.75–105, and
IV.1–5, pp.53–64, were read; pp.59, 78, 83 and 87 were visually checked.
This reading includes the left-complex lifting proof, its explicitly
stated right-complex dual, the derived comparison, and transformation
compatibility. No claim is made to have read the entire book.

## Scope and dependencies

This pair imports only pinned Mathlib through
`Mathlib.CategoryTheory.Abelian.RightDerived` and
`Mathlib.CategoryTheory.Action.Basic`. Its project environment is
artifact `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1:
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`;
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
It has no dependency on the unpublished inverse-limit or spectral-page
statements.

The Harris and Berkovich application still needs actual sheaf categories,
Godement complexes, exact augmentations, compact-support acyclicity, derived
comparison, group/Galois actions and coefficient transitions. These are not
supplied by the generic hypotheses above. No claim is made here about
Shimura cohomology or split-supercuspidal local-global compatibility, and no
banality or other torsion hypothesis is introduced.

The six-component source passed the pinned compiler and incremental Lake
check `c6893ce7-6717-45a9-98aa-57ea6afdaa07`, with zero errors and warnings.
The check used snapshot
`0fcd26e4b807daa3d66f11af312a710bf52aabdc47aafe1b3d933bfaf81fe07c`
and Lean source SHA256
`b4782eacea4576d1a7ebb7c6fcbd35f4c848e9545ffd49650a81294f269ce255`.
Exact inspection confirms that the conjunction returns `Prop`, with independent
universe parameters `u`, `v`, `u'`, `v'`, and `w`. Its target fingerprint is
`e947d1f106110f329d14004a5b820439af6a2e1533fff394fd0f8ce1348c4c58`.
All six component definitions and the conjunction were separately printed
and read in their elaborated forms. This verified the augmentation hypotheses,
the direction of each comparison, and the conclusion's placement outside the
assumptions. The sixth component's actual `Action` objects, the unconstrained
ordinary lift, and equality to the underlying map of the resulting action
isomorphism were checked explicitly. Compilation does not verify the
mathematical statements.

The comparison theorem proofs and independent acceptance/publication remain
separate obligations. Reading and registering the sources does not supply
these proofs, nor does this algebraic pair complete the Harris–Berkovich
theorem family.
