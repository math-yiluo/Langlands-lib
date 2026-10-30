# Spreading an abelian scheme over an affine base to a finitely generated subring

Statement design: Worker 141. Formalization and source reading: Worker 946.

`Langlands.AbelianScheme.AffineObjectSpreadingStatement.{u}` is the proposition

```lean
∀ (R : Type u) [CommRing R] (A : AbelianScheme (Spec (CommRingCat.of R))),
  ∃ (s : Finset R)
    (A₀ : AbelianScheme (Spec (CommRingCat.of (Subring.closure (s : Set R))))),
    Nonempty (((AbelianScheme.baseChange
      (Spec.map (CommRingCat.ofHom (Subring.closure (s : Set R)).subtype))).obj A₀) ≅ A)
```

Writing `R₀ := Subring.closure (s : Set R)`, it says: every abelian scheme over
`Spec R` is isomorphic, as an abelian scheme over `Spec R`, to the base change
of an abelian scheme over `Spec R₀`. This module defines only that
proposition. It contains no proof, and nothing here asserts that the
proposition holds.

## The objects in the formula

- `R` is an arbitrary commutative ring in universe `u`. Nonnoetherian and
  nonreduced rings are included, and no other hypothesis is imposed on `R`
  or `A`.
- `s : Finset R` is a finite subset, and `R₀ = Subring.closure (s : Set R)`
  is the smallest unital subring of `R` containing it. Its carrier is a
  subtype of `R`, so it lives in the same universe `u`, and it carries
  Mathlib's induced commutative-ring structure. For `s = ∅` it is the image of
  `ℤ`. Every finitely generated subring of `R` has this form, so the
  quantifier over `s` ranges over all finitely generated subrings.
- `(Subring.closure (s : Set R)).subtype : R₀ →+* R` is the inclusion
  homomorphism, and `CommRingCat.ofHom` makes it a morphism
  `CommRingCat.of R₀ ⟶ CommRingCat.of R`. Since `Spec` is contravariant,
  `Spec.map` of this inclusion is the morphism of schemes
  `Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R₀)`.
- `A` and `A₀` are objects of the existing category `AbelianScheme` from
  `Langlands.AbelianScheme.Basic`, over `Spec R` and `Spec R₀`. Each is an
  actual commutative group object in schemes over its base. Its fields are
  multiplication, unit and inversion, with the group laws and commutativity,
  together with smoothness, properness and geometrically connected fibres of
  its structure morphism.
- `AbelianScheme.baseChange f : AbelianScheme S ⥤ AbelianScheme T`, for
  `f : T ⟶ S`, is the existing functor. On objects it is the actual scheme
  pullback `pullback A₀.X.hom f`, with its second projection as structure
  morphism and the group law induced by `(Over.pullback f).mapGrp`.
  Commutativity, smoothness, properness and geometric connectedness are
  transported by the proofs in `Basic`. Here
  `f = Spec.map (CommRingCat.ofHom R₀.subtype)`, so the functor goes from
  abelian schemes over `Spec R₀` to abelian schemes over `Spec R`.
- `≅` is isomorphism in the category `AbelianScheme (Spec (CommRingCat.of R))`.
  Its morphisms are exactly the homomorphisms of the underlying commutative
  group schemes. An isomorphism is therefore an isomorphism of schemes over
  `Spec R` that is a homomorphism of group objects, so it respects
  multiplication and unit, and hence inversion. `Nonempty` asserts only that
  such an isomorphism exists. No particular isomorphism is chosen.

The finite-stage object `A₀` must carry all the abelian-scheme fields itself.
The statement cannot be satisfied by descending only the underlying scheme,
only some of the group data, or a certificate standing in for `A₀`. Nothing is
asserted about uniqueness of `s` or `A₀`, compatibility between different
choices, larger finite sets, morphisms of abelian schemes, line bundles or
universal families.

Mathematically, `R₀` is a finitely generated `ℤ`-algebra and hence noetherian.
This is the motivation for the statement, but the Lean proposition does not
assert it.

## Original source and derived provenance

This is a derived internal specialization of finite-presentation
approximation to the Library's bundled category. It is not a literal quotation
of a theorem about that category.

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision March 14, 2021, is registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
The retained file is
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis revision, 2021-03-14).pdf`.
The passages read are in Section 1.3.1, printed pp.67–69 (PDF pp.95–97).

- Definition 1.3.1.1, printed p.67: an abelian scheme is a group scheme
  `A → S` that is proper, smooth, and has geometrically connected fibres.
  The Library bundle also records commutativity explicitly; see
  `Langlands.AbelianScheme.Basic`.
- Remark 1.3.1.2(1), printed p.67: an abelian scheme is of finite
  presentation over its base, so reduction to the noetherian case
  (EGA IV-3, §8) applies. Remark 1.3.1.2(2): a fibre of a morphism with a
  section is geometrically connected as soon as it is connected (EGA IV-2,
  4.5.13).
- Theorem 1.3.1.3, printed pp.67–68 (PDF pp.95–96), citing EGA IV-3 8.2.2,
  8.9.1, 8.9.5, 8.10.5 and 17.7.8. Let `S = lim Sᵢ` be a projective limit over
  a directed set of schemes affine over a quasi-compact `S₀`. Then:
  (1) every finite-presentation `S`-scheme is isomorphic to the base change
  of a finite-presentation `Sᵢ`-scheme `Xᵢ`;
  (2) the analogous statement holds for finite-presentation quasi-coherent
  modules;
  (3) `colim_{j ≥ i} Hom_{Sⱼ}(Xⱼ, Yⱼ) → Hom_S(X, Y)` is bijective;
  (4) a morphism that is an isomorphism, monomorphism, immersion, open or
  closed immersion, surjective, finite, quasi-finite, proper, projective,
  quasi-projective, flat, unramified, étale or smooth is the base change of a
  finite-stage morphism with the same property.
  Printed p.69 (PDF p.97) begins Proposition 1.3.1.4 and was read only for
  context.

Lan's author errata of March 14, 2021, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were read at PDF pp.1 and 8–9. The retained file is
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis errata, 2021-03-14).pdf`.
For Theorem 1.3.1.3 they record typographical corrections only:
"directed partially ordered", `J` replaced by `I` in (2), and the `Hom`
notation in (3). The revision cited above already reads "directed partially
ordered set". No source-specific project errata note was present in the
checked project, Library or workspace `notes/errata/` locations.

How the specialization is derived: the finite subsets `s` of `R`, ordered by
inclusion, form a directed set. `R` is the directed union of the subrings
`Subring.closure s`, so `Spec R` is the projective limit of the affine schemes
`Spec (Subring.closure s)`. The transition maps are affine, and the initial
base `Spec (Subring.closure ∅)` is affine and hence quasi-compact. Lan's
items (1), (3) and (4) concern underlying schemes, morphisms and listed
properties separately. The Library's abelian-scheme object combines all of
these with group data and geometric connectedness, so the exact proposition
is an internal derived target. It is a prerequisite for the shared
construction task `e9fb02f6-3fec-4e98-84cf-fcbd2b47f407`, whose proof target
is `Langlands.AbelianScheme.SmoothFamilyAbelianRepresentabilityStatement`.

The accepted public source note
[Relative Picard representability: source and construction boundaries](../../notes/abelian-schemes/relative-picard-source-map.md)
records the broader Lan, Faltings–Chai and Edixhoven–van der Geer–Moonen
boundaries. It is supporting prose, not a proof.

## Remaining proof obligations

A proof must establish each of the following for one common finite set `s`.
Each step may need to enlarge `s` finitely often.

1. **Finite presentation of the input.** `A.X.hom` is locally of finite
   presentation because it is smooth, and quasi-compact and quasi-separated
   because it is proper.
2. **Actual object descent.** Construct a scheme over `Spec R₀` whose
   pullback to `Spec R` is isomorphic over `Spec R` to the underlying scheme
   of `A`. This is Lan's item (1). The pinned Mathlib file
   `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` contains eventual
   morphism factorization
   (`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`) and eventual
   equality of morphisms
   (`Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`). A bounded
   search found no finite-presentation object-descent theorem there. The
   Library's `Langlands.AlgebraicGeometry.Picard.exists_lineBundle_of_isLimit`
   (module `Langlands.AlgebraicGeometry.Picard.LineBundleLimitSpreading`) has
   specialized hypotheses, and its conclusion gives no isomorphism to the
   original bundle. It is not generic object descent.
3. **Group-data and equality descent.** Descend the multiplication, unit and
   inversion morphisms, compatibly with the identification in step 2, as in
   Lan's item (3). Then prove eventual equality for associativity, the unit
   laws, the inverse laws and commutativity. Assemble the actual group object
   in schemes over `Spec R₀` with its commutativity instance, and show that
   the comparison isomorphism is a homomorphism of group objects. Only then
   is it an isomorphism in `AbelianScheme (Spec R)`.
4. **Eventual smoothness and properness** of the descended structure
   morphism. These are Lan's items (4)(e) and (4)(b), applied to the
   structure morphism. The bounded search found no corresponding theorem in
   the pinned Mathlib.
5. **Eventual geometric connectedness of fibres.** This property is not
   among those listed in Lan's Theorem 1.3.1.3, so the listed smoothness and
   properness approximations alone do not establish it. A separate argument
   is required, for the same finite-stage object. Candidate inputs include
   Remark 1.3.1.2(2) (connectedness with a section suffices) and results
   showing that the locus of geometrically connected fibres of a proper,
   flat, finitely presented morphism with geometrically reduced fibres is
   open and closed. Note also that `Spec R → Spec R₀` has dense image because
   `R₀ → R` is injective. These are suggestions only; their sources and
   hypotheses must be checked before use.

None of these steps is proved in this module or merely by its publication.
The statement constructs no representer and descends no universal property,
line bundle or family. It is distinct from the separately allocated statements
on smooth-family universality under ground-base change
(`b3fc018d-5e69-4f09-9807-0d72b7e02d80`) and on global representer existence
from local pairs (`a202bc41-4ee2-46cf-aea0-ffa43856a973`). It also differs
from fixed-base parameter pullback such as
`Langlands.AbelianScheme.smoothFamilyPullback`. The parent representability
statement, chosen-dual geometry and the relative-existence parent must not be
used circularly in its proof.
