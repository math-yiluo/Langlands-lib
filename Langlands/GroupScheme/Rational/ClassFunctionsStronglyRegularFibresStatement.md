# Statement: strongly regular fibres of the canonical class-function quotient

Author: Worker 1729.

This module defines the proposition
`Langlands.GroupScheme.ClassFunctions.StronglyRegularFibresStatement.{u}`.
It specializes property 2 of
`Langlands.GroupScheme.QuasiSplitSteinbergQuotientStatement.{u}` to the
actual published morphism `ClassFunctions.rho G`. A separate proof must prove
this exact proposition.

## Complete Lean proposition

```lean
def StronglyRegularFibresStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K))),
    IsSimplyConnected G → ∀ hqs : IsQuasiSplit G,
    letI : IsAffineHom G.X.hom := hqs.isConnectedReductive.isAffineHom
    ∀ (F : Type u) [Field F] [Algebra K F]
      (y w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G.X)
      (S : GroupScheme (Spec (CommRingCat.of F)))
      (j : S ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G),
      IsTorus S → IsClosedSubgroup j →
      (∀ {Z : Over (Spec (CommRingCat.of F))}
          (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G).X),
        c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) =
            (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) * c →
          ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
      y ≫ ClassFunctions.rho G = w ≫ ClassFunctions.rho G →
      ∃ (E : Type u) (_ : Field E) (_ : Algebra K E)
        (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))))
        (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X),
        g * (q ≫ y) * g⁻¹ = q ≫ w
```

The imports are `Langlands.GroupScheme.Rational.ClassFunctions` and
`Langlands.GroupScheme.Rational.QuasiSplitSteinbergQuotientStatement`.
The namespace is `Langlands.GroupScheme.ClassFunctions`; there is one
arbitrary universe parameter `u`.

## Actual objects, hypotheses and conclusion

The fields `K` and `F` both belong to `Type u`, with `[Algebra K F]`.
They may be finite or imperfect, and their characteristics are unrestricted.
The group scheme `G` over `Spec K` is assumed only to satisfy the parent's
`IsSimplyConnected G` and `IsQuasiSplit G`. The local instance

```lean
letI : IsAffineHom G.X.hom := hqs.isConnectedReductive.isAffineHom
```

derives the affineness needed to form `ClassFunctions.rho G` from the given
quasi-split hypothesis; affineness is not an additional premise.

The quotient and its map are exactly those constructed in `ClassFunctions`.
There, `ClassFunctions.algebra G` is the equalizer subalgebra of the actual
conjugation pullback and second-factor inclusion in the actual coordinate
algebra of `G`. `ClassFunctions.quotient G` is its relative spectrum.
`ClassFunctions.rho G : G.X ⟶ ClassFunctions.quotient G` is induced by that
subalgebra inclusion and the fixed coordinate presentation of `G`.
Neither a quotient nor a morphism is existentially chosen here. The equality
in the premise is equality of composites with this map. The published
`ClassFunctions.rho_eq_iff` identifies such equality on affine points with
agreement on every regular class function; no separation theorem is assumed.

Write

```lean
b_F = Spec.map (CommRingCat.ofHom (algebraMap K F))
U_F = Over.mk b_F
G_F = (GroupScheme.baseChange b_F).obj G
```

as notation in this explanation. Thus `U_F` is the actual `Spec F` over
`Spec K`, and `y w : U_F ⟶ G.X` are actual `F`-points of `G`.
The inverse of `baseChangeBasePointsEquiv b_F G` sends `w` to its
corresponding rational point of the actual group scheme `G_F` over `Spec F`.
For each test object `Z` over `Spec F`, composing this point with `toUnit Z`
restricts it to a `Z`-point.

The group scheme `S` over `Spec F` is assumed to be a torus, and
`j : S ⟶ G_F` is a group-scheme morphism with `IsClosedSubgroup j`.
The displayed centralizer condition is copied from the parent: every point
`c : Z ⟶ G_F.X` commuting with the restriction of `w` factors through
`j.hom.hom`. It quantifies over every test scheme `Z`, including nonreduced
tests; it is an all-test containment of the centralizer in the closed torus,
not merely a condition on rational points. No chosen split structure or
pinning occurs.

If `y` and `w` have the same image under the fixed `ClassFunctions.rho G`,
the conclusion provides a field `E : Type u`, its field structure and a
`K`-algebra structure, the actual morphism `q : U_E ⟶ U_F` over `Spec K`,
and a point `g : U_E ⟶ G.X`. Here `U_E` is defined by the same formula as
`U_F`. The morphism `q` corresponds to a field embedding `F → E` compatible
with the `K`-structures and witnesses the extension of the field of
definition. Its precompositions `q ≫ y` and `q ≫ w` are the extended points.
The equation retains the parent's orientation:
`g * (q ≫ y) * g⁻¹ = q ≫ w`.
There is no condition on `y` beyond being an `F`-point with the required
quotient image: in particular its semisimplicity, regularity and strong
regularity are not premises.

## Sources, derived provenance and later proof obligations

Provenance: derived.

R. Steinberg, *Regular elements of semi-simple algebraic groups*,
Publications Mathématiques de l'IHÉS 25 (1965), 49–80, registered source
`steinberg-1965-regular-elements-semisimple-groups`, SHA-256
`bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
The registered original PDF was read at the following locations; PDF page
numbers are one-based and equal printed page minus 47. No corresponding
project errata note was found.

- Section 6.1 and its preceding definition, printed p.62/PDF p.15,
  introduce the algebra of regular class functions.
- Sections 6.5–6.6, printed p.63/PDF p.16, give equality of class-function
  values on an element and its semisimple part, and separation of
  semisimple conjugacy classes by regular class functions.
- Section 6.10 and its preceding paragraph, printed p.64/PDF p.17,
  define fibres by agreement on regular class functions and describe the
  fundamental-character map for a simply connected group. Section 6.11
  on the same page describes the semisimple class in each fibre.

The present arbitrary-field proposition for the fixed invariant-ring map is
a derived formulation of this geometric fibre argument, rather than a literal
translation of a single theorem. Steinberg's geometric argument is over an
algebraically closed field. A later Lean proof must justify passage from the
given field to an algebraic closure within universe `u`, transport the actual
quotient-image equality and all-test centralizer hypothesis, and use actual
group points throughout.

The intended argument requires the following substantive results to be proved
or imported as proved results in that later work. Self-commutation puts `w`
in the supplied torus, so it is semisimple after algebraic closure. An actual
multiplicative group-point Jordan decomposition `y = y_s y_u` must be
constructed, with commuting semisimple and unipotent parts. Class functions
must have equal values on `y` and `y_s`; separation must then conjugate `y_s`
to `w`. The conjugated unipotent part centralizes `w` and hence belongs to
the torus by the retained all-test condition; triviality of a unipotent
element in a torus must force that part to be the identity. Each of these
steps, including any necessary field-base-change comparison for the canonical
class-function algebra, is an obligation of the later proof, not a premise
or a result supplied by this statement. Tangent-element Jordan decomposition
alone does not establish the required group-point assertions.

This unit supplies no scheme-theoretic smoothness or reducedness of a fibre,
cross-section, rational lifting, or proof of the parent proposition.
The parent Lean/Markdown pair, every pair it imports, and the
`ClassFunctions` pair are unchanged. Borel–Springer 8.6 and
`QuasiSplitRegularClassRationalStatement` are consumers and are not used
to justify this proposition.
