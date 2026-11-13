# Conditional assembly of division-case CM representability

Worker 3269. This module is an internal derivation from imported Library
constructions. It does not construct a moduli scheme and does not prove
`DivisionCMRepresentabilityStatement`. It rewrites the exact consequent
`CMRepresentabilityStatement` in a form that a quasi-projective
construction can produce directly, and it states exactly which extra
premises the rewriting needs.

## Projective-space lemmas

These lemmas live in namespace `Langlands.AlgebraicGeometry`.

- `IsHProjective.of_isImmersion_of_isProper`: let `p : X ⟶ Spec R` be
  proper and let `i : X ⟶ ℙ^m_R` be an immersion over `Spec R`. Then `p`
  is `IsHProjective`, meaning `i` is in fact a closed immersion. Proof:
  `i ≫ (ℙ^m_R ⟶ Spec R) = p` is universally closed, and projective space
  is separated. So Mathlib's `UniversallyClosed.of_comp_of_isSeparated`
  makes `i` universally closed, and its range is closed. A preimmersion
  with closed range is a closed immersion.
- `IsHProjective.exists_isImmersion`: conversely, an `IsHProjective`
  morphism has an immersion into some `ℙ^m_R` over `Spec R`. This is
  just its closed immersion. Properness is the existing
  `IsHProjective.isProper`.

## Restricted functor of points

This and the remaining declarations live in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. They carry the same
variables and named prerequisite hypotheses as
`HarrisTaylorCMRepresentabilityStatement`.

`admissibleTestPoints X` is defined for any `X : Over (Spec F)`. It is
the functor `T ↦ ULift (T.obj ⟶ X)` on the opposite of the existing
componentwise admissible test category `ComponentwiseAdmissibleCMBaseCategory`.
In Lean this is the inclusion of the full subcategory composed with
`uliftYoneda.{1}.obj X`. `X` itself need not be admissible.

`uliftYonedaIsoAdmissibleTestPoints X` covers the case where `X` is
already an admissible object. It identifies the lifted Yoneda presheaf
of `X` inside the full subcategory with `admissibleTestPoints X.obj`.
The identification comes from full faithfulness of the inclusion. It is
natural by `rfl`.

## Geometric representation data

`CMLevelGeometricRepresentation U` is a structure for a small level
`U : SmallCMLevel D`. It consists of:

- an arbitrary scheme `scheme : Over (Spec F)`;
- `Smooth scheme.hom` and `IsProper scheme.hom`;
- a natural number `dim` and an immersion
  `embedding : scheme.left ⟶ ℙ^dim_F` with
  `embedding ≫ projectiveSpaceToSpec F dim = scheme.hom`;
- a natural isomorphism
  `represents : admissibleTestPoints scheme ≅ (smallLevelClassPresheafTower …).obj U`.
  The target is the existing normalized class presheaf. It is not
  modified.

Unlike the existing `CMLevelRepresentation`, the structure contains no
admissibility of the representing scheme. It also asks only for an
immersion into projective space, not a closed one.
`CMGeometricRepresentabilityStatement` says that such data exists at
every small level.

## Comparison with the exact target

- `CMLevelRepresentation.toGeometric` sends an exact representation to
  geometric data with the same underlying scheme. It forgets
  admissibility, reads properness and an immersion off `IsHProjective`,
  and composes the representing isomorphism with
  `uliftYonedaIsoAdmissibleTestPoints`. It needs no extra premises.
- `CMLevelGeometricRepresentation.toRepresentation` goes the other way.
  It takes the two Library propositions
  `RelativeDualSchemeExistenceStatement.{0}` and
  `RelativeDualSchemeGeometryStatement.{0}` as explicit hypotheses. With
  them, the published `smoothComponentwiseAdmissibleCMBase_of_relativeDual`
  makes the smooth scheme a componentwise admissible object.
  `IsHProjective.of_isImmersion_of_isProper` supplies projectivity. The
  representing isomorphism is transported along
  `uliftYonedaIsoAdmissibleTestPoints`.
- `cmLevelRepresentabilityStatement_iff_geometric` holds at each level,
  and `cmRepresentabilityStatement_iff_geometric` holds at all small
  levels. Under the two relative dual hypotheses, each says that the
  exact `CMLevelRepresentabilityStatement` (resp.
  `CMRepresentabilityStatement`) is equivalent to the existence of
  geometric representation data.
- `divisionCMRepresentabilityStatement_of_geometric` derives the exact
  `DivisionCMRepresentabilityStatement` from three premises: the two
  relative dual statements, and the implication
  `D.IsDivision → CMGeometricRepresentabilityStatement …`.

## Scope and provenance

The provenance is internal. Every step assembles imported Library results
(`smoothComponentwiseAdmissibleCMBase_of_relativeDual`,
`IsHProjective.isProper`) and Mathlib facts about immersions, separated
and universally closed morphisms, and full subcategories. No literature
definition is transcribed. The new structure only repackages the fields
of the existing `CMLevelRepresentation`: it drops admissibility and
weakens a closed immersion to an immersion plus properness.

The two relative dual statements are unproved Library propositions.
Separate tasks own them, and this module proves neither. They are
hypotheses of this conditional assembly only. They are not hypotheses of
the published target, which this module does not prove. The premise
`CMGeometricRepresentabilityStatement` is the actual construction of
smooth proper quasi-projective representing schemes. It is also
unproved here. The exact normalized CM presheaf, the published target
statement and every imported Lean/Markdown pair stay unchanged.
