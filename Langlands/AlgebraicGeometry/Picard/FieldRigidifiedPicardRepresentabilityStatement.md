# Full rigidified Picard representability over a field

`Langlands.AbelianScheme.FieldRigidifiedPicardRepresentabilityStatement.{u}`
is a proposition definition. For every field `k : Type u` and every
`A : AbelianScheme (Spec k)`, it asserts the existence of an actual
`P : Over (Spec k)` and an actual `L : RigidifiedFamily A P` such that
`P.hom` is locally of finite type and
`RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
(unitSection_comp A) L` holds.

Here `L` is a line bundle on `P ×_k A`, rigidified along the section
induced by the unit of `A`. For every test `k`-scheme `T`, the specified
`classifyingMap` sends `h : T ⟶ P` to the rigidified isomorphism class of
the canonical relative pullback of `L` along `h`. `IsUniversal` requires
this map to be bijective onto **all** rigidified line-bundle classes on
`T ×_k A`. Equivalently, every actual rigidified family is isomorphic to
such a pullback for a unique `h`. The uniqueness concerns `h`, not the
choice of a bundle isomorphism.

The test schemes include nonreduced and non-quasi-compact schemes; they
are not restricted to field-valued points. The field has no perfectness,
algebraic-closedness, characteristic, or dimension restriction. The
definition is polymorphic in `u`, with the field, base, parameter scheme
and test schemes in the existing `Scheme.{u}` convention. The class
quotients use the value universe already supplied by the imported
definitions.

## Original source and scope

The source is B. Edixhoven, G. van der Geer and B. Moonen,
*Abelian Varieties*, preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

Chapter VI (6.2), printed pp.88–89 (PDF pp.92–93), defines the rigidified
functor and its universal Poincaré bundle using actual pullback over
every test scheme. Under the hypotheses listed there, it identifies
that functor with the fppf Picard sheaf. The Library uses the symmetric
product `T ×_k A` in place of the source's `A ×_k T` and the same
rigidification direction, from the structure sheaf to the pullback
along the section.

Paragraph (6.3)(iii), printed p.89 (PDF p.93), explicitly states that the
Picard scheme of a proper scheme over a field is separated and locally
of finite type over that field, citing Murre and Oort. The present
statement retains the local finite type conclusion needed here; it
does not separately assert separatedness. Local finite type permits
infinitely many components: neither finite type nor quasi-compactness
of the full Picard scheme is required.

Chapter VI §3, printed p.95 (PDF p.99), takes an abelian variety over
an arbitrary field and admits full Picard representability from the
general theory. It explicitly identifies this Picard scheme with the
functor rigidified along zero and supplies its Poincaré bundle. This is
the representability input isolated by the Lean statement.

The later Theorem (6.18) and Definition (6.19), printed p.96
(PDF p.100), concern the identity component and the dual abelian
variety. The present target imposes no `IsPicardZeroFamily` condition,
does not identify the geometric translation-invariance predicate with
that component, and does not assert existence of a dual scheme for
that predicate. Those comparison and restriction arguments belong to
the separate dual-existence proof.

## Formalization boundary

This is a derived packaging of the cited representability and
rigidification statements using the existing actual bundle and pullback
definitions. The imported `AbelianScheme` already supplies a smooth
proper commutative group scheme with geometrically connected fibres.
Projectivity is not an input hypothesis. If a proof uses a projective
representability theorem, it must establish projectivity; similarly,
the source's universal structure-sheaf pushforward condition and the
comparison with the fppf Picard sheaf must be proved if used. None is
inserted as a hidden assumption or as an arbitrary classifier.

The file supplies no proof or axiom. Its exact proof obligation includes
existence of both `P` and `L`, local finite type of `P.hom`, and
bijectivity of the specified canonical pullback maps on all test
schemes. Proving ambient representability must not assume the parent's
dual-scheme existence conclusion.
