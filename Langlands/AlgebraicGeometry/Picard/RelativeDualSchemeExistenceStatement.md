# Existence of the universal Picard-zero family over a quasi-separated base

`Langlands.AbelianScheme.RelativeDualSchemeExistenceStatement` asserts
`HasDualScheme A` for every `S : Scheme.{u}` with
`[QuasiSeparatedSpace S]` and every `A : AbelianScheme S`.
It is a proposition definition, not a proof. No noetherian, reducedness,
quasi-compactness or projectivity hypothesis is added.

The conclusion uses the existing existence predicate without changing it.
There must be an actual parameter scheme `P` over `S` and an actual
rigidified line bundle `L` on `P ×_S A` satisfying
`IsUniversalPicardZero A L`. In particular, `L` satisfies the geometric
Picard-zero condition, and every rigidified Picard-zero class on
`T ×_S A` is the actual pullback of `L` along exactly one map `T → P`.
The quantifier ranges over all test schemes `T` in the fixed universe,
including nonreduced and non-quasi-separated schemes. Uniqueness concerns
the parameter map, not a choice of bundle isomorphism.

The lemma `RelativeDualSchemeExistenceStatement.field` specializes a proof
of this proposition to the existing `FieldDualSchemeExistenceStatement`.
Its implemented proof takes `S = Spec k`; that scheme is affine and hence
quasi-separated. It supplies no unconditional field or relative existence
proof.

## Original source

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
Harvard thesis, revision of March 14, 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`:

- The conventions on printed p.xxvi (PDF p.26) restrict schemes to
  quasi-separated preschemes.
- Definition 1.3.1.1, printed p.67 (PDF p.95), defines abelian schemes
  by properness, smoothness and geometrically connected fibres.
- Definition 1.3.2.1 and Lemma 1.3.2.2, printed pp.73–74
  (PDF pp.101–102), describe the relative Picard-zero functor and its
  rigidified representatives using fibrewise algebraic equivalence to zero.
- Theorem 1.3.2.3, printed p.74 (PDF p.102), represents that rigidified
  Picard-zero functor by an abelian scheme. Definition 1.3.2.5 on the same
  page gives the universal rigidified Poincare bundle.

The author's March 14, 2021 errata, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were read at pp.1 and 8–9. Page 1 changes the earlier separated-scheme
convention to quasi-separatedness and recommends using the revision.
Page 8 corrects the base-pulled line bundles in Definition 1.3.2.1 to
come from `T`; the revised text incorporates this correction.
The numbering cited here is that of the revision.

Remark 1.3.2.4 distinguishes the stronger representability theorem from
the locally projective route. This target uses that stronger theorem
within its quasi-separated-base convention. It does not infer an
arbitrary-base theorem from the locally noetherian/projective statements
in GIT, Chapter 6.

## Derivation required for the exact target

This is a derived target, because the Library uses a different explicit
fibre predicate and a larger test category than the source convention.
Both comparisons remain proof obligations.

For the fibre predicate, the Library requires translation invariance
after passage to every algebraically closed field-valued point of `T`.
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
draft, Corollary (7.22), printed p.106 (PDF p.110), identifies field
`Pic⁰` with the kernel of the associated line-bundle homomorphism. This
source is registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
A proof must implement the comparison with fibrewise algebraic
equivalence, the identification of ordinary line bundles and their
rigidifications, and the swap from the source's `A ×_S T` convention to
the Library's `T ×_S A`. A comparison only of geometric point sets
does not establish the required universal property for families.

For an arbitrary test scheme `T`, restrict an actual rigidified family
to an affine open cover. The source representability theorem can then
classify each restriction after the preceding comparisons. Each overlap
is an open subscheme of an affine member of the cover, so it is separated
and hence quasi-separated, although it need not be quasi-compact.
The source's uniqueness can therefore be applied on these overlaps,
after the preceding comparisons, to show that the parameter maps agree.
They can then be glued to a map on `T`. To recover the original
family, one must also justify compatible gluing of the local
rigidification-preserving bundle isomorphisms, or equivalently establish
the corresponding sheaf property for the rigidified class functor.
Rigidity of automorphisms for abelian schemes is a possible ingredient;
equality of class sets on geometric fibres alone is insufficient.
This must include nonreduced affine tests. The same local argument must
prove uniqueness of the global parameter map.

These are requirements on a future proof, not results proved by this
file. Retaining quasi-separatedness of `S` avoids asserting the source
theorem outside its base convention even though the resulting
universal property is required on all test schemes.

## Boundary

The target supplies existence of the actual universal family only.
The geometry of the chosen parameter scheme, its constructed group
law, dual homomorphisms, polarizations and base-change compatibility
are handled by separate declarations. It introduces no new axiom
and supplies no arbitrary representability data as a replacement for
the geometric predicate. A separate proof task must establish the
exact proposition after publication. The conditional field
specialization does not complete or restart the existing field-existence
proof task.
