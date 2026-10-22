# Pointed-morphism rigidity over an arbitrary field

Authors: Worker 143 proposed this formulation and the initial source map in
the task specification. Worker 301 checked the originals, errata, and revision,
and implemented this pair.

`Langlands.AbelianScheme.FieldPointedMorphismRigidity` is a proposition
definition, not a proved theorem. It covers every field `K`. Over `Spec K`,
it states that a morphism preserving the identity between actual group
schemes `A` and `H` is a group-scheme homomorphism. The hypotheses are that
`A` is smooth and proper with geometrically connected fibres and `H` is of
finite presentation.

## Quantifiers and hypotheses

- The universe parameter `u` is arbitrary. The field is any `K : Type u` with
  `[Field K]`. There is no algebraic-closedness, perfectness, characteristic,
  or finiteness restriction on `K`.
- The base is `Spec (CommRingCat.of K)`, a scheme in universe `u`. Both `A`
  and `H` have type `GroupScheme (Spec (CommRingCat.of K))`. This is
  `Grp (Over (Spec (CommRingCat.of K)))`, the category of group objects in
  schemes over `Spec K`. The unit `η` and multiplication are the actual
  `MonObj` structure maps of these objects.
- The source hypothesis is the unchanged `GroupScheme.IsAbelian A` from
  `Basic`. It is the conjunction of `Smooth A.X.hom`, `IsProper A.X.hom`, and
  `GeometricallyConnected A.X.hom`. Neither `A` nor `H` is assumed
  commutative. In particular, the source is not the bundle `AbelianScheme`,
  which separately requires commutativity.
- Finite presentation of the target structure morphism `H.X.hom` consists of
  three hypotheses: `LocallyOfFinitePresentation`, `QuasiCompact`, and
  `QuasiSeparated`. This follows Mathlib's
  `AlgebraicGeometry.Morphisms.FinitePresentation` convention. They concern
  `H` over `Spec K`, not the morphism being tested.
- The morphism `f : A.X ⟶ H.X` lies in `Over (Spec (CommRingCat.of K))`, so
  compatibility with the structure maps is part of its type. No homomorphism
  structure on `f` is supplied. The only hypothesis on `f` is the equation
  `η[A.X] ≫ f = η[H.X]` of unit maps.
- The conclusion `IsMonHom f` asserts that `f` preserves the unit and the
  multiplication. For group objects, a monoid-object homomorphism also
  preserves inverses, as Mathlib's `GrpObj.inv_comp` expresses. No separate
  inverse-preservation clause is needed.

The Lean body is the body of the published arbitrary-base statement
`Langlands.AbelianScheme.PointedMorphismRigidity`, with its scheme `S`
replaced by `Spec (CommRingCat.of K)`. Every hypothesis is otherwise
unchanged. Thus the parent statement implies this one by instantiation. This
module, however, neither states nor proves that implication.

## Original sources and correspondence

The original statement is Corollary 1.3.1.6 in Kai-Wen Lan, *Arithmetic
compactifications of PEL-type Shimura varieties*, Harvard PhD dissertation
(2008). It is on printed p.108 (PDF p.148). For an abelian scheme `A` and a
group scheme `G` of finite presentation over a base scheme `S`, it states
that an `S`-morphism taking the identity to the identity is a homomorphism.
This target takes `S = Spec K`. The other cited parts of the dissertation are
as follows.

- Definition 1.3.1.1 is on printed p.103 (PDF p.143). It defines an abelian
  scheme as a proper smooth group scheme with geometrically connected fibres,
  without commutativity. This is the unchanged `GroupScheme.IsAbelian`.
- Rigidity Proposition 1.3.1.4 and Corollary 1.3.1.5 are on printed
  pp.105–108 (PDF pp.145–148). They are the steps of the source proof. The
  connected-base hypothesis of Corollary 1.3.1.5 holds for `Spec K`.
- The dissertation's conventions are on printed p.xxxvi (PDF p.36). There,
  "scheme" means a separated prescheme. Hence the group scheme `G` in
  Corollary 1.3.1.6 is tacitly separated.

The author's errata are dated March 14, 2021. They replace that convention by
quasi-separatedness (p.1). They also state that separatedness is assumed only
for the target morphism in Proposition 1.3.1.4 (p.8). The author's revision
of the same date keeps the numbering. Its Corollary 1.3.1.6 is on printed
pp.70–71 (PDF pp.98–99), and it assumes that `G` is a *separated* group scheme
of finite presentation over `S`. Corollary 1.3.1.5 is on printed p.70 (PDF
p.98), Proposition 1.3.1.4 on printed p.69 (PDF p.97), and Definition 1.3.1.1
on printed p.67 (PDF p.95). The revision's conventions on printed p.xxvi (PDF
p.26) take schemes to be quasi-separated preschemes.

All versions therefore assume that the target is separated. The Lean
statement has no separatedness hypothesis on `H`. Over a field this is no
change of scope: every group scheme over a field is separated, by Stacks
Project Lemma 39.7.3 (Tag 047L). In particular, the hypothesis
`QuasiSeparated H.X.hom` is redundant over `Spec K`, since a separated
morphism is quasi-separated. It is retained to match the parent statement's
finite-presentation convention, and it does not restrict the target. The
source `A` is separated because it is proper.

The predecessor is Mumford, Fogarty, and Kirwan, *Geometric Invariant Theory*,
third edition (1994), Chapter 6, Corollary 6.4, printed p.117 (PDF p.130). Its
group scheme `G` need not be of finite presentation. The chapter opening on
printed p.115 (PDF p.128) assumes all preschemes to be locally noetherian and
to be schemes; in this older terminology, a scheme is a separated prescheme.
Definition 6.1, also on p.115, defines abelian schemes over a noetherian base
by smoothness, properness, and connected geometric fibres, again without
commutativity. These standing hypotheses hold in the present target.
`Spec K` is noetherian. `A` is of finite type over `K`, hence noetherian. `H`
is locally of finite type over `K`, hence locally noetherian. `H` is separated
by Tag 047L. Rigidity Proposition 6.1 and Corollaries 6.2–6.3, printed
pp.115–117 (PDF pp.128–130), are the steps of that proof.

The provenance is a direct specialization of Lan's Corollary 1.3.1.6 to
`S = Spec K`, with the separatedness discrepancy resolved by Tag 047L. The
target also lies within the scope of GIT Corollary 6.4. Commutativity of `A`
is a later consequence, Lan Corollary 1.3.1.7 and GIT Corollary 6.5. It is
not a premise here.

## Scope and proof boundary

This module only states the proposition. It adds no proof, axiom, or
auxiliary hypothesis. A separate exact-target proof task must prove it for
every field. That proof must not use a proof of the arbitrary-base
`PointedMorphismRigidity`, whose planned proof relies on this field case.
An intermediate result over algebraically closed fields would need a
separately proved descent to the present all-field statement.

Mathlib's `AlgebraicGeometry/Group/Abelian.lean` proves commutativity of
suitable proper group schemes over fields. It is not this pointed-morphism
rigidity statement and is not used here.

Sources read directly:

- `lan-2008-arithmetic-compactifications-pel-thesis`, SHA256
  `c3086d5140bab887e31a508cf4bf8804f092326a35882fc003a3422c4ab65bdd`,
  PDF pp.36 and 143–148.
- `lan-2008-pel-thesis-errata-2021`, SHA256
  `18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
  pp.1 and 8.
- `lan-2008-pel-thesis-revision-2021`, SHA256
  `a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`,
  PDF pp.26 and 95–99.
- `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`
  (GIT), SHA256
  `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`,
  PDF pp.128–130.
- `stacks-group-scheme-field-separated-047l-2026-10-22`, SHA256
  `ccfc0293f9d03d241ebc1eedf41e90008022156f5dd6d4a8c889821483acb391`,
  Lemma 39.7.3 (Tag 047L).
