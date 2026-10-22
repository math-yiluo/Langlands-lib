# Pointed-morphism rigidity over an arbitrary base

Author: Worker 139. Worker 133 supplied the target formulation and initial
source map in the task specification; Worker 139 independently checked the
originals and implemented this pair.

`Langlands.AbelianScheme.PointedMorphismRigidity` is a proposition definition,
not a proved theorem. For every scheme `S` and actual group schemes `A` and
`H` over `S`, it states that an `S`-morphism from `A` to `H` preserving the
identity is a group-scheme homomorphism, provided `A` is smooth and proper
over `S` with geometrically connected fibres and `H` is of finite presentation
over `S`.

The source hypothesis is the unchanged `GroupScheme.IsAbelian A` from
`Basic`: the conjunction of `Smooth A.X.hom`, `IsProper A.X.hom`, and
`GeometricallyConnected A.X.hom`. Both objects have type `GroupScheme S`,
the category of group objects in `Over S`. Neither object is assumed
commutative. In particular, the source is not the bundle `AbelianScheme S`,
which separately requires commutativity. The declaration has an arbitrary
universe parameter `u`, covering every universe of the current `GroupScheme`
definition. It imposes no noetherian, reducedness, field, connected-base, or
characteristic restriction.

Finite presentation of the target structure morphism is expressed by the
three hypotheses `LocallyOfFinitePresentation H.X.hom`,
`QuasiCompact H.X.hom`, and `QuasiSeparated H.X.hom`, following Mathlib's
`AlgebraicGeometry.Morphisms.FinitePresentation` convention. These properties
are imposed on `H` over `S`, not on the morphism being tested.

The morphism `f : A.X ⟶ H.X` lies in `Over S`, so compatibility with the
structure maps is already part of its type. The equation
`η[A.X] ≫ f = η[H.X]` uses the actual `MonObj` unit maps.
The conclusion `IsMonHom f` requires preservation of the unit and
multiplication in that category. For group objects, a monoid-object
homomorphism also preserves inverses, as expressed by Mathlib's
`GrpObj.inv_comp`; no additional inverse-preservation hypothesis is needed.

The original statement is Kai-Wen Lan, *Arithmetic compactifications of
PEL-type Shimura varieties*, Harvard PhD dissertation (2008),
Corollary 1.3.1.6, printed p.108 (PDF p.148). Its source notion of an abelian
scheme is Definition 1.3.1.1, printed p.103 (PDF p.143), which requires
properness, smoothness, and geometrically connected fibres of a group scheme
without assuming commutativity. Corollary 1.3.1.6 explicitly assumes finite
presentation of the target and permits an arbitrary base scheme. Its proof
invokes the reduction to the locally noetherian case in Theorem 1.3.1.3,
printed pp.103–105 (PDF pp.143–145). The intervening rigidity discussion and
Corollary 1.3.1.5 were also read. The connected-base hypothesis in that
intermediate corollary is absent from Corollary 1.3.1.6.

The cited predecessor is Mumford, Fogarty, and Kirwan, *Geometric Invariant
Theory*, third edition (1994), Chapter 6, Corollary 6.4, printed p.117
(PDF p.130). Chapter 6 explicitly assumes locally noetherian schemes in
its opening on printed p.115 (PDF p.128), and Definition 6.1 there specifies
a noetherian base. Thus the arbitrary-base scope here comes from Lan's
corollary and reduction, not from removing GIT's standing hypotheses.
Commutativity is a subsequent consequence in Lan Corollary 1.3.1.7 and
GIT Corollary 6.5; it is not a premise of the present statement.

This module translates the cited statement into the existing group-object
interface and adds no proof or axiom. A separate exact-target proof task
must retain its complete arbitrary-base scope and establish the substantial
prerequisites as separately published statements before proving them.

Sources read directly:

- Registered source `lan-2008-arithmetic-compactifications-pel-thesis`,
  SHA256 `c3086d5140bab887e31a508cf4bf8804f092326a35882fc003a3422c4ab65bdd`,
  PDF pp.143–148 (printed pp.103–108).
- Registered source
  `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
  SHA256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`,
  PDF pp.128–130 (printed pp.115–117).

No source-specific project errata note was present when this statement was
prepared.
