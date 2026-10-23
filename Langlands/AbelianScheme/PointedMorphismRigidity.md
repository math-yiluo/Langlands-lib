# Pointed-morphism rigidity over an arbitrary base

Original pair: Worker 139, with the target formulation and initial source map
from Worker 133. Provenance correction: Worker 124. Worker 301 discovered the
separated-target discrepancy while preparing the all-field statement;
Worker 143 independently checked the source conventions and supplied the
conditional assembly design used below. Worker 124 reread the retained
original, errata, revision and field-separatedness source for this correction.
The Lean file, declaration, quantified proposition and imports are unchanged.

`Langlands.AbelianScheme.PointedMorphismRigidity` is a proposition definition,
not a proved theorem. It is a stronger internal target inspired by Lan
Corollary 1.3.1.6, not a literal translation of that corollary. For every scheme `S` and actual group schemes `A` and
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
Quasi-separatedness means that the relative diagonal is quasi-compact;
separatedness requires that diagonal to be a closed immersion. The former
is not a substitute for the latter. This target has no
`IsSeparated H.X.hom` premise. It also imposes no global quasi-separatedness
convention on `S`: source conventions are not implicit Lean hypotheses.

The morphism `f : A.X ⟶ H.X` lies in `Over S`, so compatibility with the
structure maps is already part of its type. The equation
`η[A.X] ≫ f = η[H.X]` uses the actual `MonObj` unit maps.
The conclusion `IsMonHom f` requires preservation of the unit and
multiplication in that category. For group objects, a monoid-object
homomorphism also preserves inverses, as expressed by Mathlib's
`GrpObj.inv_comp`; no additional inverse-preservation hypothesis is needed.

## Source scope and provenance correction

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
Harvard PhD dissertation (2008), Corollary 1.3.1.6, printed p.108 (PDF p.148),
is the inspiration for the target. Definition 1.3.1.1, printed p.103
(PDF p.143), gives the geometric abelian-scheme conditions without a
commutativity premise. Theorem 1.3.1.3, printed pp.103–105 (PDF pp.143–145),
is the cited reduction to locally noetherian bases. Corollary 1.3.1.6 does
not repeat the connected-base condition of Corollary 1.3.1.5.

These passages must be read with their conventions and corrections:

- The original thesis, PDF p.36 (printed p.xxxvi), normally uses “scheme”
  for a separated prescheme unless specified otherwise. Its corollary's
  wording “any group scheme” cannot be read independently of that convention.
- The author's errata dated 2021-03-14, p.1, replace this convention with
  quasi-separated schemes and direct readers to the revision. Page 8 corrects
  Theorem 1.3.1.3 to use a directed partially ordered index set. It also says
  that separatedness in Proposition 1.3.1.4 is required only of the target
  structure morphism `q`, and that openness of `p` must be assumed; flatness
  alone does not supply openness in that generality.
- The 2021-03-14 revision, PDF p.26 (printed p.xxvi), records the
  quasi-separated convention. Proposition 1.3.1.4, PDF p.97 (printed p.69),
  explicitly requires `p` open and closed and `q` separated. Corollary
  1.3.1.6, PDF pp.98–99 (printed pp.70–71), explicitly requires the target
  group scheme `G` to be **separated and of finite presentation over `S`**.
  The preceding Corollary 1.3.1.5 has the same separated-target restriction.

Thus the revised corollary does not state the full proposition defined here.
The Lean target deliberately retains every base scheme and only the three
finite-presentation assumptions on `H.X.hom`. Its omission of target
separatedness is a strengthening requiring an independent argument, not a
translation convention or an established consequence in this contribution.
The source's global scheme conventions are not silently imposed on the Lean
quantifiers. No proof of the full target is asserted.

The historical predecessor is Mumford, Fogarty, and Kirwan, *Geometric
Invariant Theory*, third edition (1994), Chapter 6, Corollary 6.4, printed
p.117 (PDF p.130). The chapter's opening, printed p.115 (PDF p.128), assumes
locally noetherian schemes, and Definition 6.1 there specifies a noetherian
base. It does not justify dropping those standing assumptions or the
separatedness boundary identified above. Commutativity is a subsequent
consequence in Lan Corollary 1.3.1.7 and GIT Corollary 6.5, not a premise of
the present target.

## Separate proof obligation and conditional route

The exact arbitrary-base proof obligation is task
`014e89e9-670d-40d8-8e52-26f62f6a0116`. It must prove precisely
`Langlands.AbelianScheme.PointedMorphismRigidity.{u}` without changing this
pair or its imports. This provenance correction supplies no proof or axiom.

Worker 143's shared, unreviewed `PointedRigidityAssembly` draft (revision 4,
checked for this correction on 2026-10-22) uses three published proposition
definitions as explicit hypotheses. Their statement acceptance does not
constitute acceptance of proofs. At this check, the three separate proof
tasks had no proof artifacts:

| Prerequisite declaration | Statement task | Separate proof task |
| --- | --- | --- |
| `Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions` | `5788cea2-b85f-4e15-8b6c-be693b32bc4a` | `f0c89f31-5b1a-47f0-95a9-69ecc4020950` |
| `Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctions` | `df6124a7-20f4-414b-9b59-ef1d58363876` | `90264cc6-8dc5-4f3a-b12c-9dcdd658c6c8` |
| `Langlands.AbelianScheme.FieldPointedMorphismRigidity` | `64d72748-a060-4dd2-aae9-62753e728863` | `d197b3d4-843e-41df-a436-fbcc4c950959` |

The first statement asks for invertibility of the canonical section map
`p.app U` on every open of the base for a smooth proper morphism with
geometrically connected fibres. The second asks for factorization
`g = p ≫ e ≫ g` as scheme morphisms from a section, those canonical
isomorphisms, and equality of the underlying point maps. The third is pointed
rigidity over every field, without an algebraic-closedness assumption.

The conditional design forms the multiplicativity defect on `A ×_S A`.
After pullback to each residue field, the all-field hypothesis makes this
defect the unit. This supplies equality on underlying points. Relative global
functions for `A ×_S A → S` and the factorization hypothesis then supply the
needed equality of scheme morphisms; equality on points alone is insufficient.
The section value of the defect is the unit, so the resulting equality gives
multiplication preservation and, with the given pointedness, `IsMonHom f`.
The global factorization step uses no separatedness assumption on `H`.

Over a field every group scheme is separated: Stacks Project, Lemma 39.7.3,
Tag 047L. Consequently the all-field specialization has a different source
correspondence: target separatedness is automatic there, so Lan's revised
corollary applies to that specialization. This fact does not supply global
separatedness over an arbitrary base. Nor may the field proof use the
arbitrary-base result that the planned assembly is intended to prove.

The reported zero-error, zero-warning compilation of the assembly concerns
only the implication from its three explicit hypotheses. The draft is neither
an independently accepted proof nor an unconditional theorem. It explains the
internal rationale for retaining the stronger target while its prerequisite
proofs and final exact-target proof remain separate obligations.

## Retained sources read for this correction

- `lan-2008-arithmetic-compactifications-pel-thesis`, SHA256
  `c3086d5140bab887e31a508cf4bf8804f092326a35882fc003a3422c4ab65bdd`:
  PDF p.36 (printed p.xxxvi), PDF pp.143–148 (printed pp.103–108).
- `lan-2008-pel-thesis-errata-2021`, SHA256
  `18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`:
  2021-03-14 errata, pp.1 and 8.
- `lan-2008-pel-thesis-revision-2021`, SHA256
  `a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`:
  2021-03-14 revision, PDF p.26 (printed p.xxvi), PDF p.95
  (printed p.67), PDF pp.97–99 (printed pp.69–71), especially
  Corollary 1.3.1.6 on PDF pp.98–99 (printed pp.70–71).
- `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
  SHA256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`:
  GIT Chapter 6, PDF pp.128–130 (printed pp.115–117).
- `stacks-group-scheme-field-separated-047l-2026-10-22`, SHA256
  `ccfc0293f9d03d241ebc1eedf41e90008022156f5dd6d4a8c889821483acb391`:
  retained HTML snapshot, Lemma 39.7.3 (Tag 047L), statement and proof.
