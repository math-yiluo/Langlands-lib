# Canonical heads and socles

Author: Worker 23. Generalization of the head to an arbitrary field: Worker 375.

The published relations `IsIrreducibleHead ρ π` and `IsIrreducibleSocle ρ π`
(`Classification/ConstituentRelations`) say that `π` is the unique irreducible
quotient, or the unique irreducible subrepresentation, of `ρ`. They make no
choice of representative. This module adds one actual representation for each:
the head of `ρ` and the socle of `ρ`. Both are defined for every `ρ`, with no
choice and no existence hypothesis. Their characterizing theorems prove the
following. When `ρ` has an irreducible head or socle at all, the canonical object
is one, and every irreducible head or socle of `ρ` is equivalent to it. The module
does not prove that any representation has an irreducible head or socle.

Later modules use these objects to name the representations that the literature
calls "the unique irreducible quotient" or "the unique irreducible
subrepresentation" of a standard or induced representation. Examples are
Zelevinsky's `⟨Δ⟩` and `⟨Δ⟩^t` and the Langlands quotient
`J(π_1, …, π_r)`. The sources and conventions for those objects are recorded with
their relations in `Classification/Segments` and `Classification/LanglandsData`.
The present module is purely algebraic and makes no claim from the literature.

## Setting

The definitions live in namespace `Langlands.Classification`. `G` is any group,
and `V : Type uV`. In the head part, `ρ` is a representation of `G` on `V` over
an arbitrary field `k : Type uk`, and the irreducible targets `π` tested there are
representations over the same field `k`. The irreducible-head characterization and
the socle part stay complex: there `ρ` is a complex linear representation, because
the published relations `IsIrreducibleHead` and `IsIrreducibleSocle` are stated
for complex representations. For `k = ℂ` the head declarations specialize to the
complex ones, with the same names and argument order; `k` is found from `ρ`. No
topology, smoothness, admissibility or finite dimension is assumed. Like the
published relations, every quotient or subrepresentation tested below has its
carrier in the universe `uV` of `V`.

## Head

The declarations of this section hold over an arbitrary field `k`.

- `headKernel ρ` is the subrepresentation of the vectors `v` with `q v = 0` for
  every surjective intertwining map `q : ρ → π` onto an irreducible
  representation `π` over `k` with carrier in `Type uV`. It is the intersection
  of the kernels of all irreducible quotient maps (`mem_headKernel_iff`).
  `headKernel_le_ker` says that it lies in each such kernel.
- `head ρ` is the actual quotient representation of `ρ` on
  `V ⧸ headKernel ρ`. `toHead ρ` is the canonical quotient map. It is surjective
  (`toHead_surjective`), its kernel is the head kernel (`ker_toHead`), and
  `toHead_apply` evaluates it.
- `headEquivOfSurjective q hq hK` is the equivalence `head ρ ≃ π` induced by a
  surjective intertwining map `q : ρ → π`, with `π` over `k` and its carrier in
  any universe, whose kernel is the head kernel. It sends `toHead ρ v` to `q v`
  (`headEquivOfSurjective_apply`).

The module `Classification/Cosocle` proves the further laws of the head: its
kernel is the intersection of the maximal subrepresentations and corresponds to
the Jacobson radical over the group algebra, and for finite-length `ρ` the head
is the cosocle (maximal semisimple quotient) of `ρ`.

## Irreducible heads

From here on `ρ` and `π` are complex representations.

- `HasIrreducibleHead ρ` says that `ρ` has an irreducible head `π` with carrier in
  `Type uV`, in the sense of `IsIrreducibleHead`.

Characterization, for `h : IsIrreducibleHead ρ π`:

- `h.headKernel_eq` shows that the head kernel equals the kernel of every
  surjective intertwining map from `ρ` onto an irreducible representation with
  carrier in `Type uV`.
- `h.nonempty_headEquiv` gives an equivalence `head ρ ≃ π`.
- `h.isIrreducibleHead_head` shows that `head ρ` is itself an irreducible head of
  `ρ`, with `toHead ρ` as the quotient map.
- `isIrreducibleHead_head_iff ρ` states that
  `IsIrreducibleHead ρ (head ρ) ↔ HasIrreducibleHead ρ`.

## Socle

As in the previous section, `ρ` and `π` are complex representations.

- `irreducibleImages ρ` is the set of the images of the injective intertwining
  maps `j : π → ρ` from irreducible representations `π` with carrier in
  `Type uV`.
- `socle ρ` is the subrepresentation spanned by these images, their supremum as
  submodules. `range_le_socle` says that it contains each of them.
- `socleRepresentation ρ` is the actual restriction of `ρ` to the socle.
  `ofSocle ρ` is the canonical inclusion. It is injective (`ofSocle_injective`),
  its image is the socle (`range_ofSocle`), and `ofSocle_apply` evaluates it.
- `HasIrreducibleSocle ρ` says that `ρ` has an irreducible socle `π` with carrier
  in `Type uV`, in the sense of `IsIrreducibleSocle`.
- `socleEquivOfInjective j hj hS` is the equivalence `π ≃ socleRepresentation ρ`
  induced by an injective intertwining map `j : π → ρ` whose image is the socle.
  Composed with the inclusion, it is `j` (`ofSocle_socleEquivOfInjective`).

Characterization, for `h : IsIrreducibleSocle ρ π`:

- `h.socle_eq` shows that the socle equals the image of every injective
  intertwining map into `ρ` from an irreducible representation with carrier in
  `Type uV`.
- `h.nonempty_socleEquiv` gives an equivalence `π ≃ socleRepresentation ρ`.
- `h.isIrreducibleSocle_socleRepresentation` shows that the socle representation
  is itself an irreducible socle of `ρ`, with `ofSocle ρ` as the embedding.
- `isIrreducibleSocle_socleRepresentation_iff ρ` states that
  `IsIrreducibleSocle ρ (socleRepresentation ρ) ↔ HasIrreducibleSocle ρ`.

## Smooth representations

The definitions live in namespace `Langlands.SmoothRep`. `G` is a topological
group. The constructions use the published smooth subquotients of
`Category/Subquotients`.

For an arbitrary field `k : Type uk` and an object
`A : SmoothRep.{uk, uG, uV} k G` of the published category of smooth
representations over `k`:

- `A.headQuotient` is the smooth quotient of `A` by the head kernel of its
  underlying representation, again an object of `SmoothRep.{uk, uG, uV} k G`.
  Its representation is `head A.representation` (`headQuotient_representation`,
  by `rfl`). `A.toHeadQuotient` is the quotient morphism, and it is surjective
  (`toHeadQuotient_surjective`).

For an object `A : SmoothRep.{0, uG, uV} ℂ G` of the category of complex smooth
representations:

- `A.socleSubrepresentation` is the smooth subrepresentation of `A` on the socle.
  Its representation is `socleRepresentation A.representation`
  (`socleSubrepresentation_representation`, by `rfl`).
  `A.ofSocleSubrepresentation` is the inclusion morphism, and it is injective
  (`ofSocleSubrepresentation_injective`).
- `isIrreducibleHead_headQuotient_iff` and
  `isIrreducibleSocle_socleSubrepresentation_iff` restate the two `iff`
  characterizations for these objects.
- `nonempty_iso_headQuotient` gives an isomorphism `B ≅ A.headQuotient` in the
  smooth category for every smooth `B` whose representation is an irreducible head
  of `A`. Dually, `nonempty_iso_socleSubrepresentation` gives
  `B ≅ A.socleSubrepresentation` for every irreducible socle `B`.

## Remarks on the definitions

Every proper subrepresentation `M` of `ρ` with irreducible quotient is the kernel
of the quotient map `V → V ⧸ M`, whose carrier lies in `Type uV`. Therefore
`headKernel ρ` is the intersection of the maximal subrepresentations, the radical
of `ρ`. This identification is not proved here; it is proved, over an arbitrary
field, in `Classification/Cosocle` (`headKernel_eq_sInf_isCoatom`, and
`asSubmodule_headKernel` for the Jacobson radical of `ρ.asModule`). Likewise,
every irreducible subrepresentation is the image of its own inclusion, so
`socle ρ` is the sum of the irreducible subrepresentations, the usual socle. This
identification is explanatory only and is not proved here.

Without an irreducible head, `head ρ` may be reducible or zero. For example, it is
zero when `ρ` has no irreducible quotient. Similarly, `socleRepresentation ρ` may be
reducible or zero. The characterization theorems above only describe these
objects when the corresponding relation holds. For `ρ` of finite length over the
group algebra, `Classification/Cosocle` proves that `head ρ` is semisimple.

The universe restriction matches the published relations. `head ρ` and
`socleRepresentation ρ` have carriers in `Type uV`, so they are admissible
witnesses of `HasIrreducibleHead` and `HasIrreducibleSocle`.

The proofs that `head ρ` and `socleRepresentation ρ` are irreducible transport
irreducibility along the equivalences above. They use the published lemma
`Weil.IsomorphismInvariance.irreducible_iff`, which holds for representations of
any group.
