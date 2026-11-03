# Simple connectedness forces integral coroot generation

`SplitSimplyConnectedCorootSpanStatement` states the necessity direction of the
integral coroot criterion for a supplied finite reduced root datum. It is a
`Prop`-valued definition and is not a proof.

For an arbitrary field `k : Type u`, let `G` be algebraically simply connected
in the Library's sense. Thus `G` is semisimple and every incoming central
isogeny from a semisimple group is an isomorphism. Let `i : T.toGrp ⟶ G`
be a maximal torus with `T` split, and let `P` be a root datum of `i` on
the actual integral character and cocharacter lattices of `T`. If its root
index type is finite and `P` is reduced, the proposition asserts
`P.corootSpan ℤ = ⊤`: the integral coroots generate the full cocharacter
lattice. This is stronger than generation after tensoring with `ℚ`.

The instance needed by `IsRootDatumOf` is provided by the semisimplicity
component of `hG`, via connected reductivity and affineness.
`IsRootDatumOf` retains its published meaning: the pairing is the actual
lattice pairing, the roots are exactly the actual adjoint roots, and
normalizing points realize the reflections. The finiteness of the root index type and reducedness
premises are explicit; a use of the public `RootDatumExistenceStatement`
supplies both. There is no restriction on characteristic or perfection, and
no algebraic closure or extension field is assumed. The field, group schemes,
lattices and root index type all retain arbitrary universe `u`.

This is an internal formulation of the missing necessity input for the
field-extension proof. Its provenance is the published `IsSimplyConnected`
and `IsRootDatumOf` predicates and Mathlib's integral `corootSpan`, rather than
a new definition of simple connectedness. It complements
`SplitCorootSpanSimplyConnectedStatement`, the separately stated sufficiency
direction. A planned proof constructs the root datum on the coroot lattice
using `Langlands.LinearAlgebra.SimplyConnectedRootDatum`, realizes it by a
split reductive group and an incoming central isogeny, and then uses simple
connectedness and the actual torus/lattice comparison to show that the
coroot-lattice inclusion is surjective. That route still requires the split
Existence and central Isogeny Theorems and the root-datum criterion for
semisimplicity. This file assumes none of those results and proves no
necessity, sufficiency, cover-existence or field-extension theorem.
