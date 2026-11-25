# Arithmetic relative cocycle extensions

Let `E` be an actual number field and `K` a field, in independent universes,
with an actual `K`-algebra structure on `E`. This includes number-field
extensions. The acting group is `E ≃ₐ[K] E`,
and the coefficient group is Mathlib's actual
`NumberField.IdeleClassGroup (𝓞 E) E`, with its quotient topology.

`relativeIdeleClassAut` takes the already constructed idele-class transport
along the underlying field automorphism. Its homomorphism laws follow from
the published transport's identity and composition laws.
`relativeIdeleClassAction` is the corresponding explicitly installable
action. On a representative idele, the action is exactly the quotient
class of its arithmetic image.

`relativeGaloisTopology` explicitly installs the discrete topology on the
relative automorphism group. The module proves joint continuity of the
action from continuity for each automorphism and discreteness of the first
factor. The choice is part of the construction; it does not accept or infer
an unrelated topology on that group. Outside the module the topology and
action can be installed with `letI := relativeGaloisTopology K E` and
`letI := relativeIdeleClassAction K E`.

`RelativeIdeleCocycle K E` is a normalized multiplicative two-cocycle for
that exact arithmetic action. Its `Extension` is the constructed group
of pairs, not an arbitrary carrier. The product topology makes it a
topological group, since every cocycle on the discrete acting group is
continuous. The module exposes the injective continuous idele-class
inclusion, surjective continuous automorphism projection, exactness,
continuous section, its factor set, and conjugation by any extension
element. The last formula agrees with the actual arithmetic action,
including the formula on idele representatives. The inclusion is an open
embedding and the projection is an open quotient map. Thus the kernel has
exactly its original idele-class topology and the quotient has exactly the
specified discrete automorphism-group topology.

The construction works for the automorphism group of any such extension.
For a finite Galois extension this is its Galois group. This module neither
selects an arithmetic fundamental cocycle nor identifies its cohomology
class. Consequently it does not yet define a relative Weil group.
Fundamental-class selection, extension transitions, inverse limits,
reciprocity and local-global maps remain separate obligations.

Provenance: this is a derived specialization of the normalized extension
constructed in `Langlands.GroupTheory.CocycleExtension`, using the published
arithmetic transport in
`Langlands.Global.AdelicFunctoriality.Isomorphism`. Its algebraic convention
comes from Artin and Tate, *Class Field Theory* (2009), Chapter XIII
section 1, printed pp.127–128 (PDF pp.136–137), registered as
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
No arithmetic existence theorem from the literature is assumed.
