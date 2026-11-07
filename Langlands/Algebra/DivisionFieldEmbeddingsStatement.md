# Field embeddings in a central division algebra are conjugate

`Langlands.CentralDivision.FieldEmbeddingsConjugateStatement` states the
field-embedding case of the Skolem–Noether theorem.

Let `K : Type uK` be a field, `D : Type uD` a division ring with
`[Algebra K D] [FiniteDimensional K D] [Algebra.IsCentral K D]`, and
`L : Type uL` a field with
`[Algebra K L] [FiniteDimensional K L]`. For any two actual
`K`-algebra maps `f g : L →ₐ[K] D`, the statement requires an actual unit
`u : Dˣ` such that

`f a = (u : D) * g a * (u⁻¹ : D)` for every `a : L`.

The universes of the three fields or rings are independent. There is no
restriction on characteristic or separability. The two maps preserve
one; because their source is a field and the target is a division ring,
they are injective, so they are precisely actual field embeddings.
No conjugating unit, compatible module isomorphism, matrix splitting or
conjugacy proposition is assumed as an additional premise.

The source is J. S. Milne, *Class Field Theory*, version 4.03 (2020),
Chapter IV, section 2, Theorem 2.10 (Skolem, Noether), printed page 129
(PDF page 138), registered as `milne-2020-class-field-theory`, SHA256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.
The source allows homomorphisms from a simple `K`-algebra into a central
simple `K`-algebra and concludes precisely conjugation by an invertible
element in the target. This statement specializes the source algebra to
the finite field extension `L` and the target to the finite-dimensional
central division algebra `D`. Fields and division rings are simple rings,
so these hypotheses imply the source's simplicity assumptions.
The source's displayed order is retained exactly.

The implementation expresses field extensions through the actual
`Algebra` and `FiniteDimensional` structures, centrality through
`Algebra.IsCentral`, embeddings through `AlgHom` and the invertible
element through `Units`. Independent universes change the formal size
convention, not the mathematical assertion. This is a specialization of
the cited theorem; the general simple-algebra statement and central
simple targets with nontrivial matrix factors are outside its scope.

In a cyclic-subfield application, take one embedding to be the other
composed with a field automorphism. The conclusion then supplies the
actual unit that implements that automorphism on the embedded field.
The separate `CyclicNormCommutator` construction can use such a unit to
turn field-norm-one elements into actual commutators. This explains the
prerequisite's relevance; it does not assert local unramified-subfield
existence or identify the field norm with a reduced norm.

This module only states the proposition and supplies no proof.
It does not prove local SK₁ vanishing or `LocalKneserTitsStatement`.
