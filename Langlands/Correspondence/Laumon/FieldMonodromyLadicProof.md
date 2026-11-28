# Proof of `LadicFieldMonodromyStatement`

Module `Langlands.Correspondence.Laumon.FieldMonodromyLadicProof`. The theorem
`Langlands.Henniart.Laumon.ladicFieldMonodromyStatement` proves
`Langlands.Henniart.Laumon.LadicFieldMonodromyStatement` (module
`Langlands.Correspondence.Laumon.FieldMonodromy`) at its universe parameters `u` and `uW`.
Laumon identifies lisse `ℚ̄_ℓ`-sheaves on the generic point of a henselian trait with
continuous finite-dimensional Galois representations defined over finite extensions of `ℚ_ℓ`
(1987, (2.1.2)–(2.1.2.1), p. 152). The Lean statement makes the comparison over every field
`K` and includes exactness, compatibility with tensor products, and the correspondence between
simple sheaves and irreducible ℓ-adic classes over a nonarchimedean local field.

The proof applies `ladicFieldMonodromyStatement_of_isHomeomorph`
(`Langlands.Correspondence.Laumon.FieldMonodromyLadic`) to
`Langlands.Henniart.Laumon.fieldGaloisToAut_isHomeomorph`
(`Langlands.Correspondence.Laumon.FieldMonodromy.GaloisAut`). Clause 1 of
`FiniteEtaleFieldMonodromyStatement` is the assertion that for every field `K` and separable
closure `Ω`,
`fieldGaloisToAut K Ω` is a homeomorphism from the Krull-topologized Galois group onto the
automorphism group of the finite étale fibre functor. The page of
`Langlands.Correspondence.Laumon.FieldMonodromyLadic` gives the proof of each clause.

The theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
