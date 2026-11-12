# Finite-order etale specialization of a smooth algebra

`Langlands.CommutativeAlgebra.SmoothEtaleCompletionApproximationStatement.{u}`
states the following auxiliary result. Let `R : Type u` be a commutative
Noetherian local ring, let `m` be its maximal ideal, and let `B : Type u` be a
smooth `R`-algebra. For each `R`-algebra map `f : B → AdicCompletion m R` and
each natural number `N`, there are an etale `R`-algebra `E : Type u` and
`R`-algebra maps `g : B → E` and `ι : E → AdicCompletion m R` such that
`ι ∘ g` and `f` have exactly the same composite with the canonical map to
`R / m^N`.

This is an internal auxiliary statement for the unchanged
`FiniteTypeIntEtaleCompletionApproximationStatement`. It isolates the step
after a smooth factorization has been obtained. It neither asserts that
arbitrary finite-type algebras admit such a factorization nor supplies any
arithmetic regularity or Popescu input.

The intended proof specializes polynomial coordinates of a smooth chart
modulo `m^N`, producing an etale algebra with a specified map to `R / m^N`.
Formal smoothness lifts its residue map to the completion; formal
unramifiedness forces agreement with the specified map to `R / m^N`.
The statement includes `N = 0`, allows nonreduced `R` and `B`, and imposes
neither locality of `E` nor injectivity of `ι`. This pair states the result;
it does not prove it.
