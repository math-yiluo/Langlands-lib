# Equivariant endomorphisms with finite multiplicities

Module `Langlands.Representation.Archimedean.ComplexPermutationEndomorphism`, namespace
`Langlands.Archimedean.ComplexPermutation`. Abstract linear algebra used for permutation
invariance of complex principal series (`ComplexStandardPermutationStatement`). There is no
literature source for this module: it is an internal helper, and its statements are standard
facts about representations with finite multiplicities.

## Setting

`ρ` is a representation of a group `G` on a complex vector space `W`. Two hypotheses are used:

* every vector is a finite vector (`FiniteVectors.IsFiniteVector ρ w`: its orbit spans a
  finite-dimensional subspace);
* a linear functional `ev : W → ℂ` separates vectors along orbits: if `ev (ρ g w) = 0` for every
  `g`, then `w = 0`.

For the `U(n)`-finite functions of a principal series, `ev` is evaluation at `1`.

## Declarations

* `eqvHom ρ F`: for a subspace `F ≤ W`, the `G`-equivariant linear maps `φ : F → W`, that is
  `φ (ρ g x) = ρ g (φ x)` whenever `x` and `ρ g x` lie in `F`. `subtype_mem_eqvHom`: the
  inclusion of `F` is equivariant. `compEqvHom ρ F E hE`: composition with an equivariant
  endomorphism `E` of `W`, a linear endomorphism of `eqvHom ρ F`.
* `finiteDimensional_eqvHom`: if `F` is finite-dimensional and invariant, `eqvHom ρ F` is
  finite-dimensional. Proof: `φ ↦ ev ∘ φ` is injective into the dual of `F`, since
  `ev (ρ g (φ x)) = ev (φ (ρ g x))` and `ev` separates orbits.
* `surjective_of_injective`: an injective equivariant endomorphism `E` of `W` is surjective.
  Proof: for `w ∈ W` let `F` be its orbit span (finite-dimensional, invariant). Composition with
  `E` is an injective endomorphism of the finite-dimensional space `eqvHom ρ F`, hence
  surjective; so the inclusion of `F` is `E ∘ ψ` for an equivariant `ψ`, and `w = E (ψ w)`.
* `pairingMap`, `exists_invariant_complement`: let `B : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ` be a sesquilinear
  form (linear in the first, conjugate-linear in the second argument) that is `G`-invariant,
  `B (ρ g x) (ρ g y) = B x y`, and positive definite in the weak sense `B x x = 0 → x = 0`. In a
  finite-dimensional invariant subspace `F'`, every invariant `U ≤ F'` has an invariant
  complement `C ≤ F'` (`U ⊓ C = ⊥`, `U ⊔ C = F'`). The complement is `C = F' ∩ ⋂ᵢ ker B(·, uᵢ)`
  for a basis `uᵢ` of `U`. It is orthogonal to all of `U` by conjugate-linearity. It is invariant:
  `B (ρ g x) u = B x (ρ g⁻¹ u)`. It meets `U` trivially by positivity. Its dimension is at least
  `dim F' - dim U` by rank–nullity.
* `exists_finite_invariant`: finitely many vectors lie in a finite-dimensional invariant
  subspace (the sum of their orbit spans).
* `exists_lift`: if `E` is a surjective equivariant endomorphism and `B` is as above, every
  `φ ∈ eqvHom ρ F` (with `F` finite-dimensional) is `E ∘ ψ` for some `ψ ∈ eqvHom ρ F`. Proof:
  choose preimages `y_j` of the images `φ (b_j)` of a basis of `F` and a finite-dimensional
  invariant `F'` containing them. Take an invariant complement `C` of `ker E ∩ F'` in `F'`. Then
  `E` is injective on `C`, and `φ(F) ⊆ E(C)`, because `y_j = u + c` with `E u = 0`. Put
  `ψ = (E|_C)⁻¹ ∘ φ`. Then `ψ` is equivariant, because `E (ψ (ρ g x)) = E (ρ g (ψ x))` with
  both arguments in `C`.
* `injective_of_surjective`: a surjective equivariant endomorphism `E` is injective when `W`
  carries such a form `B`. Proof: for `v ∈ ker E` let `F` be its orbit span, so `F ⊆ ker E`. By
  `exists_lift`, composition with `E` is surjective on the finite-dimensional `eqvHom ρ F`, hence
  injective. It sends the inclusion of `F` to `0`, so the inclusion is `0` and `v = 0`.
