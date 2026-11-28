# Tensor factors over a normal subgroup

This internal module collects facts of finite-dimensional complex representation theory used to
split a representation `κ ⊗ ξ` off a representation `τ` when `κ` is known on a normal subgroup
`N`. This is the standard Clifford-theoretic step used in the theory of types: if the restrictions
of `κ` and `τ` to `N` have a nonzero intertwiner, then there is a nonzero intertwiner
`κ ⊗ ξ → τ` of representations of `G` for an irreducible representation `ξ` of `G` trivial on
`N`. When in addition the restriction of `κ` to `N` is irreducible, `κ ⊗ ξ` is irreducible
(`Langlands.BushnellKutzko.isIrreducible_tensor_of_irreducible_restriction`), so this nonzero
intertwiner is injective and `τ` contains `κ ⊗ ξ`. Without that irreducibility only the nonzero
intertwiner is asserted: for `G` of order two, `N = 1`, `κ = 1 ⊕ sgn` and `τ = 1 ⊕ 1`, no
`κ ⊗ ξ` embeds in `τ`. Groups carry no topology here and need not be finite; all representations
are on complex vector spaces (namespace `Langlands.Clifford`).

## Atoms and semisimplicity

- `exists_isAtom_le`: a nonzero subrepresentation of a finite-dimensional representation contains
  an atom of the lattice of subrepresentations. The lattice is well-founded because
  `Subrepresentation.toSubmodule` is strictly monotone and the submodule lattice of a
  finite-dimensional space is well-founded, so the lattice is atomic.
- `isSemisimpleRepresentation_of_trivial_on_normal` (Maschke's theorem through a finite
  quotient): a complex representation of `G` that is trivial on a normal subgroup `N` of finite
  index is semisimple. The representation factors through the finite group `G / N`
  (`QuotientGroup.lift`), where Mathlib's Maschke theorem gives a complement to every
  subrepresentation; a subrepresentation for `G` is the same subspace as one for `G / N`.
- `exists_isAtom_eigen`: let `ρ` be a semisimple finite-dimensional representation of `G`, `ι : H →
  G` a homomorphism and `θ` a character of `H`. If some nonzero vector `v` satisfies
  `ρ(ι h) v = θ(h) v` for all `h`, then some atom `Y` of the lattice of subrepresentations contains
  a nonzero vector with the same property. The proof takes a subrepresentation `Y` of least
  dimension containing such a vector `w`. If `Z < Y` is a subrepresentation, choose a complement
  `C` of `Z` and let `p` be the projection onto `Z` along `C`
  (`FiniteQuotientAveraging.projectionOfIsCompl`), an intertwiner. If `p w ≠ 0`, it is a
  `θ`-eigenvector in `Z`, contradicting minimality; if `p w = 0`, then `w ∈ C`, so `Y ⊓ C`
  also contains `w`, and minimality gives `Y ⊓ C = Y`, that is, `Y ≤ C`. Then `Z < Y` gives
  `Z ≤ C`, so `Z ≤ Z ⊓ C = ⊥`.

## Orbits

- `finiteDimensional_orbitSpan_of_fixed`: the orbit span `FiniteVectors.orbitSubrepresentation ρ x`
  of a vector `x` fixed by a subgroup `K` of finite index is finite-dimensional: writing
  `(gK).out = g h` with `h ∈ K` (`QuotientGroup.mk_out_eq_mul`), every `ρ(g) x` equals
  `ρ((gK).out) x`, so the orbit span lies in the span of finitely many vectors.
- `apply_eq_of_mem_orbitSpan`: if `K` is normal and fixes `x`, it fixes every vector of the orbit
  span, since `ρ(k) ρ(g) x = ρ(g) ρ(g⁻¹ k g) x = ρ(g) x`.

## Coordinates

- `coordinateRep σ` transports a representation `σ` on a finite-dimensional space `Y` to the
  coordinate space `Fin (finrank ℂ Y) → ℂ` through the linear equivalence of `Module.finBasis`;
  `coordinateEquiv σ` is this equivalence as an equivalence of representations, and
  `coordinateRep_eq_one` records that an element acting trivially on `Y` acts trivially in
  coordinates. This puts representations of varying dimension on spaces in universe `0`.

## Tensor factors

- `evalIntertwining κ τ T`: for a subrepresentation `T` of `linHom κ τ` (on which `g` acts by
  `f ↦ τ(g) ∘ f ∘ κ(g)⁻¹`), evaluation `w ⊗ f ↦ f(w)` is an intertwiner `κ ⊗ T → τ`
  (`evalIntertwining_tmul`).
- `exists_irreducible_tensor_intertwining`: let `ι : H → G` be a homomorphism whose image `N` is
  normal, and `κ`, `τ` finite-dimensional representations of `G`. If there is a nonzero
  intertwiner from `κ ∘ ι` to `τ ∘ ι`, then there are `d` and an irreducible representation `ξ` of
  `G` on `Fin d → ℂ`, trivial on `N` and on every `g` with `κ(g) = 1` and `τ(g) = 1`, with a
  nonzero intertwiner `κ ⊗ ξ → τ`. The given intertwiner lies in `restrictIntertwiners N κ τ`
  (the `N`-invariant part of `linHom κ τ`, module `Langlands.Representation.Clifford.Twist`), so
  this subrepresentation is nonzero and contains an atom `T` (`exists_isAtom_le`); `T` is
  irreducible (`FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom`), and `N` acts
  trivially on it, as does every `g` acting trivially on `κ` and on `τ`. The proof takes
  `ξ = coordinateRep T` and composes `evalIntertwining κ τ T` with the coordinate equivalence on
  the second factor (Mathlib's `IntertwiningMap.lTensor`); it is nonzero on `w ⊗ f` for a nonzero
  `f ∈ T` and a vector `w` with `f(w) ≠ 0`.

## Pullbacks

- `subrepresentationCompOrderIso ρ ι hι`: let `ι : H → G` be a homomorphism such that every
  operator `ρ(g)` equals some `ρ(ι(x))`. A subspace is stable under `ρ ∘ ι` exactly when it is
  stable under `ρ`, so the two lattices of subrepresentations are order-isomorphic (the
  isomorphism keeps the underlying subspace).
- `isIrreducible_comp_iff`: under the same hypothesis, `ρ ∘ ι` is irreducible exactly when `ρ`
  is, since irreducibility is simplicity of the lattice of subrepresentations
  (`OrderIso.isSimpleOrder_iff`).
