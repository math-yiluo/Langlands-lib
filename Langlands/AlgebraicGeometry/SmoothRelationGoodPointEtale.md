# Étale coordinates from differentials

This internal module supplies the étale-coordinates step of the good-point
existence proof (`SmoothRelationGoodPointExistence`). It is pure commutative
algebra. Throughout, `κ(T)` is the residue field of a local ring `T` and
`Ω[T⁄A]` its module of Kähler differentials.

## Statements

- `formallyEtale_of_bijective_mapBaseChange`: let `A → S → T` be ring maps
  with `T` formally smooth over `A`. If the map
  `T ⊗_S Ω[S⁄A] → Ω[T⁄A]` (`KaehlerDifferential.mapBaseChange`) is bijective,
  then `T` is formally étale over `S`.
- `formallyEtale_mvPolynomial`: let `T` be a local, formally smooth
  `A`-algebra with `Ω[T⁄A]` finitely presented, and also an algebra over the
  polynomial ring `S = A[X_i]` compatibly with `A`. If the elements
  `1 ⊗ d(X_i)` form a basis of `κ(T) ⊗_T Ω[T⁄A]` (linearly independent and
  spanning), then `T` is formally étale over `S`.
  `formallyEtale_mvPolynomial_of_eq` is the same statement with the images of
  the variables given as a family `z i`.
- `span_one_tmul_eq_top`: if a set `s` spans a module `M` over a local ring
  `T`, then the elements `1 ⊗ m`, `m ∈ s`, span `κ(T) ⊗_T M` over `κ(T)`.
- `exists_coordinates`: for a local `A`-algebra `T` and `θ : A →+* T` whose
  differentials `d θ(a)` span `Ω[T⁄A]`, there are a type `ι` (in the universe
  of `A`) and `g : ι → A` such that the elements `1 ⊗ d θ(g i)` form a basis
  of `κ(T) ⊗_T Ω[T⁄A]`.
- `span_one_tmul_D_X_eq_top`: if the local ring `T` is formally étale over
  `A[X_i]` (compatibly with `A`), then the elements `1 ⊗ d(X_i)` span
  `κ(T) ⊗_T Ω[T⁄A]`.
- `exists_etale_coordinates` (main theorem): let `B` be a smooth `A`-algebra
  and `θ : A →+* B` a ring map such that the differentials `d θ(a)`,
  `a ∈ A`, span `Ω[B⁄A]` over `B`. For every prime `q` of `B` there are a
  finite type `ι` (in the universe of `A`) and `g : ι → A` with the
  following property. For every `A[X_i]`-algebra structure on `B`,
  compatible with `A`, that sends `X_i` to `θ(g i)`, the algebra `B` is étale
  at `q` over `A[X_i]` (`Algebra.IsEtaleAt`: the localization `B_q` is
  formally étale over `A[X_i]`).
- `residueSpan_eq_top_of_isEtaleAt`: in the same setting, at any prime `P`
  of `B` where `B` is étale over `A[X_i]`, the elements
  `1 ⊗ d θ(g i)` span `κ(B_P) ⊗ Ω[B_P⁄A]` over `κ(B_P)`. This is the
  coordinate spanning hypothesis of `isGoodPoint_of_simpleIntegerRoots`
  (module `SmoothRelationGoodPointConverse`).

## Proofs

`formallyEtale_of_bijective_mapBaseChange` uses the definition of formal
étaleness in Mathlib, `Ω[T⁄S] = 0` and `H¹(L_{T/S}) = 0`. The first holds
because `Ω[T⁄A] → Ω[T⁄S]` is surjective with kernel the range of
`mapBaseChange` (`KaehlerDifferential.range_mapBaseChange`), which is
everything. The second follows from the Jacobi–Zariski sequence
`H¹(L_{T/A}) → H¹(L_{T/S}) → T ⊗_S Ω[S⁄A] → Ω[T⁄A]`: `H¹(L_{T/A}) = 0`
because `T` is formally smooth over `A`, and the last map is injective.

For `formallyEtale_mvPolynomial`, `Ω[T⁄A]` is projective, hence flat, and
finitely presented over the local ring `T`; so the elements `d(X_i)` form a
`T`-basis of `Ω[T⁄A]` (`Module.exists_basis_of_basis_baseChange`). The basis
`d X_i` of `Ω[S⁄A]` (`KaehlerDifferential.mvPolynomialBasis`) base changes to
the basis `1 ⊗ d X_i` of `T ⊗_S Ω[S⁄A]`, and `mapBaseChange` maps it to the
basis `d(X_i)`. Hence `mapBaseChange` is a linear equivalence and the
previous lemma applies.

`exists_coordinates` chooses a linearly independent subfamily with the same
span (`exists_linearIndependent'`); the span of all `1 ⊗ d θ(a)` is everything
by `span_one_tmul_eq_top`. For `span_one_tmul_D_X_eq_top`, formal étaleness
gives `Ω[T⁄S] = 0`, so `mapBaseChange` is surjective; its image of the
spanning set `1 ⊗ d X_i` is the family `d(X_i)`, which therefore spans
`Ω[T⁄A]`, and `span_one_tmul_eq_top` passes to `κ(T)`.

For `exists_etale_coordinates`, put `T = B_q`. It is formally smooth over
`A` (localization of a smooth algebra) and essentially of finite type, so
`Ω[T⁄A]` is finitely presented. Since `Ω[T⁄A]` is the localization of
`Ω[B⁄A]` (`span_eq_top_of_isLocalizedModule`), the differentials of the
images of `θ(a)` span `Ω[T⁄A]`. `exists_coordinates` gives `g`; the index type
is finite because `κ(T) ⊗ Ω[T⁄A]` is finite dimensional. For a given algebra
structure with `X_i ↦ θ(g i)`, the image of `X_i` in `T` is the image of
`θ(g i)`, and `formallyEtale_mvPolynomial_of_eq` applies.
`residueSpan_eq_top_of_isEtaleAt` is `span_one_tmul_D_X_eq_top` for `B_P`,
rewritten with `X_i ↦ θ(g i)`.

## Provenance

Internal to the good-point existence proof for the slicing statement
`SmoothEquivalenceRelationEtaleSliceStatement` (task 3c6168ac). The main
theorem is a variant of the fact that a smooth morphism is, near a point,
étale over an affine space (Stacks Project, Morphisms, Lemma 29.37.21, tag
054L). The variant chooses the affine coordinates as pullbacks along the
second map `θ` of functions on the base, using that their differentials
span the relative cotangent module; that a basis of the residue cotangent
space then gives étaleness at the point is the Jacobi–Zariski argument
above. The Lean proofs are direct and do not follow the Stacks proof, which
goes through standard smooth presentations.
