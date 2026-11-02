# Points of standard etale algebras over polynomial rings

Author: Worker 766.

This module is `Langlands.CommutativeAlgebra.EtaleLocalSections`. It imports
only Mathlib.

## Purpose and provenance

This module is the algebraic core of the proof of
`Langlands.AlgebraicGeometry.SmoothSurjectiveEtaleLocalSectionsStatement`
(The Stacks Project, More on Morphisms, Lemma 37.38.6, Tag 055U; registered
source `stacks-055U-smooth-etale-local-sections-2026-11-02`). The geometric
module `Langlands.AlgebraicGeometry.SmoothEtaleLocalSections` reduces that
statement to the main theorem here, which treats a standard etale
algebra `S` over a polynomial ring `R[X₁, …, Xₙ]`. Mathlib shows that every
smooth algebra is locally of this form. The theorem gives, through every prime
of `S`, an etale `R`-algebra `R'` with an `R`-algebra map `S → R'` that hits
the same prime of `R`.

The Stacks source has two proofs. The first uses etale slicing at a point with
finite separable residue field. The second uses a factorization through
relative affine space and a relative complete intersection. The route
implemented here uses neither slicing nor complete intersections. It shares
two ideas with the second proof: it works over relative affine space, and it
finds a point with finite separable residue field in the fibre. Instead of
cutting the fibre down, it specializes the polynomial variables directly. Each
variable `Xᵢ` is sent to a polynomial expression in a root of a separable
monic polynomial over a localization `R[1/b]`. The standard etale presentation
of `S` is then base changed along this specialization. Every lemma below is
derived here from standard facts available in Mathlib, such as the primitive
element theorem and the algebraic closure. No other literature theorem is used.

## Conventions

- `StandardEtalePair R` (Mathlib) is a pair `f, g : R[X]` with `f` monic and
  `f'` invertible in `R[X][1/g]/(f)`. Its ring `P.Ring` is `R[X][Y]/(f, Yg - 1)`.
  `P.HasMap x` means `f(x) = 0` and `g(x)` is a unit, and `P.lift x h` is the
  algebra map `P.Ring → S` sending `X` to `x`. `P.map φ` is the pair with
  coefficients mapped along `φ`.
- `StandardEtalePresentation R S` (Mathlib) is a pair together with an element
  `x : S` for which `P.lift x` is bijective. `equivRing` is the resulting
  isomorphism `S ≃ P.Ring`.
- `𝔭.ResidueField` is the residue field `κ(𝔭)` of a prime `𝔭`.

## Declarations

### Roots and remainders

- `dvd_pow_natDegree_of_forall_isRoot`: over an algebraically closed field,
  if every root of a monic polynomial `f` is a root of `g`, then `f` divides
  `g ^ natDegree f`. The proof factors `f` into linear factors and divides
  factor by factor.
- `exists_root_of_map_modByMonic_ne_zero`: let `f` be monic over a commutative
  ring `A`, let `r` be the remainder of `g ^ natDegree f` modulo `f`, and let
  `φ : A → K` be a ring map to a field. If `r` does not map to zero under `φ`,
  then `f` mapped along `φ` has a root `y` in an algebraic closure of `K` at
  which `g` mapped along `φ` does not vanish. Otherwise the previous lemma gives
  divisibility over the algebraic closure, so the mapped remainder is zero.
- `map_modByMonic_ne_zero_of_eval₂`: conversely, if `f` has a root `y` in `K`
  under `φ` and `g(y) ≠ 0`, then the remainder does not map to zero.

### Separable points of nonvanishing

- `exists_separable_point`: let `h` be a nonzero polynomial in `n` variables
  over a field `κ`. There are a monic `m : κ[X]`, polynomials `p₁, …, pₙ : κ[X]`
  and an element `z` of an algebraic closure of `κ` such that `m(z) = 0`,
  `m'(z) ≠ 0`, and `h(p₁(z), …, pₙ(z)) ≠ 0`.
  - If `κ` is finite, `h` does not vanish at some point `c` with coordinates in
    the algebraic closure (Mathlib `MvPolynomial.funext`, valid because the
    algebraic closure is infinite). The field `κ(c)` is finite and separable over
    the perfect field `κ`, so it has a primitive element `θ`. Take `m` to be the
    minimal polynomial of `θ`, which is separable, so `m'(θ) ≠ 0`. Write each
    `cᵢ` as `pᵢ(θ)`.
  - If `κ` is infinite, `h` does not vanish at some `c` with coordinates in `κ`.
    Take `m = X`, `z = 0` and the constant polynomials `pᵢ = cᵢ`.

### Lifting from a residue field

- `algebraMap_residueField_ne_zero_iff`: an element of `R` has nonzero image
  in `κ(𝔭)` exactly when it is not in `𝔭`.
- `exists_away_lift`: finitely many elements of `κ(𝔭)` all come from one
  localization `R[1/b]` with `b ∉ 𝔭`. More precisely, there are `b ∉ 𝔭` and a
  ring map `β : R[1/b] → κ(𝔭)` extending `R → κ(𝔭)` whose range contains the
  given elements. Write each element as `a / c` with `c ∉ 𝔭` and let `b` be the
  product of the denominators.

### Main theorem

`exists_etale_algHom_of_isStandardEtale`: let `S` be a standard etale algebra
over `P = R[X₁, …, Xₙ]`, compatibly an `R`-algebra, and let `𝔮` be a prime of
`S`. There are an etale `R`-algebra `R'`, an `R`-algebra map `S → R'`, and a
prime of `R'` whose preimage in `R` equals the preimage `𝔭` of `𝔮`.

The proof fixes a standard etale presentation `S ≅ P[X][1/g]/(f)` with image
`x` of `X`, and writes `d` for the degree of `f`, `κ` for `κ(𝔭)` and `r` for
the remainder of `g ^ d` modulo `f`.

1. In `κ(𝔮)` the image of `x` is a root of `f` at which `g` is a unit. By
   `map_modByMonic_ne_zero_of_eval₂`, some coefficient `rⱼ ∈ P` of `r` has
   nonzero image in `κ(𝔮)`.
2. The map `P → κ(𝔮)` factors through `κ[X₁, …, Xₙ]`, using the embedding
   `κ → κ(𝔮)` and the images of the variables. So the image `h` of `rⱼ` in
   `κ[X₁, …, Xₙ]` is nonzero, and `exists_separable_point` gives `m`, `pᵢ` and
   `z` as above.
3. `exists_away_lift`, applied to the coefficients of `m` and of the `pᵢ`, gives
   `b ∉ 𝔭` and `β : R[1/b] → κ`. Lift `m` to a monic polynomial over `R[1/b]`
   with the same degree, and lift each `pᵢ` to a polynomial over `R[1/b]`.
   These lifts are again written `m` and `pᵢ`.
4. Let `R₁` be the standard etale `R[1/b]`-algebra of the pair `(m, m')`.
   It is etale over `R`, as a composite of a localization and a standard etale
   algebra. Let `ψ : P → R₁` send `Xᵢ` to `pᵢ(X)`.
5. Let `R'` be the standard etale `R₁`-algebra of the pair `(f, g)` with
   coefficients mapped along `ψ`. It is etale over `R` by composition. Its
   generator `X` satisfies the original pair's map condition. So the
   presentation `S ≅ P.Ring`, followed by the lift sending `X` to `X`, gives a
   `P`-algebra map `S → R'`, and in particular an `R`-algebra map.
6. Let `K` be an algebraic closure of `κ`, made an `R[1/b]`-algebra through
   `β`. The lifted `m` has root `z` in `K` with `m'(z) ≠ 0`, so the
   standard etale pair gives `ρ₁ : R₁ → K` with `X ↦ z`. The composite
   `ρ₁ ∘ ψ : P → K` equals evaluation of the image in `κ[X₁, …, Xₙ]` at
   `(p₁(z), …, pₙ(z))`. Hence it sends `rⱼ` to `h(p₁(z), …, pₙ(z)) ≠ 0`, and
   `r` does not map to zero.
7. `exists_root_of_map_modByMonic_ne_zero` gives a root `y` of `f`, mapped to
   `K`, in an algebraic closure `L` of `K` with `g(y) ≠ 0`. So the pair of
   `R'` gives an `R₁`-algebra map `ρ' : R' → L`. Its kernel is a prime of `R'`.
   The composite `R → R' → L` is `R → κ → K → L`, and the last two maps are
   injective. So the preimage of the kernel in `R` is the kernel of `R → κ(𝔭)`,
   which is `𝔭`.
