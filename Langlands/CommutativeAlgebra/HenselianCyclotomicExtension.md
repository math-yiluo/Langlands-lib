# Finite étale local extensions carrying roots of unity and a residue automorphism

The module `Langlands.CommutativeAlgebra.HenselianCyclotomicExtension`
builds a finite étale extension `R'` of a Henselian regular local ring `R` that
receives a given étale `R`-algebra, contains a root of unity of exact order
`n`, and has an `R`-algebra endomorphism that lifts a given automorphism of
the separable closure of the residue field. In the proof of the tame
conjugation law this ring plays the role of the residue field extension in
the residue fundamental group sequence (SGA 7 I, Exposé I, 0.3 and 0.4).

Throughout, `k = ResidueField R` and `K = SeparableClosure k`.

## Declarations

- `eq_of_pow_eq_one`: let `π : A →+* F` be a ring homomorphism to a field such
  that every `x` with `π x ≠ 0` is a unit, and `(n : F) ≠ 0`. If `a ^ n = 1`,
  `b ^ n = 1` and `π a = π b`, then `a = b`. Proof:
  `(∑ aⁱ bⁿ⁻¹⁻ⁱ) * (a - b) = aⁿ - bⁿ = 0`, and the sum maps to `n * (π a)ⁿ⁻¹`,
  which is nonzero, so the sum is a unit.
- `exists_residuePoint`: for an étale `R`-algebra `S` (here `R` is only
  assumed regular local) and a prime `z` of `S` over the maximal ideal, there
  is an `R`-algebra map `S → K`. The prime `z` serves only to certify that
  the closed fibre `k ⊗[R] S` is nonempty; the map need not come from `z`.
  Proof: `k ⊗[R] S` maps onto `S ⧸ z`, so it is nontrivial; take a maximal
  ideal `M`. The field `(k ⊗[R] S) ⧸ M` is separable over `k` (a Mathlib
  instance for étale algebras over a field), so it embeds into `K` over `k`
  (`IsSepClosed.lift`).
- `exists_finiteDimensional_normal`: a finite subset of a normal extension `K`
  of `k` lies in an intermediate field that is finite-dimensional and normal
  over `k`: the normal closure of the field it generates.
- `exists_etaleCover_intermediateField`: for `R` regular local (only the
  locality of `R` is used), every
  finite-dimensional intermediate field `k'` of `K / k` is the image of a
  surjective `R`-algebra map `L → k'` from a local, finite étale `R`-algebra
  `L`. Proof: `k'` is finite and formally unramified over `R`, and
  `R → k'` is a local homomorphism; a field is a Henselian local ring. The
  Library theorem
  `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal.exists_etaleCover`
  then gives `L`.
- `exists_domainCover`: for `R` a Henselian regular local domain, the ring
  `L` can be taken to be a Henselian local domain with `R → L` injective and
  with `π x ≠ 0 → IsUnit x`. Proof: `L` is Henselian by the package theorem
  `HenselianLocalRing.finite_local_henselian`. `R` is factorial by the Library
  theorem `Langlands.CommutativeAlgebra.regularLocalFactorial`, hence a
  normal domain, so the local étale `R`-algebra `L` is a domain by the package
  theorem `Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization`.
  The kernel of `π` is the maximal ideal of `L`. `L` is flat, so a nonzero `r`
  of `R` is a nonzerodivisor on `L`, and `R → L` is injective.
- `exists_root_of_unity_lift`: in a Henselian local ring `L` with `n` a unit,
  every `n`-th root of unity in a residue field `F` (a surjection `π` whose
  kernel is the set of non-units) lifts to an `n`-th root of unity of `L`.
  This is Hensel's lemma for the separable polynomial `X ^ n - 1`.
- `exists_extension` assumes that `R` is a Henselian regular local domain, that
  `n` is a unit of `R`, and that `φ` is a `k`-algebra automorphism of `K` with
  `φ ζ = ζ ^ q` for every `ζ` with `ζ ^ n = 1`. Let `S` be an étale
  `R`-algebra and `z` a prime of `S` over the maximal ideal. Then there are a
  domain `R'`, an `R`-algebra structure with `Module.Finite R R'`,
  `Algebra.Etale R R'` and `R → R'` injective, and:
  - an element `ζ : R'` with `ζ ^ n = 1` and `IsUnit (ζ ^ l - 1)` for
    `0 < l < n`;
  - an `R`-algebra endomorphism `α` of `R'` with `α ζ = ζ ^ q`;
  - an `R`-algebra map `S →ₐ[R] R'`.

## Proof of `exists_extension`

Take `ψ₀ : S → K` from `exists_residuePoint` and a primitive `n`-th root of
unity `ζ₀` of `K`; it exists because `n ≠ 0` in `k`. Choose finitely many
generators of `S` over `R`. By `exists_finiteDimensional_normal` there is a
finite normal intermediate field `k'` containing `ζ₀` and the images of the
generators. Take `L` and `π : L → k'` from `exists_domainCover`; put `R' = L`.

- `ψ₀` lands in `k'`. The Library theorem
  `Langlands.CommutativeAlgebra.HenselianEtaleAlgebraLift.exists_lift` lifts
  `S → k'` along `π` to an `R`-algebra map `S → L`.
- `φ` restricts to an automorphism `φ'` of the normal extension `k'`
  (`AlgEquiv.restrictNormal`). The same lifting theorem, applied to the
  étale `R`-algebra `L` and the map `φ' ∘ π : L → k'`, gives an `R`-algebra
  endomorphism `α` of `L` with `π ∘ α = φ' ∘ π`.
- `exists_root_of_unity_lift` gives `ζ` with `ζ ^ n = 1` and `π ζ = ζ₀`.
  For `0 < l < n`, `π (ζ ^ l - 1) = ζ₀ ^ l - 1 ≠ 0` because `ζ₀` is primitive,
  so `ζ ^ l - 1` is a unit.
- `α ζ` and `ζ ^ q` are both `n`-th roots of unity, and they have the same
  image `φ ζ₀ = ζ₀ ^ q` in `k'`. By `eq_of_pow_eq_one` they are equal.
