# Cyclic quotients of order ℓ of π₁(Spec R[1/t]) are Kummer

The module `Langlands.AlgebraicGeometry.FiniteEtale.KummerCyclicQuotient`
proves that, over a strictly Henselian regular local domain `R` with a regular
parameter `t` and a prime `ℓ` invertible in `R`, every quotient of order `ℓ`
of the finite étale fundamental group of `U = Spec R[1/t]` is the one cut out
by the Kummer cover `X^ℓ = t`. Declarations are in the namespace
`Langlands.AlgebraicGeometry.FiniteEtale`; rings and the field `Ω` are in one
universe `u`.

## Cover maps to Kummer covers

Let `A` be a commutative ring, `C` a group and
`D : SingleObj C ⥤ Cover (Spec A)`; `coverRing D` and `coverAction D c` are
the ring of the cover and the action of `c ∈ C` on it, from the Library module
`AffineQuotientCoconeProof`.

- `coverBaseHom D : A →+* coverRing D` is the structure map, through
  `Scheme.ΓSpecIso`. `coverBaseHom_ΓSpecIso_hom` compares it with
  `algebraMap Γ(Spec A, ⊤) (coverRing D)`, and `coverAction_coverBaseHom`
  says that `C` fixes its image.
- `kummerCoverHom D a m hm0 hm ha ψ hψ` is the cover map from the cover of
  `D` to the Kummer cover `kummerRootCover a m hm0 hm ha` (from the module
  `KummerCovers`) given by a ring map
  `ψ : KummerRootAlgebra a m →+* coverRing D` that is compatible with the
  structure maps.
- `kummerCoverHom_comm`: if `coverAction D c ∘ ψ = ψ ∘ kummerScale R a m η`
  for an `m`-th root of unity `η` of a ring `R` with `[Algebra R A]`, then
  the cover map intertwines the action of `c` with the cover endomorphism
  `kummerScaleHom … η` (`X ↦ ηX`).

## The Kummer character of the parameter

- `isUnit_natCast_away`: an integer invertible in `R` is invertible in
  `Localization.Away t`.
- `card_rootsOfUnity_eq`: for a Henselian local domain `R` with separably
  closed residue field and `m ≠ 0` invertible in `R`,
  `Nat.card (rootsOfUnity m R) = m` (from a primitive `m`-th root of unity,
  `StrictlyHenselianKummerUnits.exists_isPrimitiveRoot`).
- `parameterKummerCharacter t x m hm0 hmR`, for a geometric point
  `x : Spec Ω ⟶ Spec (Localization.Away t)`, is the Kummer character
  `kummerCharacter` (module `KummerCovers`) of the cover
  `Spec R[1/t][X]/(X^m - t)`, a homomorphism
  `FundamentalGroup x (geometricFiberFinite x) →* rootsOfUnity m R`. The
  Kummer algebra of `a = t` is literally the Library's `KummerAlgebra t m`.

## The theorem

`ker_le_ker_parameterKummerCharacter` assumes that `R` is a regular local
domain, Henselian with separably closed residue field, that
`t ∈ maximalIdeal R` and `t ∉ maximalIdeal R ^ 2`, that `ℓ` is a prime
invertible in `R`, and that `x` is a geometric point of `Spec R[1/t]` with
`Ω` algebraically closed. For every surjective homomorphism
`χ : FundamentalGroup x _ →* rootsOfUnity ℓ R` with open kernel it concludes

- `χ.ker ≤ (parameterKummerCharacter t x ℓ _ hℓR).ker`, and
- `parameterKummerCharacter t x ℓ _ hℓR ≠ 1`.

Proof as implemented.

1. `t` is prime (`RegularLocalFactorial.prime_of_mem_maximalIdeal_notMem_sq`),
   so `R[1/t]` is a Noetherian domain, and `rootsOfUnity ℓ R` has `ℓ`
   elements.
2. By `exists_torsor_cover` (module `KummerCyclicCover`), `χ` is realized by
   a diagram `D` whose geometric fibre at `x` is a torsor under
   `rootsOfUnity ℓ R`, the fundamental group acting through `χ`. So the
   action of the roots of unity is transitive and free.
3. Choose `ζ ≠ 1` in `rootsOfUnity ℓ R`; it has order `ℓ` and generates the
   group. Make `B = coverRing D` an `R[1/t]`-algebra through `coverBaseHom`,
   and let `σ` be the `R[1/t]`-algebra automorphism `coverAction D ζ`. Then
   `σ^ℓ = 1`. An element fixed by `σ` is fixed by the whole group, hence
   comes from `R[1/t]` (`exists_algebraMap_eq_of_forall_coverAction_eq`). Over
   every maximal ideal of `R[1/t]` there is a field point `φ` of `B` with
   `φ ∘ σ^j ≠ φ` for `0 < j < ℓ` (`exists_free_residue_point`). The map
   `R[1/t] → B` is injective (`bijective_algebraMap_quotientRing`).
4. The Picard group of `R[1/t]` is trivial (the Library's
   `regularLocalAwayPicard`). By
   `KummerEigenvector.exists_unit_eigenvector`, there are a unit `v` of `B`
   with `σ(v) = ζ v` and a unit `w` of `R[1/t]` with `v^ℓ = w`.
5. By `exists_kummerLift_of_unit_eigenvector` (module `KummerCyclicAlgebra`),
   for `a = 1` or `a = t` there are `η ≠ 1` in `rootsOfUnity ℓ R` and an
   `R[1/t]`-algebra map `ψ : R[1/t][X]/(X^ℓ - a) → B` with
   `σ ∘ ψ = ψ ∘ (X ↦ ηX)`. Let `π = kummerCoverHom … ψ`, a cover map to the
   Kummer cover of `a`; by `kummerCoverHom_comm` it intertwines `ζ` with
   `X ↦ ηX`.
6. Fix a point `y` of the fibre of `D`. For `g` in the fundamental group,
   `g • y = y · χ(g)`. Write `κ_a` for the Kummer character of `a`. If
   `χ(g) = 1`, then `g` fixes `y`, hence fixes `π(y)` (`smul_naturality`), so
   `κ_a(g) = 1` (`smul_eq_self_iff_kummerCharacter`). For `g₀` with
   `χ(g₀) = ζ`, `g₀ • π(y) = π(y · ζ) = π(y) · η`, so `κ_a(g₀) = η`
   (`smul_eq_comp_kummerCharacter`, `kummerScale_injective`).
7. If `a = 1`, then `κ_a` is trivial (`kummerCharacter_one_eq_one`), which
   contradicts `κ_a(g₀) = η ≠ 1`. So `a = t` and `κ_a` is the parameter
   Kummer character of level `ℓ`: it vanishes on `ker χ`, and it is
   nontrivial since `κ_a(g₀) = η ≠ 1`.

## Provenance

This is the Kummer description of cyclic covers of degree `ℓ` of `R[1/t]`:
since `Pic R[1/t] = 0`, such a cover is generated by an `ℓ`-th root of a unit
of `R[1/t]`; the units of `R[1/t]` are `R^× t^ℤ`, and every unit of the
strictly Henselian ring `R` is an `ℓ`-th power, so the unit can be taken to be
`1` or `t`, and `1` is excluded for a connected cover. This is the degree-`ℓ` case of the
structure of tame covers along a regular divisor (SGA 7 I, Exposé I, 0.3–0.4;
Stacks, *Fundamental Groups of Schemes*, Lemma 58.31.5, Tag 0EYG, whose proof
treats a strictly Henselian base directly). The argument through eigenvectors
of a generator, the Picard group and the Library's fibre functors is internal
to the Library.
