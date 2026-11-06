# Bialgebra maps into a finite free scalar extension

Module `Langlands.Algebra.FiniteBialgebraHom`, namespace `Langlands.FiniteBialgebraHom`.

## Setting

Let `R` be a commutative ring, and let `A` and `P` be commutative `R`-bialgebras in the same universe as `R`.
For a commutative `R`-algebra `C`, write `C ⊗ P` for `C ⊗[R] P`. In this file a *point* is an
`R`-algebra map `f : A → C ⊗ P`. Geometrically, `A` and `P` are the coordinate rings of affine
group schemes `G` and `H` over `Spec R`. A point is then a morphism `H_C → G` of schemes over `R`,
and a *Hopf point* is a group homomorphism `H_C → G_C`.

This is internal infrastructure for the torus case of SGA 3, Exp. XI, 4.1, which is the task
"Prove smooth moduli of actual closed torus subgroups". In that proof `H` is the finite diagonalizable
group `μ_m^I`, whose coordinate ring `R[(ℤ/m)^I]` is finite free. The construction is the standard
one: homomorphisms from a finite free group into an affine group of finite presentation are cut
out, by finitely many equations, inside the Weil restriction that parametrizes all morphisms. The
Lean formulation and the proofs are internal to this project.

## Conditions (`section Conditions`)

- `comulLeft R f : A →ₐ[R] C ⊗ (P ⊗ P)` is `(id_C ⊗ Δ_P) ∘ f`.
- `inclFirst R`, `inclSecond R : C ⊗ P →ₐ[R] C ⊗ (P ⊗ P)` are `id_C` tensored with the two factor
  inclusions `P → P ⊗ P`.
- `comulRight R f` is `(inclFirst ∘ f) · (inclSecond ∘ f)` composed with `Δ_A`. That is, it sends
  `a` with `Δ_A a = Σ a₁ ⊗ a₂` to `Σ inclFirst (f a₁) · inclSecond (f a₂)`.
- `counitMap R f : A →ₐ[R] C` is `(id_C ⊗ ε_P) ∘ f` followed by `C ⊗[R] R ≅ C`.
- `IsHopfPoint R f` is the conjunction of `comulLeft R f = comulRight R f` and
  `counitMap R f = (Algebra.ofId R C) ∘ ε_A`. These say that `f` respects comultiplication and
  counit.
- `pushPoint R g f := (g ⊗ id_P) ∘ f` changes the coefficients along `g : C →ₐ[R] D`. The results
  `pushPoint_pushPoint` and `pushPoint_id` give functoriality. The results `comulLeft_pushPoint`,
  `comulRight_pushPoint` and `counitMap_pushPoint` give naturality of the three maps, and
  `inclFirst_map` and `inclSecond_map` give naturality of the inclusions.
- `IsHopfPoint.pushPoint`: pushing a Hopf point along `g` gives a Hopf point.

## Coordinates (`section Coordinates`)

- `basis_repr_map`: let `b` be an `R`-basis of `Q`. The coordinate at `i` of
  `(g ⊗ id_Q) x` in the scalar-extended basis of `D ⊗ Q` equals `g` applied to the coordinate at
  `i` of `x` in the basis of `C ⊗ Q`.

## Comparison with bialgebra maps (`section BaseChange`)

- `tensorSquareEquiv R P C : (C ⊗ P) ⊗[C] (C ⊗ P) ≃ₐ[C] C ⊗ (P ⊗ P)` composes Mathlib's
  `Algebra.TensorProduct.cancelBaseChange` with `Algebra.TensorProduct.assoc`.
  - `tensorSquareEquiv_tmul` computes it on pure tensors: `x ⊗ y ↦ inclFirst x · inclSecond y`.
  - `tensorSquareEquiv_comul` shows that it carries the comultiplication of the `C`-bialgebra
    `C ⊗ P` to `id_C ⊗ Δ_P`.
- `counitAlgHom_scalarExtension`: the counit of the `C`-bialgebra `C ⊗ P` is `id_C ⊗ ε_P`
  followed by `C ⊗[R] R ≅ C`.
- `restrictPoint R φ` sends a `C`-algebra map `φ : C ⊗ A → C ⊗ P` to its point `a ↦ φ (1 ⊗ a)`.
  It is the inverse of Mathlib's `AlgHom.liftEquiv`.
- Supporting computations: `tensorSquareEquiv_map_comul`, `tensorSquareEquiv_comul_apply` and
  `algebraTensorProductMap_eq_map`.
- `isHopfPoint_restrictPoint`: the point of a `C`-bialgebra map `C ⊗ A →ₐc[C] C ⊗ P` is a Hopf
  point.
- `bialgHomOfHopfPoint R f hf` is the converse. The `C`-linear extension of a Hopf point is a
  `C`-bialgebra map. It is built with `BialgHom.ofAlgHom`, and both conditions are checked on
  `1 ⊗ a`.
- `bialgHomEquiv R` is the bijection
  `(C ⊗[R] A →ₐc[C] C ⊗[R] P) ≃ {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f}`. The lemma
  `bialgHomEquiv_apply_coe` gives `(bialgHomEquiv R φ).1 a = φ (1 ⊗ a)`.

## The representing algebra (`section Representing`)

Here `P` is finite and free as an `R`-module, and `A` is a finitely presented `R`-algebra.

- `Weil R A P` is the Weil restriction `TauCeti.Algebra.WeilRestriction R P (P ⊗[R] A)` from the
  Library. By `TauCeti.Algebra.WeilRestriction.tensorHomEquiv`, its `R`-algebra maps to `C`
  correspond to points `A → C ⊗ P`.
- `weilPoint R A P` is the universal point. `tensorHomEquiv_eq` says that the point attached to
  `g` is `pushPoint R g (weilPoint R A P)`.
- `gens R A` is a chosen finite set of `R`-algebra generators of `A`, and `adjoin_gens` says that
  it generates `A`. `basisPP R P` is the chosen basis of `P ⊗[R] P`.
- `comulRelation R A P` lists the coordinates, in the basis `basisPP`, of
  `comulLeft - comulRight` of the universal point at each generator. `counitRelation R A P` lists
  the counit defects at each generator.
- `relationIdeal R A P` is the ideal spanned by both families. `relationIdeal_fg` says it is
  finitely generated.
- `isHopfPoint_pushPoint_iff`: `pushPoint R g (weilPoint R A P)` is a Hopf point if and only if
  `relationIdeal R A P ≤ ker g`. For the converse direction, both conditions are equalities of
  `R`-algebra maps out of `A`, so they can be checked on the generators. There they are coordinate
  equations, by `basis_repr_map` and the naturality lemmas.
- `HomAlgebra R A P := Weil R A P ⧸ relationIdeal R A P`. The instance
  `Algebra.FinitePresentation R (HomAlgebra R A P)` holds because a Weil restriction of a finitely
  presented algebra along a finite free algebra is finitely presented (Library), and the quotient
  is by a finitely generated ideal.
- `universalPoint R A P` is the image of `weilPoint` in `HomAlgebra R A P ⊗ P`, and
  `isHopfPoint_universalPoint` says that it is a Hopf point.
- `homEquiv R A P C` is the bijection
  `(HomAlgebra R A P →ₐ[R] C) ≃ {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f}` for `C` in the universe
  of `R`. It sends `g` to `pushPoint R g (universalPoint R A P)`, which is the content of
  `homEquiv_apply`. Its inverse lifts the Weil-restriction map of a Hopf point through the
  quotient, using `isHopfPoint_pushPoint_iff`.
