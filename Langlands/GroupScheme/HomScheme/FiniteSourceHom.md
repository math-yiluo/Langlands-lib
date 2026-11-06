# Homomorphisms out of a finite free Hopf spectrum

Module `Langlands.GroupScheme.HomScheme.FiniteSourceHom`, namespace
`Langlands.GroupScheme.HomScheme.FiniteSource`.

Let `R` be a commutative ring, and let `A` and `P` be commutative Hopf `R`-algebras, all in one
universe `u`. Write `G_A` and `G_P` for their relative spectra over `Spec R`. This file proves
the following when `P` is finite free over `R` and `A` is finitely presented. The algebra
`HomAlgebra R A P` of `Langlands.Algebra.FiniteBialgebraHom` carries an actual universal family
of group-scheme homomorphisms `G_P → G_A`, in the sense of `HomScheme.IsUniversal`. In other
words, the functor `T ↦ Hom_T(G_P ×_S T, G_A ×_S T)` on all schemes over `S = Spec R` is
represented by `Spec (HomAlgebra R A P)`.

This is internal infrastructure for the task "Prove smooth moduli of actual closed torus
subgroups" (SGA 3, Exp. XI, 4.1, torus case). There `P` is the group algebra `R[(ℤ/m)^I]`. It is
the scheme-theoretic form of the representability of `Hom(H, G)` for a finite free source `H` and
an affine target `G` of finite presentation (compare SGA 3, Exp. XI, 3.12). The Lean formulation
and the proofs are internal to this project.

## Notation

- `hopfGroup R A` is the group scheme `(hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R A))`
  over `Spec R`, using Mathlib's relative spectrum of Hopf algebras.
- `specOver R C` is `Spec C`, as a scheme over `Spec R` via `algebraMap R C`, for an `R`-algebra
  `C` in universe `u`.

## Coordinates on base changes (`section Coordinates`)

- `tensorIso A C : (hopfGroup R A).X.left ×_{Spec R} Spec C ≅ Spec (C ⊗[R] A)` is
  `pullbackSymmetry` followed by Mathlib's `pullbackSpecIso`.
- `baseChangeSpecIso_hom_left` and `baseChangeSpecIso_inv_left` say that the underlying scheme
  maps of the Library isomorphism `HopfCoordinates.baseChangeSpecIso R C A` are `tensorIso A C`
  and its inverse. Both hold by `rfl`.
- `tensorIso_inv_fst`, `tensorIso_inv_snd`, `tensorIso_hom_includeRight` and
  `tensorIso_hom_algebraMap` compute the two pullback projections in tensor coordinates. They are
  `Spec` of `a ↦ 1 ⊗ a` and of `c ↦ c ⊗ 1`.

## Homomorphisms over affine tests (`section Equiv`, `section Points`)

- `relativeHomEquiv A P C` is the bijection from
  `RelativeHom (hopfGroup R P) (hopfGroup R A) (specOver R C)` to the `C`-bialgebra maps
  `C ⊗[R] A →ₐc[C] C ⊗[R] P`. It conjugates by the two isomorphisms `baseChangeSpecIso`, then
  uses that `hopfSpec` is fully faithful (Mathlib's `hopfSpec.fullyFaithful`).
- `relativeHomEquiv_symm_fst`: the homomorphism attached to `φ`, followed by the projection to
  `G_A`, is `tensorIso P C` followed by `Spec` of `a ↦ φ (1 ⊗ a)`.
- `pointEquiv A P C` composes `relativeHomEquiv` with `bialgHomEquiv R` of
  `FiniteBialgebraHom`. It is the bijection from these relative homomorphisms to the Hopf points
  `{f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f}`. Neither finiteness nor freeness of `P` is used
  here.
- `pointEquiv_symm_fst`: the homomorphism attached to a Hopf point `f`, followed by the
  projection to `G_A`, is `tensorIso P C` followed by `Spec f`.
- `specMap g : specOver R D ⟶ specOver R C` is `Spec` of an `R`-algebra map `g : C →ₐ[R] D`.
- `baseChangeProj_specMap g`: in tensor coordinates, the projection
  `baseChangeProj (hopfGroup R P) (specMap g)` is `Spec` of `g ⊗ id_P`.
- `evaluate_specMap g f`: evaluation along `specMap g` corresponds to `pushPoint R g` on Hopf
  points. The proof compares the projections to `G_A` with `relativeHom_ext`.
- `specOverHomEquiv : (specOver R C ⟶ specOver R B) ≃ (B →ₐ[R] C)`. It uses Mathlib's
  `Spec.preimage`, and its inverse is `specMap`.

## The universal family (`section Universal`)

Here `[Module.Finite R P] [Module.Free R P] [Algebra.FinitePresentation R A]`.

- `universalFamily R A P` is the relative homomorphism over `specOver R (HomAlgebra R A P)`
  attached by `pointEquiv` to the universal Hopf point `universalPoint R A P`.
- `bijective_evaluate_universalFamily_specOver R A P C`: on the affine tests `specOver R C`, the
  evaluation map is the composite of three bijections: `specOverHomEquiv`, then
  `homEquiv R A P C` of `FiniteBialgebraHom`, then `(pointEquiv A P C).symm`. The identification
  is `evaluate_specMap` together with `homEquiv_apply`.
- `isUniversal_universalFamily R A P`: the family is universal. By `isUniversal_of_affine` of
  `HomScheme.AffineTest`, it suffices to test affine `T`. Such a `T` is isomorphic over `Spec R`
  to `specOver R Γ(T, ⊤)`, via `T.left.isoSpec`, with the `R`-algebra structure given by
  `Spec.preimage`. Then `bijective_evaluate_of_iso` reduces to the previous result.
