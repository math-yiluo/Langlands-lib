# Homomorphisms from a finite diagonalizable group into a group of multiplicative type

This module is an internal helper for the étale-local splitting of groups of
multiplicative type (Conrad, *Reductive group schemes*, Appendix B, B.3.4). Its main
result is `etale_homAlgebra`. Let `G` be an affine group over `Spec R` of finite
presentation that becomes diagonalizable, `G_{R'} ≅ D(Λ)`, after a faithfully flat ring
map `R → R'`. Then for every finite abelian group `A`, the Hopf-point algebra
`HomAlgebra R 𝒪(G) R[A]` is étale over `R`. This algebra comes from the published
`Langlands.Algebra.FiniteBialgebraHom` and represents homomorphisms `D(A) → G`.

Geometrically, the scheme `Hom(D(A), G)` is étale over `Spec R`. This is the classical
rigidity of homomorphisms between groups of multiplicative type, specialized to a finite diagonalizable source. The proof below is
derived and does not follow a specific text. It has two parts:

1. formal étaleness of `R' ⊗[R] HomAlgebra`, from the lifting of Hopf points between
   group algebras (`Langlands.Algebra.GroupAlgebraHopfPointLift`);
2. Mathlib's faithfully flat descent of étaleness,
   `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`.

## Base change of relative homomorphisms (section `BaseChange`)

Let `b : S' ⟶ S` and let `H`, `G` be group schemes over `S`. The published
`RelativeHom H G T` is the type of homomorphisms `H_T → G_T` over an `S`-scheme `T`, and
`evaluate` restricts them along maps of test objects.

* `compIso b T H` is the published `Descent.pullbackComparison`, the isomorphism
  `(H_{S'})_T ≅ H_T` for an `S'`-scheme `T`. Here `T` is viewed over `S` by `Over.map b`.
* `baseChangeEquiv b T : RelativeHom H G ((Over.map b).obj T) ≃
  RelativeHom H_{S'} G_{S'} T` conjugates by these comparisons.
* `baseChangeEquiv_evaluate` says that `baseChangeEquiv` commutes with `evaluate` along
  a map `a : T' ⟶ T` of `S'`-schemes. The supporting lemmas `relativeHom_left_snd`,
  `compIso_hom_left_snd`, `compIso_hom_fst`, `compIso_hom_snd`, `compIso_inv_fst`,
  `left_fst_snd` and `compIso_hom_baseChangeProj` compute the comparisons against the
  pullback projections. The proof checks equality after composing with the two
  projections, using the published `relativeHom_ext`.

## The point chain (sections `Etale` and `EtaleChain`)

Fix `R → R'`, `G` affine over `Spec R` with `Algebra.FinitePresentation R 𝒪(G)` (for
`𝒪(G) = AffineCoordinates.hopfAlgebra G`), an abelian group `Λ`, an isomorphism
`ψ : G_{R'} ≅ D(Λ)_{R'}` (to `RelativeMultiplicativeType.diagonalizable`), and a finite
abelian group `A`.

* `specBase R R'` is `Spec R' ⟶ Spec R`. `specOverIso B` identifies `Spec B` over
  `Spec R'`, pushed to `Spec R`, with `Spec B` over `Spec R`, for an `R'`-algebra `B`
  with compatible `R`-algebra structure. `specOverIso_naturality` is its compatibility
  with `specMap`.
* `evaluateEquiv e` is evaluation along an isomorphism `e : T' ≅ T` of test objects, as
  an equivalence.
* `sourceIso R R' A` identifies the Hopf spectrum of `R'[A]` over `R'` with the base
  change of the Hopf spectrum of `R[A]`. It composes the published
  `hopfSpecIso`, `relativeModelIso` and `diagonalizableBaseChangeIso`.
* `targetIso G ψ` identifies the base change of the Hopf spectrum of `𝒪(G)` with the
  Hopf spectrum of `R'[Λ]` over `R'`. It uses `coordinateIso G`, `ψ` and the same model
  isomorphisms.
* `pointChain G ψ A B` (main construction): for every `R'`-algebra `B` with compatible
  `R`-algebra structure, an equivalence

  `(R' ⊗[R] HomAlgebra R 𝒪(G) R[A] →ₐ[R'] B) ≃
     {f : R'[Λ] →ₐ[R'] B ⊗[R'] R'[A] // IsHopfPoint R' f}`.

  It composes `AlgHom.liftEquiv` (maps out of `R' ⊗[R] X` are `R`-maps out of `X`), the
  published `homEquiv` and `pointEquiv` (Hopf points as homomorphisms over `Spec B`),
  `evaluateEquiv (specOverIso B)`, `baseChangeEquiv`, and the published
  `transportEquiv` along `sourceIso` and `targetIso`. It ends with `pointEquiv` over
  `R'`.
* `pointChain_naturality`: for `g : B →ₐ[R'] C`, `pointChain` of `g ∘ φ` is
  `pushPoint R' g` of `pointChain` of `φ`. Each link in the chain is natural. The
  links are the published `pushPoint_pushPoint`, `evaluate_specMap`, `evaluate_comp`
  and `evaluate_transport`, together with `specOverIso_naturality` and
  `baseChangeEquiv_evaluate` from this module.

## Étaleness

* `formallyEtale_tensor_homAlgebra` (needs `ψ`): `R' ⊗[R] HomAlgebra R 𝒪(G) R[A]` is
  formally étale over `R'`. It uses Mathlib's criterion
  `Algebra.FormallyEtale.iff_comp_bijective`: for an `R'`-algebra `B` and an ideal `I`
  with `I² = 0`, composition with `B → B/I` must be bijective on algebra maps. Through
  `pointChain` and its naturality, this map becomes `pushPoint R' (B → B/I)` on Hopf
  points `R'[Λ] → (–) ⊗[R'] R'[A]`. That map is bijective by the published
  `bijective_pushPoint` from `GroupAlgebraHopfPointLift`, since the kernel `I` consists
  of nilpotent elements.
* `etale_homAlgebra` (main theorem; assumes `R → R'` faithfully flat and
  `G.X.hom` locally of finite presentation): `HomAlgebra R 𝒪(G) R[A]` is étale over `R`.
  It is of finite presentation (published instance on `HomAlgebra`, using the published
  `finitePresentation_hopfAlgebra` instance for `𝒪(G)`). Its base change to `R'` is
  étale by the previous item. Mathlib's
  `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat` descends étaleness.

No finiteness or freeness of `Λ` is assumed. The universe of `R`, `R'`, `Λ`, `A` and
all test algebras is the fixed universe `u`.
