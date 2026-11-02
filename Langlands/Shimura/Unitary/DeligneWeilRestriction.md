# The Deligne torus is the Weil restriction `Res_{ℂ/ℝ} 𝔾ₘ`

Author: Worker 299.

This module identifies the host Weil restriction
`Langlands.GroupScheme.WeilGm.groupScheme (CommRingCat.of ℝ) ℂ` (module
`Langlands.GroupScheme.Torus.WeilRestriction`) with the published Deligne torus
`Langlands.Shimura.DeligneTorus.groupScheme` (module
`Langlands.Shimura.Unitary.DeligneGroupScheme`). Both are group schemes over
`Spec ℝ`. On the points over a real algebra `S` the isomorphism is the unit map
of the `ℝ`-algebra isomorphism `ℂ ⊗[ℝ] S ≃ Complexification S` sending `z ⊗ s`
to `s • complexMap S z`. All declarations are in the namespace
`Langlands.Shimura.DeligneTorus`.

Here `Complexification S` is the published `QuadraticAlgebra S (-1) 0` (module
`Langlands.Shimura.Unitary.Deligne`), with elements `a + b i` and `i² = -1`.
`Points S` is its unit group, and `complexMap S : ℂ →ₐ[ℝ] Complexification S`
is the canonical map. Real algebras `S` are in `Type`, the universe of
`DeligneTorus.groupScheme`.

## Sources

- Milne, *Introduction to Shimura varieties*, Section 2, printed p.282 (PDF
  p.294), in Arthur, Ellwood and Kottwitz (eds.), *Harmonic Analysis, the Trace
  Formula, and Shimura Varieties* (2005). Source ID
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
  `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`: "Let S be
  C× regarded as a torus over R. It can be identified with the closed subgroup
  of GL_2(R) of matrices of the form (a b; −b a)." The matrices
  `(a b; −b a)` are the quadratic model `a + b i` of `Complexification`.
- Milne, *Algebraic Groups* (2017), §2.i "Restriction of scalars", 2.55,
  printed p.57 (PDF p.73). Source ID `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  `(G)_{A/k}` is "the algebraic group over k such that (G)_{A/k}(R) = G(A ⊗ R)
  for all k-algebras R". For `k = ℝ`, `A = ℂ` and `G = 𝔾ₘ` this is
  `S ↦ (ℂ ⊗[ℝ] S)ˣ`, the functor of the host `groupScheme (CommRingCat.of ℝ) ℂ`.
  "C× regarded as a torus over R" is this Weil restriction.

**Derived content.** Milne gives the torus `S` by its real points and a matrix
model. He does not state a comparison isomorphism. The isomorphism here is
derived: both group schemes have point models over every test scheme, and the
tensor identity `ℂ ⊗[ℝ] S ≃ Complexification S` matches them. The host
`Res_{ℂ/ℝ} 𝔾ₘ` is built from the TauCeti coordinate algebra (source ID
`tauceti-8428d621-weil-restriction-closure`, TauCeti commit
`8428d6217f74afa72531df0bc85d7b57ab72810f`); `ℂ` is finite free over `ℝ`.

## The algebraic comparison

In this section `S : Type` is a commutative ring with `[Algebra ℝ S]`.

- `complexTensorEquiv S : ℂ ⊗[ℝ] S ≃ₐ[ℝ] Complexification S` is the tensor
  commutativity isomorphism `ℂ ⊗[ℝ] S ≃ S ⊗[ℝ] ℂ` followed by the inverse of the
  published `tensorEquiv S : Complexification S ≃ₐ[S] S ⊗[ℝ] ℂ`, with scalars
  restricted to `ℝ`.
- `complexTensorEquiv_tmul` (simp, proved by `rfl`):
  `z ⊗ s ↦ s • complexMap S z`.
- `complexTensorEquiv_mul_tmul`: `e (x * (1 ⊗ s)) = s • e x`. So the isomorphism
  is `S`-linear for the action of `S` on the right tensor factor. That
  `S`-algebra structure on `ℂ ⊗[ℝ] S` is not a Mathlib instance, so this lemma
  states that `complexTensorEquiv S` is an isomorphism of `S`-algebras.
- `complexTensorEquiv_natural`: for a map `φ : S →ₐ[ℝ] T` of real algebras,
  `complexTensorEquiv T` composed with `id_ℂ ⊗ φ` equals
  `map φ.toRingHom` (coefficientwise `φ` on `Complexification`) composed with
  `complexTensorEquiv S`. The proof is by induction on tensors, comparing real
  and imaginary parts.

## The group-scheme isomorphism

Test schemes are `T : Over (Spec (CommRingCat.of ℝ))`, with global sections
`Γ(T) = ((algΓ (CommRingCat.of ℝ)).obj T).unop`.

- `weilPointsEquiv T` is a multiplicative equivalence from the points over `T`
  of the host `groupScheme (CommRingCat.of ℝ) ℂ` to `Points Γ(T)`. It is the
  host `pointsEquiv`, with values in `(ℂ ⊗[ℝ] Γ(T))ˣ`, followed by the unit map
  of `complexTensorEquiv Γ(T)`.
- `deligneSchemePointsEquiv T : (T ⟶ groupScheme.X) ≃* Points Γ(T)` is an
  abbreviation for the published `GroupScheme.Corepresented.pointsEquiv` of
  `DeligneTorus.functor` and `DeligneTorus.corepresentableBy`, the data that
  define `DeligneTorus.groupScheme`.
- `weilPointsEquiv_naturality`: for `a : T' ⟶ T`, `weilPointsEquiv T' (a ≫ x)`
  is the image of `weilPointsEquiv T x` under `DeligneTorus.functor.map` of
  `Γ(a)`, the coefficientwise unit map. The proof uses the host
  `pointsEquiv_naturality` and `complexTensorEquiv_natural`.
- `weilRestrictionIso : groupScheme (CommRingCat.of ℝ) ℂ ≅ groupScheme` (the
  right side is `DeligneTorus.groupScheme`) is an isomorphism of group schemes
  over `Spec ℝ`. It is built with the published `GroupScheme.isoOfPointModels`
  (`Langlands.GroupScheme.Torus.Split`). The common point model is
  `T ↦ Points Γ(T)`, with restriction maps from `DeligneTorus.functor`. One
  side is `weilPointsEquiv`, the other `deligneSchemePointsEquiv`, natural by
  the published `Corepresented.pointsEquiv_naturality`.
- `weilRestrictionIso_hom_points`: for every test scheme `T` and point `x` of
  the host Weil restriction, `deligneSchemePointsEquiv T (x ≫
  weilRestrictionIso.hom.hom.hom)` is the image of the host
  `pointsEquiv (CommRingCat.of ℝ) ℂ T x` under the unit map of
  `complexTensorEquiv Γ(T)`. For an affine test scheme `Spec S`, `Γ(T)` is `S`
  up to the canonical isomorphism `Γ(Spec S) ≅ S`.

## Scope

This module does not compare the inversion map, the norm or the weight
homomorphism of the Deligne torus with constructions on the Weil restriction.
