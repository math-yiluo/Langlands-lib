# The Weil restriction of `𝔾ₘ` along `A → A^I` is the split torus

Author: Worker 299.

This module identifies the host group scheme `Res_{A^I/A} 𝔾ₘ`
(`Langlands.GroupScheme.WeilGm.groupScheme A (I → A)`, module
`Langlands.GroupScheme.Torus.WeilRestriction`) with the published split torus
`Langlands.GroupScheme.splitTorus (Spec A) I` (module
`Langlands.GroupScheme.Torus.Split`). On points the isomorphism is the unit map
of the canonical isomorphism `(I → A) ⊗[A] T ≃ (I → T)`. All declarations are in
the namespace `Langlands.GroupScheme.WeilGm`.

Throughout, `A : CommRingCat.{u}` and `I : Type u` with `[Finite I]`. The
algebra `I → A` is finite and projective (indeed free) over `A` by Mathlib
instances, so `groupScheme A (I → A)` is defined.

## Sources

- Milne, *Algebraic Groups* (2017), §2.i "Restriction of scalars", 2.60,
  printed p.58 (PDF p.74). Source ID `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Milne:
  "Let A be a product of finite k-algebras, A = k_1 × ··· × k_n. To give an
  algebraic group G over A is the same as giving an algebraic group G_i over
  each k_i. In this case, (G)_{A/k} ≃ (G_1)_{k_1/k} × ··· × (G_n)_{k_n/k}."
  The proof is on points: `(G)_{A/k}(R) = G(A ⊗ R) = G_1(k_1 ⊗ R) × ··· ×
  G_n(k_n ⊗ R)`. Here Milne's `k` is `A`, every `k_i` is `A` (indexed by `I`),
  and `G` is `𝔾ₘ`. Then each factor `(𝔾ₘ)_{A/A}` is `𝔾ₘ`, and the product is the
  split torus `𝔾ₘ^I`.
- TauCeti, Lean source closure at commit
  `8428d6217f74afa72531df0bc85d7b57ab72810f`. Source ID
  `tauceti-8428d621-weil-restriction-closure`. The ported closure (modules
  `Langlands.TauCeti.*`) provides the coordinate algebra of `groupScheme A B` for
  `B` finite projective over a commutative ring `A`.

**Derived generality.** Milne works over a field `k`. This module works over an
arbitrary commutative ring `A` and for a finite index type `I`, and only for
`G = 𝔾ₘ` with every factor equal to `A`. That ring version is derived, not taken
from Milne. The generality of `Res_{B/A} 𝔾ₘ` over a ring is that of the TauCeti
source. The proof follows Milne's argument on points. Points are over
arbitrary test schemes `T : Over (Spec A)`, through the global sections
`Γ(T) = ((algΓ A).obj T).unop`, whose underlying ring is `Γ(T.left, ⊤)`.

## Declarations

- `piTensorEquiv A I T : (I → A) ⊗[A] T ≃ₐ[A] (I → T)`, for a commutative
  `A`-algebra `T`, is the canonical isomorphism. It is tensor commutativity
  followed by Mathlib's `Algebra.TensorProduct.piScalarRight`, which needs a
  `Fintype` instance and decidable equality on `I`; the definition chooses them
  from `[Finite I]` and classical logic. `piTensorEquiv_tmul` (simp, proved by `rfl`): `f ⊗ t ↦ (i ↦ f i • t)`.
- `piTensorEquiv_natural`: for a map `φ : T →ₐ[A] T'` of `A`-algebras, the
  isomorphism for `T'` composed with `id ⊗ φ` sends `w` to
  `i ↦ φ (piTensorEquiv A I T w i)`.
- `splitPointsEquiv A I T : (T ⟶ (groupScheme A (I → A)).X) ≃* (I → Γ(T.left, ⊤)ˣ)`
  is the composite of the host `pointsEquiv A (I → A) T`, with values in
  `((I → A) ⊗[A] Γ(T))ˣ`, the unit map of `piTensorEquiv`, and Mathlib's
  `MulEquiv.piUnits : (I → Γ(T))ˣ ≃* (I → Γ(T)ˣ)`. `splitPointsEquiv_apply`
  (proved by `rfl`) gives its `i`-th coordinate.
- `splitPointsEquiv_naturality`: for `a : T' ⟶ T` in `Over (Spec A)`,
  `splitPointsEquiv A I T' (a ≫ x)` is `splitTorus.unitsRestrict I a` of
  `splitPointsEquiv A I T x`, that is, `a.left.appTop` applied to every unit.
  The proof uses the host `pointsEquiv_naturality` and `piTensorEquiv_natural`.
- `splitIso A I : groupScheme A (I → A) ≅ splitTorus (Spec A) I` is an
  isomorphism of group schemes over `Spec A`. It is built with the published
  `isoOfPointModels`. The common point model is `T ↦ (I → Γ(T.left, ⊤)ˣ)`
  with restriction maps `splitTorus.unitsRestrict`. One side is
  `splitPointsEquiv`, the other the published `splitTorus.pointsEquiv I`.
- `splitIso_hom_points`: for every test scheme `T` and point
  `x : T ⟶ (groupScheme A (I → A)).X`,
  `splitTorus.pointsEquiv I T (x ≫ (splitIso A I).hom.hom.hom)` is
  `MulEquiv.piUnits` of the unit map of `piTensorEquiv A I Γ(T)` applied to
  `pointsEquiv A (I → A) T x`. So on points the isomorphism is the unit map of
  `(I → A) ⊗[A] Γ(T) ≃ (I → Γ(T))`. `MulEquiv.piUnits` only rewrites a unit of
  `I → Γ(T)` as a family of units, the point model of `splitTorus`.

## Scope

This module does not treat products `k_1 × ··· × k_n` of different algebras or
group schemes other than `𝔾ₘ`. It does not treat splitting of `Res_{L/K} 𝔾ₘ`
over a field that splits `L`.
