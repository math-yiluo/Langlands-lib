# Base change of the Weil restriction `Res_{B/A} 𝔾ₘ`

Author: Worker 299.

This module proves that the host group scheme `Res_{B/A} 𝔾ₘ`
(`Langlands.GroupScheme.WeilGm.groupScheme A B`, module
`Langlands.GroupScheme.Torus.WeilRestriction`) commutes with base change. For
a ring map `f : A ⟶ A'`, the base change of `groupScheme A B` along
`Spec.map f` is isomorphic to `groupScheme A' (A' ⊗[A] B)`, and on points the
isomorphism is the unit map of the canonical isomorphism
`B ⊗[A] T ≃ (A' ⊗[A] B) ⊗[A'] T`. All declarations are in the namespace
`Langlands.GroupScheme.WeilGm`.

Throughout, `A, A' : CommRingCat.{u}`, and `B : Type u` is a commutative
`A`-algebra with `[Module.Finite A B] [Module.Projective A B]`. No other
hypotheses are used. The algebra `A' ⊗[A] B` is finite projective over `A'`
by the Mathlib instances for base change. This is what `groupScheme A' (A' ⊗[A] B)`
needs.

## Sources

- Milne, *Algebraic Groups* (2017), §2.i "Restriction of scalars", 2.59,
  printed p.58 (PDF p.74). Source ID `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Milne
  works over a field `k` with `A` a finite `k`-algebra: "For any field K
  containing k and algebraic group G over A, (Π_{A/k} G)_K ≃ Π_{A⊗_k K/K}(G_K);
  in other words, Weil restriction commutes with extension of scalars." The
  proof is on points: for a `K`-algebra `R`,
  `(Π_{A/k} G)_K(R) = G(A ⊗_k R) ≃ G(A ⊗_k K ⊗_K R) = Π_{A⊗_k K/K}(G_K)(R)`,
  "because A ⊗_k R ≃ A ⊗_k K ⊗_K R". Here Milne's `k`, `A`, `K`, `R` and `G`
  are `A`, `B`, `A'`, `T` and `𝔾ₘ`.
- TauCeti, Lean source closure at commit
  `8428d6217f74afa72531df0bc85d7b57ab72810f`. Source ID
  `tauceti-8428d621-weil-restriction-closure`. The ported closure (modules
  `Langlands.TauCeti.*`) provides the coordinate algebra
  `WeilRestriction A B B[T;T⁻¹]` of `groupScheme A B` for `B` finite projective
  over a commutative ring `A`.

**Derived generality.** Milne's statement is for a field extension `K/k` and a
finite algebra over a field. This module proves it for an arbitrary ring map
`f : A ⟶ A'` and `B` finite projective over `A`, for `G = 𝔾ₘ` only. That ring
version is derived, not taken from Milne. The generality of `Res_{B/A} 𝔾ₘ` over
a ring is that of the TauCeti source. The proof follows Milne's argument on
points, with the same tensor identity. It does not use TauCeti's base-change
isomorphism `WeilRestriction.baseChangeAlgEquiv` of coordinate algebras.
Milne's points are over `K`-algebras, that is, affine test schemes. Here they
are over arbitrary test schemes `T : Over (Spec A')`, through the global sections
`Γ(T) = ((algΓ A').obj T).unop`.

## The algebraic comparison

In this section `A, A', B, R : Type u` are commutative rings with algebras
`A → A'`, `A → B`, `A' → R`, `A → R` and `[IsScalarTower A A' R]`.

- `baseChangeTensorEquiv A A' B R : B ⊗[A] R ≃+* (A' ⊗[A] B) ⊗[A'] R` is the
  ring isomorphism of Milne's identity. It is the composite of Mathlib's tensor
  commutativity `B ⊗[A] R ≃ R ⊗[A] B`, the inverse of
  `Algebra.TensorProduct.cancelBaseChange`, `R ⊗[A] B ≃ R ⊗[A'] (A' ⊗[A] B)`,
  and tensor commutativity `R ⊗[A'] (A' ⊗[A] B) ≃ (A' ⊗[A] B) ⊗[A'] R`.
- `baseChangeTensorEquiv_tmul` (simp): `b ⊗ r ↦ (1 ⊗ b) ⊗ r`.
- `baseChangeTensorEquiv_mul_tmul`: `e (x * (1 ⊗ r)) = e x * (1 ⊗ r)`. So the
  isomorphism is `R`-linear when both sides are `R`-algebras through their right
  tensor factors. These `R`-algebra structures are not Mathlib instances, so the
  isomorphism is stated as a ring isomorphism together with this lemma. This is
  the sense in which it is the canonical isomorphism of `T`-algebras of the task.
- `baseChangeTensorEquiv_natural`: compatibility with a map `φ : R →ₐ[A'] R'`
  of `A'`-algebras. `ψ : R →ₐ[A] R'` is the same map regarded as a map of
  `A`-algebras (hypothesis `∀ r, ψ r = φ r`). Then the isomorphism for `R'`
  composed with `id_B ⊗ ψ` equals `id_{A' ⊗[A] B} ⊗ φ` composed with the
  isomorphism for `R`. The proof is by induction on tensors.

## The group-scheme isomorphism over an algebra `A → A'`

In this section `A, A' : CommRingCat.{u}` with `[Algebra A A']`.

- `baseMap A A' : Spec A' ⟶ Spec A` is `Spec.map` of `algebraMap A A'`.
- `restrictedSections A A' T : CommAlgCat A`, for `T : Over (Spec A')`, is the
  `A`-algebra of global sections of `T` regarded over `Spec A` through
  `baseMap A A'` (by `Over.map`). Its underlying ring is `Γ(T.left, ⊤)`.
- The instance `restrictedSectionsAlgebra` gives it the `A'`-algebra structure
  of `((algΓ A').obj T).unop`. The instance `restrictedSectionsScalarTower`
  proves `IsScalarTower A A' (restrictedSections A A' T)`. Its proof uses the
  naturality `Scheme.ΓSpecIso_inv_naturality` of `Γ(Spec R) ≅ R`.
- `basePointsEquiv A A' B T` is a multiplicative equivalence from the points
  over `T` of `(GroupScheme.baseChange (baseMap A A')).obj (groupScheme A B)`
  to `((A' ⊗[A] B) ⊗[A'] Γ(T))ˣ`. It is the composite of
  `GroupScheme.baseChangePointsEquiv` (module
  `Langlands.AbelianScheme.KernelBaseChange`), which identifies these points with
  the points of `groupScheme A B` over `T` regarded over `Spec A`. Then comes the
  host `pointsEquiv A B`, with values in `(B ⊗[A] Γ(T))ˣ`, and finally the unit
  map of `baseChangeTensorEquiv A A' B (restrictedSections A A' T)`.
  `basePointsEquiv_apply` (proved by `rfl`) unfolds this composite.
- `basePointsEquiv_naturality`: for `a : T' ⟶ T` in `Over (Spec A')`,
  `basePointsEquiv A A' B T' (a ≫ x)` is the image of
  `basePointsEquiv A A' B T x` under the unit map of `id_{A' ⊗[A] B} ⊗ Γ(a)`.
  Here `Γ(a) = ((algΓ A').map a).unop.hom`. The proof combines
  `baseChangePointsEquiv_naturality`, the host `pointsEquiv_naturality` and
  `baseChangeTensorEquiv_natural`. The last step uses
  `set_option backward.isDefEq.respectTransparency false` for that one tactic,
  so that the two `A'`-algebra structures on the global sections unify.
- `algebraBaseChangeIso A A' B` is an isomorphism of group schemes over `Spec A'`
  from `(GroupScheme.baseChange (baseMap A A')).obj (groupScheme A B)` to
  `groupScheme A' (A' ⊗[A] B)`. It is built with `isoOfPointModels`
  (`Langlands.GroupScheme.Torus.Split`). The common point model is
  `T ↦ ((A' ⊗[A] B) ⊗[A'] Γ(T))ˣ`, with restriction maps the unit maps of
  `id ⊗ Γ(a)`. One side is `basePointsEquiv`, the other the host
  `pointsEquiv A' (A' ⊗[A] B)`.
- `algebraBaseChangeIso_hom_points`: for a point `x` of the base change over `T`,
  `pointsEquiv A' (A' ⊗[A] B) T (x ≫ (algebraBaseChangeIso A A' B).hom.hom.hom)`
  is the image under the unit map of `baseChangeTensorEquiv` of
  `pointsEquiv A B` applied to `baseChangePointsEquiv x`.

## Base change along a ring map

In this section `f : A ⟶ A'` is a morphism in `CommRingCat.{u}`. Statements
that need `A'` as an `A`-algebra use `f.hom.toAlgebra` locally, as in the task.

- `baseChangeIso f B` is an isomorphism of group schemes over `Spec A'` from
  `(GroupScheme.baseChange (Spec.map f)).obj (groupScheme A B)` to
  `groupScheme A' (A' ⊗[A] B)`. It is `algebraBaseChangeIso A A' B` for the
  algebra structure of `f`. Then `Spec.map f` is definitionally `baseMap A A'`.
- `baseChangeIso_hom_points`: for `T : Over (Spec A')` and a point `x` of the
  base change over `T`,
  `pointsEquiv A' (A' ⊗[A] B) T (x ≫ (baseChangeIso f B).hom.hom.hom)` equals
  the image under the unit map of `baseChangeTensorEquiv A A' B Γ(T)` of
  `pointsEquiv A B ((Over.map (Spec.map f)).obj T)` applied to
  `baseChangePointsEquiv (Spec.map f) (groupScheme A B) T x`. So on points the
  isomorphism is the unit map of the canonical isomorphism
  `B ⊗[A] Γ(T) ≃ (A' ⊗[A] B) ⊗[A'] Γ(T)`.

  The proof rewrites with two private lemmas, proved by `rfl`:
  `baseChangeIso_points_eq` (`baseChangeIso f B` and `algebraBaseChangeIso` act
  in the same way on points) and `basePoints_specMap_eq` (the right-hand side
  agrees with its `baseMap A A'` form). Then it applies
  `algebraBaseChangeIso_hom_points`. Closing the goal with
  `algebraBaseChangeIso_hom_points` directly makes elaboration exceed the
  maximum recursion depth.

## Scope

This module treats only `𝔾ₘ` and only base change of the host group scheme
`groupScheme A B`. It does not state the compatibility of TauCeti's
coordinate-algebra base change `baseChangeAlgEquiv` with this isomorphism.
