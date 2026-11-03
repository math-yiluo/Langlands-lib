# Rational points of torsors from Lang's theorem

Module `Langlands.GroupScheme.FiniteFieldTorsorPoint.TorsorAction`. These are internal
helper results for the proof of `Langlands.GroupScheme.FiniteFieldTorsorPointStatement`.
They reduce that statement to Lang's theorem for the group of points over the algebraic
closure. The reduction is the standard argument, as in Lang, *Algebraic groups over
finite fields* (1956). Serre, *Galois Cohomology*, III §2.3 (printed p. 132), reports
Lang's result that `x ↦ x⁻¹ F(x)` is surjective. The module adds no statements,
definitions or axioms.

Group schemes are the Library's `GroupScheme S = Grp (Over S)`. Their points
`Z ⟶ H.X` form a group under Mathlib's `Hom.group` (scoped in `CategoryTheory.MonObj`).
An action `[ModObj H.X X]` makes them act on `Z ⟶ X` through `Hom.mulAction`,
`h • x = lift h x ≫ γ`. The shear map is Mathlib's `ModObj.leftSMul H.X X`,
`(h, x) ↦ (h • x, x)`, and the binary product in `Over S` is the scheme pullback.

## `locallyOfFiniteType_of_isIso_leftSMul`

Let `H` be a group scheme over a scheme `S` whose structure map is locally of finite
type. Let `X` be a scheme over `S` with an action of `H`. Suppose `X → S` is flat,
surjective and quasi-compact, and the shear map is an isomorphism. Then `X → S` is
locally of finite type.

Proof in Lean. Mathlib's `ModObj.leftSMul_snd` says that the shear map followed by the
second projection `X ×_S X → X` is the second projection `H ×_S X → X`. On underlying
schemes the latter is `pullback.snd H.X.hom X.hom`, a base change of `H → S`, so it is
locally of finite type. The underlying scheme map of the shear is an isomorphism. Hence
`pullback.snd X.hom X.hom` equals the inverse of the shear followed by
`pullback.snd H.X.hom X.hom`, and is locally of finite type. It is the base change of
`X → S` along the fpqc map `X → S`. Mathlib's fpqc descent of local finite type
(`DescendsAlong @LocallyOfFiniteType (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`, with
`MorphismProperty.of_pullback_snd_of_descendsAlong`) gives the claim.

## `torsor_point_of_lang`

Let `k` be a finite field, `K = AlgebraicClosure k`, and let `F = ringTestMap k Fr` be
the endomorphism of `Spec K` over `Spec k` induced by the `q`-power Frobenius
`Fr = FiniteField.frobeniusAlgHom k K`. Let `H` be a group scheme over `Spec k` whose
structure map is locally of finite type. Let `X` be a scheme over `Spec k` with an
`H`-action, with `X → Spec k` flat, surjective and quasi-compact and the shear map an
isomorphism. Assume `hLang`: every `K`-point `a` of `H` can be written as
`a = g⁻¹ * (F ≫ g)` for some `K`-point `g`. Then `X` has a `k`-point:
`Nonempty (RingPoint k X k)`.

`hLang` is a premise of this helper theorem. It is not a premise of the final statement:
the final proof derives it from Lang's theorem for smooth connected affine `H`.

Proof in Lean.

1. `X → Spec k` is locally of finite type by `locallyOfFiniteType_of_isIso_leftSMul`.
   `X` is nonempty because `X → Spec k` is surjective. So
   `nonempty_ringPoint_of_locallyOfFiniteType` gives a `K`-point `p₀` of `X`.
2. Mathlib's `ModObj.isIso_leftSMul_iff` says that the shear is an isomorphism exactly
   when, for every test object, any two points of `X` differ by a unique point of `H`.
   Applied to `p₀` and `F ≫ p₀`, it gives `a` with `a • p₀ = F ≫ p₀`. Only existence
   is used.
3. Apply `hLang` to `a⁻¹`, giving `g` with `a⁻¹ = g⁻¹ * (F ≫ g)`, that is,
   `F ≫ g = g * a⁻¹`.
4. Let `p = g • p₀`. Then `F ≫ p = (F ≫ g) • (F ≫ p₀)` (`ModObj.comp_smul`), which is
   `(g * a⁻¹) • (a • p₀) = g • p₀ = p`. So `p` is fixed by Frobenius, and
   `nonempty_ringPoint_of_frobenius_fixed` gives a `k`-point of `X`.
