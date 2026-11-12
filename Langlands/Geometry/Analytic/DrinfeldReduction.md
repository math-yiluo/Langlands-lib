# Norms on coefficient vectors and the reduction map of Drinfeld's upper half space

Author: Worker 21.

This module constructs the reduction map `Res : Ω → BT` from Drinfeld's upper
half space to the space of norms on `F^{d+1}` up to homothety. It proves that
the map is continuous and `GL_{d+1}(F)`-equivariant. It contains:

- `VectorNorm F V`: ultrametric norms on an `F`-vector space `V`, in
  multiplicative form; homothety of norms; the space `NormClass F V` of norms up
  to homothety;
- the action of `GL_n(F)` on norms of row vectors and on their classes;
- `DrinfeldUpperHalfSpace.reduction`, which sends a point `z` of `Ω` to the
  class of the norm `a ↦ |ℓ_a(z)|`;
- triviality of the action of scalar matrices on `Ω` and on norm classes, so
  that both actions factor through `PGL_{d+1}(F)`.

The facets of the building, the neighbourhoods `B(e, ε)` and the domains
`U(e) = Res⁻¹(B(e, ε))` are not treated here (see Scope).

All declarations lie in `Langlands.Analytic`. The reduction map uses the
hypotheses of `DrinfeldUpperHalfSpace`; equivariance also uses
`ProperSpace F` and `NeZero d`, as the group action does.

## Original sources and derived provenance

Bruhat–Tits, *Schémas en groupes et immeubles des groupes classiques sur un
corps local*, Bull. Soc. Math. France 112 (1984), registered as
`bruhat-tits-1984-schemas-groupes-classiques`, SHA256
`1a92f21114a9142ebde0341e2047e044349dea47bba4daab5d34d1a155398076`:

- 1.1, printed p.262 / PDF p.5: "Une D-norme ou plus simplement une norme sur
  X est une application α : X → ℝ ∪ {+∞} telle que l'on ait, pour x, y ∈ X et
  t ∈ D, (1) α(xt) = α(x) + ω(t), (2) α(x + y) ≥ inf(α(x), α(y)), (3)
  α(x) = +∞ si et seulement si x = 0."
- 1.5(i), printed p.264 / PDF p.7: "si D est complet, toute norme est
  scindable."
- 2.11, printed p.283 / PDF p.26: "Soit 𝒩 l'ensemble des normes scindables sur
  X. (i) L'application p ↦ α_p se prolonge d'une manière et d'une seule en une
  application j de l'immeuble élargi ℐ¹ de G dans 𝒩 covariante par G … (ii)
  L'application j est bijective … et à (13) j(x + v) = j(x) − a₀(v) pour
  x ∈ ℐ¹ et v ∈ V¹."

So for a complete field `F` the extended building of `GL(X)` is the set of all
norms on `X`. By (13), translations by `V¹` add constants to a norm, so the
building of `PGL(X)`, the quotient of `ℐ¹` by `V¹`, is the set of norms
modulo additive constants.

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper half
spaces* (1997), registered as `harris-1997-drinfeld-cohomology`, §2, printed
p.90 / PDF p.16: "There is a GJ^ad-equivariant map Res: Ω → BT; the factors
GJ(K_1^{(j)}) act trivially on both sides, for j > 1." Harris gives no formula
for `Res`.

Drinfel'd, *Coverings of p-adic symmetric regions* (1976), registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`, printed
p.107 / PDF p.1: "Ω^d is a strict analytic space over K, on which PGL(d, K)
acts (see [1])." Harris 1997, §2, printed p.88 / PDF p.14, likewise speaks of
"the natural action of GJ^ad ≃ PGL(n, F_v) on Ω". The triviality of scalar
matrices proved below is what makes the action of `GL_{d+1}(F)` from
`DrinfeldGroupAction` factor through `PGL_{d+1}(F)`.

Derived choices:

- A norm is written multiplicatively, `ν = q^{−α}`, where `q > 1` and
  `‖t‖ = q^{−ω(t)}` on `F`. Bruhat–Tits' axioms (1)–(3) become
  `ν(t x) = ‖t‖ ν(x)`, `ν(x + y) ≤ max(ν(x), ν(y))` and `ν(x) > 0` for
  `x ≠ 0`. Adding a constant to `α` multiplies `ν` by a positive constant, so
  the building of `PGL` corresponds to `NormClass`. The identification with
  the building (Bruhat–Tits 2.11 and 1.5) is not formalized here.
- `Res(z)` is the class of `a ↦ |ℓ_a(z)|`, where `ℓ_a = a₀ + Σ aᵢ₊₁ Tᵢ`. In
  homogeneous coordinates `ẑ = (1 : z₁ : ⋯ : z_d)`, this is `a ↦ |a · ẑ|`, a
  norm on the dual space of `F^{d+1}`. The norm is positive on nonzero `a`
  because `z` lies on no `F`-rational hyperplane.
- `GL_n(F)` acts on row vectors by the contragredient action `a ↦ a γ⁻¹`, so on
  norms by `(γ • ν)(a) = ν(a γ)`. This is Bruhat–Tits' covariance
  `(gα)(x) = α(g⁻¹x)` for the dual representation.
- `NormClass` carries the quotient of the topology of pointwise convergence on
  `V`. This topology is not compared here with the metric topology of the
  building.

## Norms

- `VectorNorm F V`, with `pos`, `map_smul`, `add_le_max`, `map_zero` and
  `nonneg`.
- `Homothetic ν μ`: `μ = c ν` for some `c > 0`. It is an equivalence relation
  (`Homothetic.refl`, `.symm`, `.trans`, `homotheticSetoid`).
- `NormClass F V := Quotient (homotheticSetoid F V)`.
- The topology on `VectorNorm F V` is induced from the product topology on
  functions `V → ℝ`.

## The action of invertible matrices

For a finite index type `n`:

- `VectorNorm.vecMul_ne_zero`: `a γ ≠ 0` for `a ≠ 0` and `γ` invertible.
- `comapMatrix ν γ`: the norm `a ↦ ν(a γ)`.
- A `MulAction` of `GL_n(F)` on `VectorNorm F (n → F)` by
  `(γ • ν)(a) = ν(a γ)` (`smul_apply`). The action laws are
  `a 1 = a` and `a (γ γ') = (a γ) γ'`.
- `Homothetic.smul`: the action preserves homothety, so it descends to a
  `MulAction` on `NormClass F (n → F)` (`NormClass.smul_mk`).

## The reduction map

In `DrinfeldUpperHalfSpace`:

- `coefficients_add`, and for points `z` of the affine space:
  `linearNorm_nonneg`; `linearNorm_add_le` (the strong triangle inequality,
  from the existing `BanachSpectrum.isNonarchimedean`);
  `linearNorm_coefficients_smul` (`|ℓ_{t a}| = ‖t‖ |ℓ_a|`, from
  `linearForm_smul` and `BanachSpectrum.algebraMap_apply`).
- `omegaNorm K z : VectorNorm F (Fin (d + 1) → F)` for `z ∈ Ω`:
  `a ↦ |ℓ_a(z)|` (`omegaNorm_apply`). `continuous_omegaNorm`: it is continuous
  in `z`, because each `z ↦ |ℓ_a(z)|` is (`continuous_linearNorm`).
- `reduction K z := ⟦omegaNorm K z⟧ : NormClass F (Fin (d + 1) → F)`.
  `continuous_reduction`.
- `omegaNorm_actionMap`: for a chart point `z` of a member `U` of the exhaustion,
  `|ℓ_a(γ · z)| = |ℓ_{γ_0}(z)|⁻¹ · |ℓ_{a γ}(z)|`. The factor
  `|ℓ_{γ_0}(z)|⁻¹` is the value at `z` of the inverse of `ℓ_{γ_0}` on `U`
  (`linearNorm_actionPoint`).
- `reduction_actionMap`: `Res(γ · z) = γ • Res(z)`. The two norms differ by the
  positive factor `|ℓ_{γ_0}(z)|⁻¹` (`inverse_apply_ne_zero`).

## Scalar matrices

For `γ` with `γ = c · 1` as a matrix:

- `scalar_ne_zero`: `c ≠ 0`.
- `coefficients_entries_scalar`: the rows of `γ` are `c e_k`.
- `actionTuple_scalar`: the image of `Tᵢ` is
  `ℓ_{c e_{i+1}} / ℓ_{c e_0} = c Tᵢ / c = Tᵢ`. The inverse of `ℓ_{c e_0} = c` is
  `c⁻¹` (`eq_inverse_of_mul_eq_one`).
- `actionMap_eq_self` and `compatibleHom_eq_id`: a matrix whose pullback on
  every member of the exhaustion is the identity acts as the identity map and
  as the identity compatible strong map. The proof follows `compatibleHom_one`.
- `compatibleHom_scalar` and `omegaAction_ρ_scalar`: scalar matrices act as the
  identity on `Ω`, in the localized category as well.
- `smul_normClass_scalar`: scalar matrices fix every class of norms, since
  `ν(a · c 1) = ‖c‖ ν(a)`.

## Scope

Not done here:

- the identification of `NormClass F (Fin (d + 1) → F)` with the building in the
  sense of Bruhat–Tits, and its metric and simplicial structure (vertices as
  lattice classes, facets as lattice chains);
- the neighbourhoods `B(e, ε)` of Harris 1997 p.90, the domains
  `U(e) = Res⁻¹(B(e, ε))`, their distinguishedness and their stabilizers;
- the actions as actions of the quotient group `PGL_{d+1}(F)` (only the
  triviality of scalar matrices is proved).
