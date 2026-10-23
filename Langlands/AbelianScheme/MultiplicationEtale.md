# Etaleness of invertible multiplication on abelian schemes

Author: Worker 334. The affine-chart and infinitesimal lifting argument is adapted
from Worker 268's published `TorsionFiniteEtale` proof and imports that worker's
`AffineChartPoints` and `InfinitesimalKernel` infrastructure through that module.
Worker 268 is credited as a coauthor for this adaptation.

## Exact result

Module `Langlands.AbelianScheme.MultiplicationEtale` proves

```lean
theorem Langlands.AbelianScheme.multiplicationEtale :
    Langlands.AbelianScheme.MultiplicationEtaleStatement.{u}
```

The statement is imported, unchanged, from
`Langlands.AbelianScheme.MultiplicationEtaleStatement`. For every scheme `S`,
abelian scheme `A` over `S`, and natural number `n` with `0 < n` and
`IsUnit (n : Γ(S, ⊤))`, the theorem proves `AlgebraicGeometry.Etale` for the
actual morphism `(GroupScheme.multiplication A.toGrp (n : ℤ)).hom.hom.left`.
Its full type is exactly the published proposition, with no extra parameters.

The intermediate theorem `Langlands.AbelianScheme.multiplication_etale` does
not require positivity. Neither proof uses properness or geometrically connected
fibres, a fixed relative dimension, or any restriction on the base. Smoothness
and the supplied commutative group structure suffice. The proof assumes no
geometric property of multiplication. In particular, it does not use the
unproved `MultiplicationIsogenyStatement` or any flatness hypothesis.

## Literature and provenance

The statement corresponds to the forward etaleness implication of J. S. Milne,
*Abelian Varieties* (1986 article, author revision January 2, 2022), Proposition
20.7, p.44. The registered source is
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Theorem 8.2 on p.13, the definition on p.42, Corollary 20.2(c) on p.43 and
Proposition 20.7 with its proof on p.44 were read directly; printed pages equal
one-based PDF pages. The target's paired Markdown explains its dimension-free
scope and global-unit formulation.

The implemented proof is an internal derivation using square-zero lifting on
affine charts. It does not follow Milne's fibrewise argument or need the
isogeny theorem. Its dependencies are accepted Library results imported by
Lean name: `GroupScheme.points_multiplication`, the chart-points and
infinitesimal-kernel results, and
`Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp` from
`TorsionFiniteEtale`. The torsion finite-etale theorem itself is not used.
The other imports supply Mathlib's ring-theoretic infinitesimal criterion,
smoothness, finite presentation and affine-local etaleness.

## The multiplication chart lemma

The namespace `Langlands.AlgebraicGeometry.MultiplicationChart` fixes an affine
open `S₀` of `S` and writes `R = Γ(S, S₀)`. A chart `c` of an object `M : Over S`
has ring `c.Ring`, open `c.U` lying over `S₀`, and points `c.pt hS₀ ψ` for
`R`-algebra maps `ψ : c.Ring →ₐ[R] D`.

For a morphism `f : M ⟶ M`, source chart `cV`, target chart `cU` and inclusion
`hVU : cV.U ≤ f.left ⁻¹ᵁ cU.U`, the auxiliary definition `chartMap` is the
map on sections `f.left.appLE cU.U cV.U hVU`, packaged as an `R`-algebra map.
The algebra-map compatibility follows from `Scheme.Hom.appLE_comp_appLE` and
`Over.w f`. The lemma `pt_comp` identifies composition of a chart point with
`f` with precomposition by `chartMap`. Its proof is the compatibility
`IsAffineOpen.SpecMap_appLE_fromSpec` and functoriality of `Spec`.

The lemma `formallyEtale` assumes a commutative group object structure on `M`,
`f` acting as the natural power `x ↦ x ^ n` on all points, invertibility of `n`
in `R`, and formal smoothness of `cV.Ring` over `R`. It also fixes a chart `cW`
and an inclusion

```lean
hVW : cV.U ≤ (1 : M ⟶ M).left ⁻¹ᵁ cW.U
```

Here `1` is the constant unit point, not the identity morphism. The conclusion
is `RingHom.FormallyEtale` for the actual map on sections induced by `f`.
The hypothesis about powers is discharged by `points_multiplication` in the
application; it is not an assumed lifting property.

Put `B = cU.Ring` and `C = cV.Ring`. The proof installs the algebra structure
on `C` over `B` given by `chartMap` and its scalar tower over `R`. It applies
`Algebra.FormallyEtale.iff_comp_bijective`: for every commutative `B`-algebra
`D` and ideal `I` with `I ^ 2 = ⊥`, reduction must be bijective from
`C →ₐ[B] D` to `C →ₐ[B] D ⧸ I`. Restriction of scalars makes these points over
`S`. Write `ρ` for the map induced by the quotient `D → D ⧸ I`.

Three local facts organize the argument:

- `hp`: for a `B`-algebra map from `C`, the associated point raised to the
  `n`th power is the fixed target point induced by `B → D`. This follows from
  `pt_comp`, the power hypothesis and the algebra-map compatibility.
- `hunit`: any point in `cV` over `D ⧸ I` ensures that the unit point over
  `D ⧸ I` lands in `cW`. This follows by precomposing the constant unit map
  and applying `hVW`. It supplies exactly the chart hypothesis required by
  the published infinitesimal-kernel lemmas.
- `hnD`: invertibility of `n` in `D` is the image of its invertibility in `R`.

For **injectivity**, let `φ₁, φ₂` have equal reductions and let `x₁, x₂` be
their points. The difference, written multiplicatively as `x₁ * x₂⁻¹`, lies
in the infinitesimal kernel because its reduction is `1`. Its `n`th power is
also `1`, since both points have the same prescribed `n`th power by `hp`.
`InfinitesimalKernel.eq_one_of_pow_eq_one` gives `x₁ * x₂⁻¹ = 1`. Thus
`x₁ = x₂`; `Chart.pt_injective` and injectivity of restriction of scalars
give `φ₁ = φ₂`.

For **surjectivity**, let `φ : C →ₐ[B] D ⧸ I`. Restrict scalars to `R` and use
formal smoothness of `C` over `R` to lift it to a point `x` over `D`.
Let `y` be the prescribed target point from `B → D`. The reduction of `y`
equals the `n`th power of the point of `φ`, by `hp`. Hence
`k = x ^ n * y⁻¹` lies in the infinitesimal kernel.
`InfinitesimalKernel.exists_pow_eq` supplies a point `r` in that kernel with
`r ^ n = k`. Commutativity then gives `(x * r⁻¹) ^ n = y`, and `x * r⁻¹`
reduces to the original point.

The corrected point remains in `cV`: a square-zero thickening does not change
the image of a point (`range_testHom_comp`, using the quotient's surjectivity
and nilpotent kernel). Therefore `Chart.exists_pt` writes it as `cV.pt ψ` for
an `R`-algebra map `ψ : C →ₐ[R] D`. Its prescribed `n`th power, `pt_comp` and
`cU.pt_injective` show that `ψ` commutes with `B → C` and `B → D`. This
upgrades it to the required `B`-algebra map. Finally, `cV.pt_injective` shows
its reduction is `φ`. This establishes surjectivity and formal etaleness.

## Passage to schemes

The lemma `multiplication_locallyOfFinitePresentation` applies the published
cancellation lemma `locallyOfFinitePresentation_of_comp`. The composition of
multiplication with `A`'s structure morphism equals that structure morphism,
which is smooth and hence locally of finite presentation and locally of
finite type.

For `multiplication_etale`, the proof applies
`HasRingHomProperty.iff_exists_appLE` for `Etale`. At a point `x` of `A`, it
chooses an affine open `S₀` of the base containing the image of `x`, an affine
open `U` around `f(x)` over `S₀`, and an affine open `W` around the unit point
over the same base point. It then chooses an affine neighborhood `V` of `x`
inside `f⁻¹(U) ∩ 1⁻¹(W)`. Since `f` is over `S`, `V` lies over `S₀`.
These form the three charts of `formallyEtale`.

The restriction of the global unit hypothesis to `S₀` supplies invertibility
in `R`. Smoothness of `A → S` supplies smoothness, hence formal smoothness,
of `Γ(A, V)` over `R`. The power hypothesis is precisely
`GroupScheme.points_multiplication`, with `zpow_natCast` converting the
integer exponent to a natural exponent. Thus the map on sections
`Γ(A, U) → Γ(A, V)` is formally etale. It is finitely presented by the
preceding local finite presentation lemma. Combining these properties gives
an etale ring map. The affine-local criterion concludes that multiplication
is etale over the arbitrary base scheme.

Finally `multiplicationEtale` introduces exactly the parameters of the
published statement and applies `multiplication_etale`. The positivity
hypothesis is retained in the exact target but is unnecessary for this proof.
