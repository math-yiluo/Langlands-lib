# A crossed homomorphism extending a closed additive subgroup

Module `Langlands.GroupScheme.LinearAdditiveExtension.CrossedHom`, namespace
`Langlands.GroupScheme.LinearAdditiveExtension`.

The setting is that of `EquivariantFunction`: `q : E ⟶ D(Λ)`, the full kernel with inclusion
`ι`, `a : kernel q ⟶ 𝔾ₐ`, and a character `χ` of `D(Λ)`. This module averages the equivariant
function into a crossed homomorphism `c' : E ⟶ 𝔾ₐ` for the action of `E` on `𝔾ₐ` through
`χ ∘ q`, with `c'` restricting to `a` on the kernel. This is the vanishing of the relevant
Hochschild class for a diagonalizable group acting linearly on `𝔾ₐ`, as in Milne, *Algebraic
Groups* (2022), Proposition 15.31 and Theorem 15.34(a). The Lean proof is internal. It uses the
averaging operator of `DiagonalizableAverage` and fpqc descent of morphisms.

## Descent along `q`

The descent section assumes `q` quasi-compact, flat and surjective on underlying schemes.

- `fpqc_whiskerRight` and the instances after it: `q ▷ Y : E ⊗ Y ⟶ D ⊗ Y` is again
  quasi-compact, flat and surjective. It is a base change of `q`, by Mathlib's
  `MorphismProperty.pullbackMap`. Hence it is an epimorphism, and so is `q`.
- `eq_mul_kpt`: two points with the same image differ by the kernel point `kpt`.
- `descend q Ψ hΨ` descends a morphism `Ψ : E ⟶ W` that is invariant under right translation by
  kernel points. `fac_descend` gives `q ≫ descend q Ψ hΨ = Ψ`.
- `descendLeft q Ψ hΨ : D ⊗ Y ⟶ W` does the same along `q ▷ Y` for `Ψ : E ⊗ Y ⟶ W`, invariant
  in the first variable. `fac_descendLeft` and `lift_comp_descendLeft` state the factorization.
- In both cases the relation needed by Mathlib's `EffectiveEpi.desc` is checked on arbitrary
  scheme morphisms (`descend_rel`, `descendLeft_rel`). These are turned into points over
  `Spec k`. The second point of a pair is written as the first times a kernel point.
- `hom_ext_lift` and `hom_ext_lift₃`: morphisms out of `X ⊗ Y` (or `X ⊗ (Y ⊗ Z)`) are equal if
  they agree on all points `lift x y` (or `lift x (lift y z)`).

## The averaged crossed homomorphism

Hypotheses `hconj`, `hlin` and `hfE` are those of the splitting statement and of
`exists_equivariant`. An action `b` of `D` on the kernel is induced by conjugation in `E`
(`hconj`). It is the restriction of the linear action through `χ` (`hlin`). The function `fE`
satisfies `f(g · ι(u)) = f(g) + χ(q g) a(u)` (`hfE`).

- `phi q χ fE : E ⊗ E ⟶ 𝔾ₐ` is `Φ(g, x) = χ(q g)⁻¹ (f(g x) − f(g))`. `cd_lift_phi` computes it
  on points. `charValue_inv_mul` is the identity `χ(q x) χ(q(g x))⁻¹ = χ(q g)⁻¹`.
- `phi_invariant`: `Φ(g · ι(u), x) = Φ(g, x)`. Write `g ι(u) x = (g x) ι(v)` with
  `v = b(q(x)⁻¹, u)`, using `hconj`. Then `hfE`, `hlin` and multiplicativity of `χ` give the
  claim.
- `phiBar = descendLeft q (phi …) …` is `Φ` descended to `D ⊗ E`. `lift_comp_phiBar` and
  `lift_comp_whiskerLeft_phiBar` evaluate it at points `(q g, y)`.
- `phiBar_mul` is the integrand identity
  `Φ̄(z, x y) = Φ̄(z, x) + χ(q x) Φ̄(z · q(x), y)` as morphisms out of `D ⊗ (E ⊗ E)`. It is proved
  after cancelling the epimorphism `q ▷ (E ⊗ E)`, on points `(g, x, y)`.
- `crossedHom = DiagonalizableAverage.average Λ phiBar`. This needs `E` affine over `Spec k`.
- `crossedHom_mul`: `c'(x y) = c'(x) + χ(q x) c'(y)`, as an equality of morphisms out of
  `E ⊗ E`. The proof averages `phiBar_mul`, using `comp_average_eq`, `average_mul`,
  `average_weightAction` and `average_translate` with translation by `q(x)`.
- `isAffineHom_kernel`: if `IsClosedSubgroup a`, then the kernel is affine over `Spec k`.
- `kernel_comp_crossedHom`: `ι ≫ c' = a`. On `D ⊗ kernel`, the integrand `(D ◁ ι) ≫ Φ̄` equals
  `snd ≫ a`, because `Φ(g, ι u) = a(u)` by `hfE`. Then `average_snd` applies.
