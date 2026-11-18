# Two-sided orbit extensions into an affine scheme are constant

Author: Worker 919.

Module `Langlands.GroupScheme.Dynamic.TwoSidedConstancy`, namespace
`Langlands.GroupScheme.TwoSidedConstancy`. This is an internal supporting unit for Task 7586.
It formalizes an elementary fact: a Laurent polynomial lying in both `A[s]` and `A[s⁻¹]` is
constant. It uses the Library's polynomial and Laurent charts of `𝔸¹` and `𝔾ₘ`
(`Dynamic/Uniqueness`, `Dynamic/AffineExtension`, `Dynamic/OppositeIntersection`). It needs no literature source.

## Statements

The inversion machinery is the Library's (`Dynamic/OppositeIntersection`):
`AffineLine.laurentInvertRing`, `AffineLine.laurentInvert`,
`AffineLine.laurentInvert_comp_laurentPoint` (on the Laurent chart, `X ↦ X⁻¹` is inversion
`(CommGroupScheme.groupHom (Gm.powerHom _ (-1))).hom.hom` of `𝔾ₘ`) and
`AffineLine.polynomial_eq_C_eval_zero_of_invert`. This module adds:

- `ΓSpecIso_hom_specMap_comp_appTop`: global functions pulled back along `Spec.map φ`
  correspond to applying `φ`, under `Scheme.ΓSpecIso`.
- `evalOneHom A`: evaluation `A[X, X⁻¹] ⟶ A` at `X = 1`.
  `polynomialC_toLaurent_evalOneHom`: evaluation at `1` is the identity on constants.
- `unitPointLaurent f : Over.mk f ⟶ laurentScheme f`, the point `X = 1` of
  `Spec A[X, X⁻¹]` over `S`, for `f : Spec A ⟶ S`.
- `unitPointLaurent_comp_laurentPoint`: `unitPointLaurent f ≫ laurentPoint f =
  lift (𝟙 _) (toUnit _ ≫ η[(Gm S).X])`. The point `X = 1` is the unit section of `𝔾ₘ`.
- `evalZero_eq_of_twoSided` (main theorem). Fix `A : CommRingCat`, `V : Over (Spec A)` with
  `[IsAffine V.left]`, `o : Over.mk (𝟙 (Spec A)) ⊗ (Gm (Spec A)).X ⟶ V`, and
  `e₀ eInf : Over.mk (𝟙 (Spec A)) ⊗ AffineLine.scheme (Spec A) ⟶ V`. Assume
  - `h₀ : Over.mk (𝟙 _) ◁ unitInclusion _ ≫ e₀ = o`;
  - `hInf : Over.mk (𝟙 _) ◁ unitInclusion _ ≫ eInf =
    Over.mk (𝟙 _) ◁ (CommGroupScheme.groupHom (Gm.powerHom (Spec A) (-1))).hom.hom ≫ o`.

  Then `Dynamic.evalZero e₀ = lift (𝟙 _) (toUnit _ ≫ η[(Gm (Spec A)).X]) ≫ o`. The value at
  `0` of the extension equals the value of `o` at `1`. Taking `A = CommRingCat.of k`, the
  base `Spec A` is `Spec k` and `Over.mk (𝟙 (Spec A))` is the rational point.

## The implemented proof of `evalZero_eq_of_twoSided`

Write `P = polynomialPoint`, `L = laurentPoint` and `ι_L = laurentInclusion` for
`f = 𝟙 (Spec A)`.

1. `laurentInclusion_comp_of_whiskerLeft` turns `h₀` into `ι_L ≫ P ≫ e₀ = L ≫ o`. It turns
   `hInf` into `ι_L ≫ P ≫ eInf = L ≫ (◁ inversion) ≫ o`, which by
   `AffineLine.laurentInvert_comp_laurentPoint` equals `laurentInvert ≫ L ≫ o`.
2. Write the value at `0` as `polynomialZero ≫ P ≫ e₀` (`evalZero_polynomialPointInv`).
   Write the value at `1` as `unitPointLaurent ≫ L ≫ o`. Since `V` is affine, it suffices
   to compare pullbacks of each global function `g` of `V` (`ext_of_isAffine`).
3. Let `a ∈ A[X]`, `b ∈ A[X, X⁻¹]`, `c ∈ A[X]` be the pullbacks of `g` along `P ≫ e₀`,
   `L ≫ o`, `P ≫ eInf`, read through `ΓSpecIso`. Step 1 and
   `ΓSpecIso_hom_specMap_comp_appTop` give `toLaurent a = b` and
   `toLaurent c = invert b`. Hence `toLaurent a = invert (toLaurent c)`, and
   `polynomial_eq_C_eval_zero_of_invert` gives `a = C (a.eval 0)`.
4. Then `a` at `X = 0` is `a.eval 0`. Also `b = toLaurent (C (a.eval 0))` at `X = 1` is
   `a.eval 0`. So the two pullbacks of `g` agree.
