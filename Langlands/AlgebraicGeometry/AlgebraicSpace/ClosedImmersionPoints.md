# Points of closed immersions

Author: Worker 105.

Helper module for the proof of Conrad's p.17 claim that closed immersions of separated
algebraic spaces of finite type induce closed embeddings on adelic points
(`Langlands.Global.AdelicSpacePointTopologyStatement`).

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.ClosedImmersionPoints`. Here `X` and `Y`
are algebraic spaces over `Spec C`, and `IsClosedImmersion (hom f)` is the representable notion
of `Langlands.AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion`: every pullback to a scheme is
a closed immersion.

- `injective_appTop_spec`: `Spec` of an injective ring map is injective on global sections.
- `exists_changeRing_eq`: let `f : X → Y` be a closed immersion and `φ : A →ₐ[C] B` injective.
  If a `B`-point `x` of `X` maps to the image in `Y(B)` of an `A`-point `y` of `Y`, then `x`
  comes from an `A`-point `x'` of `X` with `f(x') = y`.
  - Proof: pull `f` back along `y`. This gives a closed immersion `Z → Spec A`, and the point
    `x` gives a factorization of `Spec B → Spec A` through `Z`.
  - So `Z → Spec A` is injective on global sections, hence an isomorphism
    (`IsClosedImmersion.isIso_of_injective_of_isAffine`).
  - Its inverse gives `x'`.
- `map_injective`: a closed immersion is injective on `B`-points for every `C`-algebra `B`.
  Two points with the same image give two sections of the pullback `Z → Spec B` of `f` along
  that image. A closed immersion is a monomorphism, so the sections agree.
