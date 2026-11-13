# The linear system of an invertible module on a proper flat family with geometrically integral fibres

Authors: Worker 5705.

Worker 5705 wrote the Lean file and this description for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705), after reading p.15 (the
locally noetherian convention) and pp.22–26 of Kleiman's survey (Section 3,
from Definition 3.3 to Exercise 3.14). The
proposition is the linear-system ingredient of Grothendieck's construction of
the Picard scheme (Kleiman, proof of Theorem 4.8, pp.28–30): for an invertible
sheaf `M` on a proper flat family `Y/T` with geometrically integral fibres, the
functor `LinSys_{M/Y/T}` is represented by a proper `T`-scheme carrying a
universal relative effective divisor. It also records the flatness and
surjectivity of the representing scheme when the fibres have no first
cohomology.

No proof is asserted here.

## Statement

The module defines one declaration,
`Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement`,
with the single universe parameter `u`. It is a proposition (`def … : Prop`)
whose body is

```lean
∀ (T : Scheme.{u}) [IsLocallyNoetherian T] {Y : Scheme.{u}} (g : Y ⟶ T),
  IsProper g → Flat g → GeometricallyIntegral g →
  ∀ M : Y.Modules, Scheme.Modules.IsInvertible M →
    ∃ (Λ : Scheme.{u}) (l : Λ ⟶ T) (W : RelativeEffectiveDivisor (pullback.snd g l))
      (N : Λ.Modules),
      IsProper l ∧ Scheme.Modules.IsInvertible N ∧
      Nonempty (W.toEffectiveCartierDivisor.lineBundle.obj ≅
        (Scheme.Modules.pullback (pullback.fst g l)).obj M ⊗
          (Scheme.Modules.pullback (pullback.snd g l)).obj N) ∧
      (∀ (T' : Scheme.{u}) [IsLocallyNoetherian T'] (t' : T' ⟶ T)
          (E : (pullback g t').IdealSheafData),
        (∃ (k : T' ⟶ Λ) (hk : k ≫ l = t'),
            W.ideal.comap
              (pullback.map g t' g l (𝟙 Y) k (𝟙 T) (by simp) (by simp [hk])) = E) ↔
          ∃ hE : IsRelativeEffectiveCartierIdeal (pullback.snd g t') E,
            ∃ N' : T'.Modules, Scheme.Modules.IsInvertible N' ∧
              Nonempty ((EffectiveCartierDivisor.lineBundle ⟨E, hE.1⟩).obj ≅
                (Scheme.Modules.pullback (pullback.fst g t')).obj M ⊗
                  (Scheme.Modules.pullback (pullback.snd g t')).obj N')) ∧
      (∀ (T' : Scheme.{u}) [IsLocallyNoetherian T'] (t' : T' ⟶ T) (k₁ k₂ : T' ⟶ Λ)
          (hk₁ : k₁ ≫ l = t') (hk₂ : k₂ ≫ l = t'),
        W.ideal.comap (pullback.map g t' g l (𝟙 Y) k₁ (𝟙 T) (by simp) (by simp [hk₁])) =
            W.ideal.comap (pullback.map g t' g l (𝟙 Y) k₂ (𝟙 T) (by simp) (by simp [hk₂])) →
          k₁ = k₂) ∧
      ((∀ t : T, IsZero ((relativeCohomology (pullback.snd g (T.fromSpecResidueField t)) 1).obj
          ((Scheme.Modules.pullback (pullback.fst g (T.fromSpecResidueField t))).obj M))) →
        Flat l ∧ LocallyOfFinitePresentation l ∧
          ((∀ t : T, ¬ IsZero
              ((relativeCohomology (pullback.snd g (T.fromSpecResidueField t)) 0).obj
                ((Scheme.Modules.pullback (pullback.fst g (T.fromSpecResidueField t))).obj M))) →
            Surjective l))
```

### Hypotheses

- `T` is a locally noetherian scheme (Mathlib's `IsLocallyNoetherian`).
- `g : Y ⟶ T` is proper (Mathlib's `IsProper`: separated, universally closed
  and locally of finite type), flat (Mathlib's `Flat`) and geometrically
  integral (Mathlib's `GeometricallyIntegral`: for every field `K` and every
  `Spec K ⟶ T` the fibre product `Y ×_T Spec K` is integral). This is
  Kleiman's hypothesis "X/S is proper and flat, and its geometric fibers are
  integral" of Theorem 3.13.
- `M` is an invertible `𝒪_Y`-module: `Scheme.Modules.IsInvertible M` is the
  predicate of the FLT port, defined by local trivialisations. Every point of
  `Y` has an open neighbourhood `U` such that the pullback of `M` along the
  inclusion `U.ι` is isomorphic to the structure sheaf of `U`; that is, `M` is
  locally free of rank one. Equivalently, though this is not the definition
  used, `M` has a tensor inverse. The tensor
  product `⊗` throughout is the monoidal structure of the FLT port on
  `Y.Modules` (`AlgebraicGeometry.Scheme.Modules.monoidalCategory`), the only
  monoidal structure on module sheaves in this module's imports.

For a morphism `t' : T' ⟶ T` write `Y_{T'} = pullback g t'` (Mathlib's chosen
fibre product `Y ×_T T'`) with projections `pullback.fst g t' : Y_{T'} ⟶ Y`
and `pullback.snd g t' : Y_{T'} ⟶ T'`, and `M_{T'}` for the module pullback
of `M` along the first projection.

### Conclusion

There exist a scheme `Λ`, a morphism `l : Λ ⟶ T`, a relative effective
divisor `W` on `Y_Λ = pullback g l` over `Λ`, and an `𝒪_Λ`-module `N`, with:

1. `l` is proper and `N` is invertible.
2. `O(W) ≅ M_Λ ⊗ (pullback.snd g l)^* N`. Here `W` is the Library's
   `RelativeEffectiveDivisor (pullback.snd g l)`: an actual ideal sheaf of
   `Y_Λ` that is an effective Cartier ideal and whose closed subscheme is flat
   over `Λ` (`IsRelativeEffectiveCartierIdeal`); `O(W)` is the Library's
   `EffectiveCartierDivisor.lineBundle`, the dual of the ideal sheaf. This is
   Kleiman's `O(W) = L_L ⊗ f_L^* O_L(1)` of Exercise 3.14, with `N` in place of
   `O_L(1)`.
3. **Representability (existence and characterisation).** For every locally
   noetherian scheme `T'` (instance argument `[IsLocallyNoetherian T']`), every
   morphism `t' : T' ⟶ T` and every actual ideal sheaf `E` of `Y_{T'}`, the
   following are equivalent:
   - there is a `T`-morphism `k : T' ⟶ Λ` (that is, `k ≫ l = t'`) such that
     the pullback of the ideal `W` along `1 × k : Y_{T'} ⟶ Y_Λ`
     (`pullback.map g t' g l (𝟙 Y) k (𝟙 T)`) is `E` (Mathlib's
     `IdealSheafData.comap`);
   - `E` is a relative effective Cartier ideal for `Y_{T'} ⟶ T'`, and there is
     an invertible `𝒪_{T'}`-module `N'` with
     `O(E) ≅ M_{T'} ⊗ (pullback.snd g t')^* N'`.

   The second condition says exactly that `E` lies in Kleiman's
   `LinSys_{M/Y/T}(T')` (Definition 3.12).
4. **Representability (uniqueness).** For every locally noetherian `T'`,
   every `t' : T' ⟶ T` and any two
   `T`-morphisms `k₁, k₂ : T' ⟶ Λ` over `t'`, if `W` pulls back to the same
   ideal along `1 × k₁` and `1 × k₂`, then `k₁ = k₂`.
5. **Fibrewise vanishing.** Suppose that for every point `t` of `T` the first
   cohomology of the fibre vanishes: writing
   `T.fromSpecResidueField t : Spec κ(t) ⟶ T` and `Y_t = pullback g (T.fromSpecResidueField t)`,
   the `κ(t)`-module `H¹(Y_t, M_t)`, given by the Library's
   `Modules.DerivedSections.relativeCohomology (pullback.snd g _) 1` applied to
   the pullback `M_t` of `M`, is zero. Then `l` is flat and locally of finite
   presentation; if moreover `H⁰(Y_t, M_t) ≠ 0` for every `t`, then `l` is
   surjective.

Together, items 3 and 4 say that `k ↦ (1 × k)^{-1} W` is a bijection from the
`T`-morphisms `T' ⟶ Λ` onto `LinSys_{M/Y/T}(T')`, for every locally noetherian
`T`-scheme `T'`. This is Kleiman's universal property of `W` in Exercise 3.14
and the representability of Theorem 3.13, on Kleiman's test category: on
p.15 Kleiman works throughout with locally noetherian schemes only, and he
omits the limit argument that removes this restriction. The statement makes
no assertion about test schemes that are not locally noetherian.

## Source and derivation

The source is S. L. Kleiman, *The Picard scheme*, arXiv math/0504020v1
(2005), registered original `kleiman-2005-picard-scheme-arxiv-math0504020v1`:

- p.15, the standing convention of Sections 2–4: "Throughout these notes, we
  work only with locally Noetherian schemes", with the passage to general
  schemes by a limiting process explicitly omitted;
- p.22, Definition 3.3 (a relative effective divisor on `X/S` is an
  effective divisor `D ⊂ X` that is `S`-flat), matching the Library's
  `IsRelativeEffectiveCartierIdeal`;
- p.24, Subsection 3.10 (the module `Q`, with
  `Hom(Q, N) ≅ f_*(F ⊗ f^*N)` (3.10.1), compatible with base change), and
  p.25, the conditions (i)–(v) of Subsection 3.10, of which (v)
  `H¹(X_s, F_s) = 0` implies (i) `Q` free near `s`;
- p.25, Exercise 3.11 (`𝒪_S ≅ f_*𝒪_X` universally);
- p.25, Definition 3.12 (`LinSys_{L/X/S}(T)`: relative effective divisors `D`
  on `X_T/T` with `O_{X_T}(D) ≅ L_T ⊗ f_T^*N` for some invertible `N` on `T`);
- pp.25–26, Theorem 3.13 (`P(Q)` represents `LinSys_{L/X/S}` when `X/S` is
  proper and flat with integral geometric fibres) and its proof;
- p.26, Exercise 3.14 (the universal relative effective divisor `W` on
  `X_{P(Q)}` with `O(W) = L ⊗ O(1)` and its universal property).

Items 1–4 restate Theorem 3.13 and Exercise 3.14 with `Λ = P(Q)` and
`N = O_{P(Q)}(1)`. `P(Q)` is proper over `T` because `Q` is coherent. They
keep Kleiman's p.15 convention exactly: the base `T` and every test scheme
`T'` are locally noetherian, and nothing is claimed for other test schemes.
The Picard scheme over a noetherian base is built in this setting (Kleiman,
proof of Theorem 4.8, pp.28–30), and the consumer of this statement, the
Picard-scheme construction of Task 5705, only applies it to locally
noetherian test schemes (schemes locally of finite type over a noetherian
ring). Kleiman's hypothesis that the geometric fibres are integral is
Mathlib's `GeometricallyIntegral`.

Item 5 is derived. If `H¹(Y_t, M_t) = 0` for every `t`, then by 3.10, (v)
implies (i), the coherent module `Q` is locally free, so `P(Q)` is locally a
projective space over `T`; it is therefore smooth, hence flat and locally of
finite presentation. Kleiman uses exactly this on p.30 in the proof of
Theorem 4.8 ("Since (v) implies (i) in Subsection 3.10, therefore `Q` is
locally free"). The fibre of `P(Q)` over `t` is `P(Q ⊗ κ(t))`, and by
(3.10.1) with `N = κ(t)`, `Hom(Q ⊗ κ(t), κ(t)) ≅ H⁰(Y_t, M_t)`; so the fibre is
nonempty exactly when `H⁰(Y_t, M_t) ≠ 0`, and then `l` is surjective. Any
`Λ` satisfying items 1–4 is locally of finite type over the locally noetherian
`T` (because `l` is proper), hence is itself a locally noetherian test scheme.
By the Yoneda lemma on locally noetherian `T`-schemes it is therefore
`T`-isomorphic to `P(Q)`, compatibly with the universal divisors. So the
properties in item 5 do not depend on the choice made in items 1–4.

## Conventions and scope

- Equalities of divisors are equalities of actual ideal sheaves
  (`Scheme.IdealSheafData`), as in the Library's `RelativeEffectiveDivisor`.
- The universal property is expressed by explicit existence and uniqueness of
  classifying morphisms rather than by an isomorphism of functors; this avoids
  constructing a `LinSys` functor and is equivalent to representability.
- Cohomology of the fibre is the Library's derived-functor cohomology
  `relativeCohomology` of `𝒪`-modules over `Spec κ(t)`, as `κ(t)`-modules.
- Test category: the base `T` and all test schemes `T'` are locally
  noetherian (Kleiman's p.15 convention). The extension to arbitrary test
  schemes, by Kleiman's omitted limiting process, is not part of this
  statement.
- The assertion is in universe `u` throughout; no countability or other
  size condition is imposed.
