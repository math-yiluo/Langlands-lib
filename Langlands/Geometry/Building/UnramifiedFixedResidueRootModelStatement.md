# Fixed-point models whose reductive quotients carry the vanishing restricted roots

Author: Worker 407.

Lean module: `Langlands.Geometry.Building.UnramifiedFixedResidueRootModelStatement`.

This module states `UnramifiedFixedResidueRootModelStatement.{u}` and does not
prove it. It is a geometric existence prerequisite for the published
`UnramifiedRootSpecializationStatement`. The theorem
`unramifiedRootSpecialization_of_fixedResidueRootModel`, in
`UnramifiedRootSpecializationReduction`, proves that this statement implies
that target. The same module shows that it also implies the published
`UnramifiedFixedRootModelStatement`.

## Common data

All binders, the local `HenselianLocalRing ↥𝒪[F]` instance, and the four `let`
bodies `fixed`, `φ`, `P` and `Q` are copied verbatim from the published
`UnramifiedRootSpecializationStatement`. The setting is as follows.

- `F : Type u` is a nonarchimedean local field, and
  `K = inertiaFixedField F` is its maximal unramified extension.
- `G` is a connected reductive `F`-group, with a maximal split torus
  `iS : S.toGrp ⟶ G` contained in `iT` through `f : S ⟶ T`. The base change
  `iT_K` is maximal split and has opposite factor pairs `hE`.
- An upper apartment datum `D : KPApartmentData iT_K ω` is given, where `ω`
  is the order of `MaximalUnramified.valuation F`. A centralizer datum `C`
  is also given, and `D` and `C` are Ω-compatible.
- `fixed x` says that every `K/F` automorphism fixes the root-function family
  at the upper point `x`.
- `φ x` is the published torus-then-field restriction of that family to
  `S`.
- `P` is `torusFieldTranslationMap`, which sends `V(S)` to the upper reduced
  translation space.
- `Q` is the quotient map from `V(S)` to the reduced translation space of
  `iS`.

No lower apartment, carrier identification, specialness or building descent
is assumed.

## Existential conclusion

For every fixed upper point `x`, the statement asserts that there exist

- `D₀ : RelativeComponentModelData ↥𝒪[F] F G`;
- `T₀ : IntegralTorusData D₀ S iS`, with a proof `hT₀` that its integral
  torus is split;
- `Q₀ : SpecialFibreQuotientData D₀`.

These satisfy the following clauses together.

1. `T₀.inclusion` is a closed subgroup (`IsClosedSubgroup`).
2. `T₀.HasMaximalSplitSpecialFibre`: the special fibre of the torus is a
   maximal split torus of the neutral special fibre.
3. `Q₀.IsReductiveQuotient`: the specified radical is the unipotent radical
   of the neutral special fibre, and the specified projection is its
   represented fppf quotient onto a connected reductive group.
4. `IsMaximalSplitTorus (T₀.specialFibreInclusion ≫ Q₀.projection)`: the
   image of the torus in the reductive quotient is maximal split.
5. For every relative root `a ∈ relativeRoots iS` and every `g ∈ U_a(F)`
   (`rootGroupPoints iS a`), including the identity,

   ```
   g ∈ D₀.neutral.integralPoints ↔ 0 ≤ φ x a g,
   g ∈ Q₀.positivePoints        ↔ 0 < φ x a g.
   ```

   These are exactly the two comparisons of the published
   `UnramifiedFixedRootModelStatement`, at the same point `x` and for the same
   family `φ x`.
6. For every upper affine root `ψ ∈ D.affineRoots` with `ψ(x) = 0` and
   `ψ.linear ∘ P ≠ 0`, there is a relative root `a : relativeRoots iS` such
   that:
   - its specialization `T₀.characterSpecialization hT₀ a` lies in
     `relativeRoots (T₀.specialFibreInclusion ≫ Q₀.projection)`, i.e. it is a
     root of the actual reductive quotient with respect to the image of the
     torus;
   - for some real `c ≠ 0`, `(rootForm iS a).comp Q = c • (ψ.linear.comp P)`.

All clauses concern the same `D₀`, `T₀`, `hT₀` and `Q₀`, which serve every
relevant upper affine root at `x`. The relative root `a` is not required to be
reduced or nonmultipliable; it may be any relative root with the stated
proportional form. Uniqueness of the data is not asserted. The statement does
not include `IntegralRootSpecializationData`, root models, kernels, or the
predicate `RepresentsIntegralRoot`.

## Source and provenance

Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered
source `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- Proposition 9.4.23, printed p. 357 / PDF p. 388. The relative root datum of
  the maximal reductive quotient of the special fibre of the connected
  parahoric model at `Ω` has as roots the derivatives of the affine roots
  vanishing identically on `Ω`. Here `Ω = {x}`.
- The proof of Proposition 9.4.25, printed pp. 357–358 / PDF pp. 388–389. The
  image of the closed split integral torus is a maximal split torus of the
  reductive quotient.
- Proposition 9.4.28 and its proof, printed pp. 359–360 / PDF pp. 390–391.
  The parahoric model over the maximal unramified extension is the base change
  of the model at `z`, so the reductive quotient base-changes compatibly.
  Then `b`, a root of the base-changed quotient for an absolute affine root
  vanishing at `z`, restricts to a root of the quotient over the residue
  field. The converse half of that proof is the source of clause 6.
- Proposition 9.4.9 and Axiom 4.1.22(4) for the comparisons in clause 5, as
  recorded in the published `UnramifiedFixedRootModelStatement`.

The authors' corrections dated 1 November 2024 (registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) contain
no change to Propositions 9.4.23–9.4.28.

This is an internal derived interface. It is not a transcription of one
numbered source assertion. It combines the existence of the actual connected
model at a Galois-fixed point (KP Chapters 8–9, descended from the maximal
unramified extension) with the identification of the roots of its reductive
quotient. That identification uses the upper affine roots vanishing at the
point with nonzero restriction to `S`, as in the proof of KP 9.4.28. The
scalar `c` allows for the normalization of `ψ.linear ∘ P` relative to
`rootForm iS a`.
