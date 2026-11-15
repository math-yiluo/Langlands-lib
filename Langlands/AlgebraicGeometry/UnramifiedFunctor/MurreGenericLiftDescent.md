# Descending `NoLargerLift` from basic opens to localizations

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreGenericLiftDescent`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.GenericLift`. It supports the proof of
`EtaleLocus.GenericNoLargerLiftStatement` (step 3 of Murre's case (b), "using (F2)"; see
`MurreGenericNoLargerLift.md`). It imports `MurreGenericLiftMaps` and the published module
`MurreChartsLocalization` (namespace `Charts`). That module provides the directed index
`DivIndex M` (elements of a submonoid `M` ordered by divisibility), the maps
`awayMap : A[1/a] → A[1/b]` for `a ∣ b` and `toLoc M B a : A[1/a] → B` for a localization
`B` of `A` at `M`, and condition (F2) in the form of the lemmas
`exists_eq_of_isLocalization` (every element of `F(Spec B)` comes from some `F(Spec A[1/a])`)
and `exists_eq_of_isLocalization_of_eq` (two elements of `F(Spec A[1/a])` with the same
image in `F(Spec B)` agree in some `F(Spec A[1/b])`). All results use only the standard
axioms.

## (F2) in `rhom` form (section `F2`)

- `spec_comp₂₂`: an equality `ψ.comp (α.comp β) = γ.comp δ` of ring maps gives the
  corresponding equality of composites of `Spec.map`s followed by `g`.
- `toLoc_comp_algebraMap`: `toLoc M B a` is compatible with the maps from `A`.
- `exists_away`, `exists_away_eq`: restatements of the two (F2) lemmas above for objects
  `algebraOver f T` and maps `rhom` (from `MurreGenericLiftMaps`). The restated maps are
  definitionally equal to the original ones.

## The descent (section `Descent`)

- `exists_away_lift`: for `a = m mod K` in `A/K` and a ring map `ρ : A/K → T` with `ρ(m)` a
  unit, there is `ℓ : (A/K)[1/a] → T` extending `ρ`. It is `IsLocalization.Away.lift`; only
  the extension property is retained.
- `noLargerLift_of_isLocalization`: let `f : Spec A ⟶ S`, `I` an ideal of `A`,
  `ξ ∈ F(algebraOver f (A ⧸ I))`, and `B` a localization of `A` at a submonoid `M`, under
  `ZariskiSheaf F` (F1a) and `FilteredColimits F` (F2). If `g₀ ∈ M` and
  `NoLargerLift (Localization.Away g) ξ` holds for every multiple `g` of `g₀`, then
  `NoLargerLift B ξ`.
- `noLargerLift_atPrime`: the case `B = A_q` for a prime `q` with `g₀ ∉ q`.

Proof of `noLargerLift_of_isLocalization`. Let `J < IB`, and let `η` over `Spec (B/J)`
restrict on `Spec (B/IB)` to the restriction of `ξ`.

1. *Shape of `J`.* `K := J.under A ⊓ I` satisfies `K ≤ I` and `KB = J`. This uses
   `IsLocalization.map_inf`, `IsLocalization.map_under` and `J ≤ IB`. So `J` may be replaced
   by `KB` with `K ≤ I`.
2. *(F2) surjectivity over `A/K`.* `B/KB` is the localization of `A/K` at the image of `M`
   (a Mathlib instance). View `η` over `S` through `Spec (A/K)`. `exists_away` gives
   `a = m mod K` with `m ∈ M`, and `ζ ∈ F(Spec (A/K)[1/a])` whose image in `F(Spec (B/KB))`
   is `η`.
3. *(F2) injectivity over `A/I`.* `B/IB` is the localization of `A/I` at the image of `M`.
   Let `a₁ = m mod I`. Compare two elements of `F(Spec (A/I)[1/a₁])`: the push-forward of
   `ζ` along `ψ₁ : (A/K)[1/a] → (A/I)[1/a₁]` and the restriction of `ξ`. Their images in
   `F(Spec (B/IB))` are the restriction of `η` and the restriction of `ξ`, which are equal by
   hypothesis. `exists_away_eq` gives `b = m' mod I` with `m' ∈ M`, `a₁ ∣ b`, and the two
   elements agree in `F(Spec (A/I)[1/b])`.
4. *Restriction to `A_g`, `g = g₀ m m'`.* Then `g ∈ M`, so `NoLargerLift (Localization.Away g) ξ`
   holds. Put `J' := K A_g`. Then `J' < I A_g`: if they were equal, mapping both to `B`
   (through `A_g → B`, defined since `g` is a unit in `B`) would give `KB = IB`. Push `ζ`
   along `ℓ : (A/K)[1/a] → A_g/J'` to `η' ∈ F(Spec (A_g/J'))`; here `m` is a unit in `A_g`.
   Map the equality from step 3 along `μ : (A/I)[1/b] → A_g/IA_g`. Then `η'` and the
   restriction of `ξ` to `Spec (A_g/IA_g)` agree. This contradicts
   `NoLargerLift (Localization.Away g) ξ`.

Each step identifies composites of ring maps out of `(A/K)[1/a]`, `(A/I)[1/a₁]`, `A/I`. This
uses `IsLocalization.ringHom_ext` and `Ideal.Quotient.ringHom_ext` and evaluation on elements
of `A`.

Murre (printed p.251, PDF p.10 of `murre-1965-bourbaki-294-unramified-functors`, SHA-256
`e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`) states this step without
proof ("As we have noted before, it follows then (using (F2))"). The argument above is this
project's. Taking `K = J.under A ⊓ I` avoids any finite generation hypothesis on `J`.
