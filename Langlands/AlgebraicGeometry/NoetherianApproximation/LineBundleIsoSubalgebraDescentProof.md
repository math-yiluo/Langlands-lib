# Proof of descent of isomorphisms of line bundles to finitely generated subalgebras

`Langlands.AlgebraicGeometry.NoetherianApproximation.lineBundleIsoSubalgebraDescent` proves
`Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleIsoSubalgebraDescentStatement.{u}`
for an arbitrary universe `u`. See `LineBundleDescentStatements.md` for the statement and its
Stacks Project sources (Lemma 32.10.2(2),(3), tag 01ZR).

This module contains no ported FLT code. It applies the ported FLT theorem
`AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit`
(module
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit`,
Anthropic FLT Lean source at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, Apache-2.0).
That theorem works for an arbitrary directed system of rings `G` with direct limit `R`
(FLT's predicate `IsDirectLimit`), a stage `i`, and a quasi-compact, quasi-separated
`fX : X ⟶ Spec (G i)`. Given two modules `𝓛₁`, `𝓛₂` on `X` that satisfy FLT's
`Scheme.Modules.IsInvertible`, if their pullbacks along the chosen
`pullback.fst fX (Spec.map (g i))` to `Spec R` are isomorphic, then so are their pullbacks along
`pullback.fst fX (Spec.map (φ i j hij))` for some `j ≥ i`. The bridge does three things. It
specialises the system to finitely generated subalgebras, converts the Library's
`IsLocallyFreeRankOne` into FLT's `IsInvertible`, and moves between the chosen fibre products
and the arbitrary pullback squares of the statement.

## Shared lemmas

The helper lemmas and the directed system of finitely generated subalgebras are in
`Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentBridge`
(see `LineBundleDescentBridge.md`). This proof uses `isInvertible_of_isLocallyFreeRankOne`,
`nonempty_iso_pullback_of_fac`, `nonempty_iso_pullback_pullback_iff`, the system `FGIndex`,
`FGStage`, `fgTransition`, `fgToLimit`, `fgIsDirectLimit`, and the identities
`spec_map_fgToLimit_comp` and `spec_map_fgTransition_comp`.

## Specialisation of the FLT theorem

`exists_fg_nonempty_iso_pullback` is the FLT theorem with `ι := FGIndex A₀ A`,
`G := FGStage`, `R := A`, `φ := fgTransition` and `g := fgToLimit`. Its arguments are passed
by name: with positional arguments, elaborating the call hit the heartbeat limit.

## The main proof

Fix the data of the statement. Let `i` be the index `Algebra.adjoin A₀ s` (finitely generated
by `Subalgebra.fg_adjoin_finset`), write `ι₀ := Spec.map (algebraMap A₀ (FGStage i))`, and take
the chosen base change `pullback f₀ ι₀` of `X₀` to `Spec i`. Its second projection
`pullback.snd f₀ ι₀` is quasi-compact and quasi-separated by Mathlib's base-change instances.
Apply `exists_fg_nonempty_iso_pullback` at `i` to `pullback.snd f₀ ι₀` and to the modules
`(pullback (pullback.fst f₀ ι₀)).obj M` and `(pullback (pullback.fst f₀ ι₀)).obj N`. These are
FLT-invertible by `isInvertible_of_isLocallyFreeRankOne` and
`Scheme.Modules.IsInvertible.pullback`.

1. **Hypothesis of the FLT theorem (`h₀`).** By `nonempty_iso_pullback_pullback_iff`, its
   hypothesis asks for an isomorphism of the pullbacks of `M` and `N` along the composite
   `pullback.fst _ (Spec.map (fgToLimit i)) ≫ pullback.fst f₀ ι₀`. This composite factors as
   `c ≫ a`, where `c` is the morphism into `X` that the pullback square `hpb` gives for the pair
   `(pullback.fst _ _ ≫ pullback.fst f₀ ι₀, pullback.snd _ _)`. The required compatibility is
   that `pullback.fst _ _ ≫ pullback.fst f₀ ι₀ ≫ f₀` equals
   `pullback.snd _ _ ≫ Spec.map (algebraMap A₀ A)`. It follows from the two `pullback.condition`
   equations and `spec_map_fgToLimit_comp`. `nonempty_iso_pullback_of_fac` with `hpb.lift_fst`
   and the hypothesis `hiso` gives `h₀`.
2. **Conclusion of the FLT theorem.** It provides `j ≥ i` and an isomorphism of the iterated
   pullbacks along `pullback.fst (pullback.snd f₀ ι₀) (Spec.map (fgTransition i j hij))`.
   `nonempty_iso_pullback_pullback_iff` turns these into pullbacks along that projection
   composed with `pullback.fst f₀ ι₀`.
3. **Choice of `T`.** Take `T := j.1`. It is finitely generated, and it contains `s` because
   `s ⊆ Algebra.adjoin A₀ s = i ≤ j` (`Algebra.subset_adjoin`).
4. **Arbitrary pullback squares over `Spec T`.** Let `IsPullback a' f' f₀ (Spec.map (algebraMap A₀ T))`.
   Build `c' : X' ⟶ pullback (pullback.snd f₀ ι₀) (Spec.map (fgTransition i j hij))` as
   `pullback.lift (pullback.lift a' (f' ≫ Spec.map (fgTransition i j hij)) _) f' _`. The inner
   lift needs `a' ≫ f₀ = (f' ≫ Spec.map (fgTransition i j hij)) ≫ ι₀`. This follows from the
   commutativity `hpb'.w` of the square and `spec_map_fgTransition_comp`. The outer lift's
   condition is `pullback.lift_snd`. By `pullback.lift_fst` (twice), `c'` composed with the
   projection to `X₀` is `a'`. `nonempty_iso_pullback_of_fac` transports the isomorphism of
   step 2 to the pullbacks along `a'`.

The pullback property of the square on the `T` side is not used. Only its commutativity is.
