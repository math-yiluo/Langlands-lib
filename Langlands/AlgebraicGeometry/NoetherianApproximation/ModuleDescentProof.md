# Proof of descent of finitely presented modules to finitely generated subalgebras

Module `Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentProof`, universe `u`.
Author: Worker 1038. It proves the published proposition
`Langlands.AlgebraicGeometry.NoetherianApproximation.FinitePresentationModuleSubalgebraDescentStatement`
of [`ModuleDescentStatements`](ModuleDescentStatements.md), which it imports unchanged:

```lean
theorem finitePresentationModuleSubalgebraDescent :
    FinitePresentationModuleSubalgebraDescentStatement.{u}
```

It uses the helper modules [`ModuleDescentCore`](ModuleDescentCore.md) and
[`ModuleDescentStages`](ModuleDescentStages.md). The theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Proof

Given noetherian `A₀`, `f₀ : X₀ ⟶ Spec A₀` quasi-compact, separated and locally of finite type,
the pullback square `hpb : IsPullback a f f₀ (Spec.map (algebraMap A₀ A))`, a locally finitely
presented `M : X.Modules` and `s : Finset A`:

1. **Cover and presentations.** `X₀` is quasi-compact and quasi-separated
   (`QuasiCompact.compactSpace_of_compactSpace`, `quasiSeparatedSpace_of_quasiSeparated`), and `a`
   is affine (base change of a morphism of spectra). `exists_finset_affineOpens_cover` gives a
   finite family `W : t → X₀.Opens` of affine opens covering `X₀`. On each affine preimage
   `a ⁻¹ᵁ W i` the sections of `M` are finitely presented
   (`finitePresentation_sections_of_isAffineOpen`), and `exists_relations` chooses generators
   `γ i`, relation vectors `ρ i` spanning all relations, through
   `Module.FinitePresentation.fg_ker` and `Submodule.fg_iff_exists_fin_generating_family`.
2. **Overlaps.** Each `W i ⊓ W k` is compact; `exists_finset_basicOpen_cover` covers it by
   finitely many basic opens `X₀.basicOpen h` of `W i` contained in it. On the preimage of such
   a basic open, which is the basic open of `a.app _ h` (`Scheme.preimage_basicOpen`), the
   restricted `γ k l` lies in the span of the restricted `γ i`
   (`mem_span_restrict_basicOpen`, from the Library's `isLocalizingAt_of_isQuasicoherent` and
   the invertibility of `h` on its basic open); coefficients `cc` are chosen.
3. **Finite stage.** `exists_finset_forall_descends` gives finite sets `C₁` for all relation
   entries and `C₂` for all coefficients `cc`. Put `T := Algebra.adjoin A₀ (C₁ ∪ C₂ ∪ s)`, which
   is finitely generated (`Subalgebra.fg_adjoin_finset`) and contains `s`.
4. **The key step.** For every `c` with `IsLift f₀ a f T c`, `c` is affine (`IsLift.isPullback`:
   the pasted square is Cartesian; base change of a morphism of spectra). After choosing the
   descended relation entries and coefficients, substituting `a = c ≫ stageFst f₀ T` makes the
   sections over `a ⁻¹ᵁ W i` sections of the direct image along `c` over
   `V i := stageFst f₀ T ⁻¹ᵁ W i`. The core theorem `exists_isFinitePresentation_pullback_iso`
   applies with `g := γ`:
   - each `V i` is affine (`stageFst` is affine), `(hV i).fromSpec` is affine since the stage is
     separated over `Spec T` (`isAffineHom_fromSpec_stage`), and `Γ(stage f₀ T, V i)` is
     noetherian (`isNoetherianRing_stage`: `T` is noetherian, and `appLE` of the locally finite
     type `stageSnd` is of finite type);
   - the `V i` cover the stage;
   - the relation condition holds with the descended relation entries, since `c.app` maps them
     to the original entries;
   - the cross condition holds on preimages of the chosen basic opens, with the descended
     coefficients.
   This gives a locally finitely presented `G` with `(pullback c).obj G ≅ M`.
5. **Conclusion.** `exists_isLift` provides the canonical lift `q₀`, and `key q₀` gives `M₀`.
   Any `c` satisfying the two equations of the statement equals `q₀` (`IsLift.eq`, by
   `pullback.hom_ext`), so the isomorphism holds along every such `c`.

## Provenance

The statement is Stacks Project, Limits of Schemes, Lemma 01ZR part (1), specialized as described
in [`ModuleDescentStatements`](ModuleDescentStatements.md). The proof follows the first proof
sketched there (`limits.tex`, commit `a04446e5`, lines 2582–2605: the affine case and Zariski
gluing), with the gluing realized by the kernel subsheaf of `ModuleDescentCore`. The helper
lemmas in this module (finite covers, basic-open generation, the stage lemmas) are internal.
