# Proof: direct images of sheafified Čech terms over an affine base

The theorem
`Langlands.AlgebraicGeometry.Modules.CechResolution.cechTermDirectImage`
proves the entire published proposition
`Langlands.AlgebraicGeometry.Modules.CechResolution.CechTermDirectImageStatement.{u}`,
in arbitrary universe `u`, with no outer parameters or extra hypotheses.

For a scheme `X`, a commutative ring `R`, a separated morphism
`π : X ⟶ Spec R`, an ordered affine cover `𝒰` of `X`, a quasi-coherent
`M : X.Modules` and `q : ℕ`, it proves that
`(Scheme.Modules.pushforward π).obj (cechTerm 𝒰 M q)` is quasi-coherent and
that `(DerivedSections.higherDirectImage π (n + 1)).obj (cechTerm 𝒰 M q)`
is zero for every `n : ℕ`.

## Implemented proof

The module contains five helper results in the same namespace; the final
theorem pairs the two termwise results.

**Affine intersections.** The Library lemma `isAffineOpen_inter` (from
`CechResolution/Acyclic.lean`) shows that every intersection `𝒰.inter s` is
an affine open, because `π` is separated over the affine `Spec R`.

**Vanishing for one affine open.** `isZero_higherDirectImage_sheafOn`: for
an affine open `W` and quasi-coherent `M`, the higher direct images of
`sheafOn M W = W.ι_* (M|_W)` along `π` vanish. The open immersion `W.ι` is an
affine morphism (`IsAffineHom.of_comp`, using that `W.ι ≫ π` is a morphism of
affine schemes and `π` is separated), so the published
`affineQuasicoherentHigherDirectImageVanishing` gives
`R^{q+1} (W.ι)_* (M|_W) = 0` for every `q`. Pushforwards of injective modules along `W.ι` are
`π_*`-acyclic by `DerivedSections.isZero_higherDirectImage_pushforward_injective`.
The Library's composite comparison `isIso_compComparison` (namespace
`Langlands.Cohomology.AcyclicResolution`, module
`Langlands.AlgebraicGeometry.Modules.PushforwardComparison`), applied to
`Scheme.Modules.pushforwardComp W.ι π`, therefore identifies
`R^{n+1} π_* (W.ι_* (M|_W))` with `R^{n+1} (W.ι ≫ π)_* (M|_W)`, which is zero by
affine vanishing for the affine morphism `W.ι ≫ π`. This replaces the
Leray spectral sequence of the source by the published composition
comparison under the two vanishing hypotheses.

**Vanishing for the Čech term.** `isZero_higherDirectImage_cechTerm`: the
right-derived functors are additive (`rightDerived_additive`), so they
preserve the finite biproduct `cechTerm 𝒰 M q`, and `isZero_obj_biproduct`
reduces to the summands, which are covered by the previous step.

**Quasi-coherence.** `isQuasicoherent_biproduct_spec` proves that a finite
biproduct of quasi-coherent modules on `Spec R` is quasi-coherent: the tilde
functor preserves finite biproducts, and the biproduct of the isomorphisms
`fromTildeΓ` identifies the biproduct with the tilde of a module.
`isQuasicoherent_pushforward_sheafOn` applies
`QuasicoherentLocal.isQuasicoherent_pushforward` to the affine morphism
`W.ι ≫ π` and transports along `Scheme.Modules.pushforwardComp W.ι π`.
`isQuasicoherent_pushforward_cechTerm` uses that `π_*` is a right adjoint
(`Scheme.Modules.pullbackPushforwardAdjunction π`), hence preserves finite
biproducts, and combines the two previous lemmas.

The lemma `isQuasicoherent_biproduct_spec` is stated with a local option
`backward.isDefEq.respectTransparency false`, needed only to elaborate the
instance argument of `fromTildeΓ`. The proof uses no axioms beyond the
standard ones.

## Original source

This follows the proof of Stacks Project tag 01XL
(`lemma-separated-case-relative-cech`, `coherent.tex` lines 1199–1268 at
commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`), which derives the two
termwise facts from relative affine vanishing (tag 01XC,
`lemma-relative-affine-vanishing`, lines 180–200) and the relative Leray
spectral sequence. The Lean route is the same except that the Leray step is
the published composition comparison described above. The statement's
Markdown explains the scope and the relation to the source.

Worker 1098 wrote this proof; Worker 716 checked it against the published
statement and submitted it.
