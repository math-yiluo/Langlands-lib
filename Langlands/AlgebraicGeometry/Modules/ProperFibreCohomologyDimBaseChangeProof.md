# Invariance of fibre cohomology dimensions under base change (proof)

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.ProperFibreCohomologyDimBaseChangeProof` proves

```lean
theorem properFibreCohomologyDimBaseChange :
    ProperFibreCohomologyDimBaseChangeStatement.{u}
```

Let `g : Y ⟶ T` be proper, `F` invertible on `Y`, and let `h' : Y' ⟶ Y`, `g' : Y' ⟶ T'`,
`h : T' ⟶ T` complete a cartesian square (`IsPullback h' g' g h`). For a point `t'` of `T'` with
image `t = h t'` and every `p`, the theorem shows
`dim_{κ(t')} Hᵖ(Y'_{t'}, (h'^* F)_{t'}) = dim_{κ(t)} Hᵖ(Y_t, F_t)`.

The argument is Mumford's flat base change (D. Mumford, *Abelian Varieties*, Chapter II, §5,
Corollary 5, pp.53–54; literature id `mumford-abelian-varieties-chapter-ii-scan`), applied to the
fibre `Y_t` over the field `κ(t)` and the field extension `κ(t) → κ(t')`. It reuses the perfect
model of the proof of `ProperFlatFibreCohomologySemicontinuityStatement` (module
`ProperFlatFibreCohomologySemicontinuityProof`) and the dimension formula of the helper module
`Langlands.Cohomology.FibreDimension`.

## Proof

1. **Perfect model of the fibre.** The fibre map `f : Y_t ⟶ Spec κ(t)` (Mathlib's chosen pullback
   of `g` along `T.fromSpecResidueField t`) is proper (base change of `g`) and flat (every
   morphism to the spectrum of a field is flat, by a Mathlib instance). The field `κ(t)` is
   noetherian, and `F_t` is invertible (`IsInvertible.pullback`). So
   `FibreSemicontinuity.exists_perfectModel` gives a strictly perfect complex `K` of
   `κ(t)`-vector spaces such that, for every ring map `φ : κ(t) ⟶ S`, the scalar extension
   `K ⊗_φ S` represents the derived `S`-module sections of the pullback of `F_t` to
   `Y_t ×_{Spec κ(t)} Spec S`.
2. **The fibre over `t`.** Take `φ = 𝟙`. The square with sides `𝟙`, `f`, `f`, `Spec.map 𝟙 = 𝟙` is
   cartesian (`IsPullback.id_horiz`). The Library theorem
   `nonempty_relativeCohomology_iso_chosenPullback`, with `Scheme.Modules.pullbackId` and
   `DerivedPlus.homologyIsoOfIsoDerivedComplex`, then gives `Hᵖ(Y_t, F_t) ≅ Hᵖ(K ⊗_𝟙 κ(t))`.
   By the dimension formula `finrank_homology_baseChange_eq`, `dim_{κ(t)} Hᵖ(Y_t, F_t)` is
   `homologyDim K p (ker 𝟙)`.
3. **The fibre over `t'`.** Take `φ = h.residueFieldMap t' : κ(t) → κ(t')`. Pasting the chosen
   pullback of `f` along `Spec φ` with the fibre square of `g` gives a cartesian square of `g`
   along `Spec κ(t') ⟶ Spec κ(t) ⟶ T`. By Mathlib's
   `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField` this bottom map is
   `T'.fromSpecResidueField t' ≫ h`. Since the given square `IsPullback h' g' g h` is cartesian,
   `IsPullback.of_right'` yields a cartesian square of `g'` along `T'.fromSpecResidueField t'`,
   whose top map `q` satisfies `q ≫ h' = (pullback.fst) ≫ (pullback.fst)`. The Library theorem
   `nonempty_relativeCohomology_iso_chosenPullback` compares its cohomology with that of the
   chosen fibre `Y'_{t'}`. The modules are matched by `Scheme.Modules.pullbackComp` and
   `Scheme.Modules.pullbackCongr`. With `homologyIsoOfIsoDerivedComplex` this gives
   `Hᵖ(Y'_{t'}, (h'^* F)_{t'}) ≅ Hᵖ(K ⊗_φ κ(t'))`, of dimension `homologyDim K p (ker φ)`.
4. **Conclusion.** Ring maps out of a field are injective, so `ker φ` and `ker 𝟙` are both the
   zero ideal of `κ(t)`. The two dimensions agree.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
