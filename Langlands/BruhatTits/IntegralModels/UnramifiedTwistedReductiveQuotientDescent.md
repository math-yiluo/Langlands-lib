# Proof of the Frobenius descent of the reductive quotient

The theorem `Langlands.BruhatTits.IntegralModels.unramifiedTwistedReductiveQuotientDescent`
proves the published statement `UnramifiedTwistedReductiveQuotientDescentStatement.{u}`
at an arbitrary universe `u`. The statement is unchanged. The proof uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

Notation follows the statement. `K = inertiaFixedField F`, `O = fixedFieldIntegers F` and
`Ω = ResidueField O`, with the `𝓀[F]`-algebra structure `residueToFixedField F`. `θ_σ(g) =
c σ · σ(g) · (c σ)⁻¹` is the twisted conjugation, and `Frob` is the arithmetic Frobenius
`FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F] Ω`.

## Outline

The proof follows the route described in the statement's Markdown (Kaletha–Prasad,
Fact 2.10.16 and §9.2). The neutral model is descended along the inner twist to the ring
of integers `𝒪[F]` of `F`. The reductive quotient of the descended special fibre gives `R`.

1. **Inner-twisted descent of `D.neutral`.** The published
   `IntegralModel.exists_common_finiteInnerRecovery` gives a finite Galois, arithmetically
   unramified subextension `E` with a cocycle `d` on `Aut(E/F)` that recovers `c`, and the
   finite-level data `N`, `e`. `IntegralModel.recovery_at_liftAutomorphism` gives the
   recovery at lifted automorphisms. The new lemma `twisted_inverse_mem` turns `θ`-stability
   of `G^0(O)` into stability under the inverse twists `g ↦ σ⁻¹((c σ)⁻¹ g c σ)`, which is
   the second stability hypothesis of the descent. Then:
   - `IntegralModel.givenFiniteInnerModel` is a model `M` over `𝒪[F]` of the inner form
     `H` defined by `d`;
   - `givenFiniteInnerModel_smooth` shows `M` is smooth;
   - `givenFiniteInnerModelIso` is an isomorphism `ρ` from the unramified base change of
     `M` to `D.neutral`, over the generic comparison `ψ : H_K ≅ G_K`;
   - `finiteInnerInertiaGenericComparison_innerGaloisCompatible` shows that `ψ` carries
     the Galois descent data of `H_K` to the `c`-twisted descent data of `G_K`
     (`InnerGaloisCompatible`).

   The rest of the proof is the lemma `exists_residueDescent`. It takes an arbitrary
   smooth `M`, an isomorphism `ρ` and a compatibility `hall` of this form.

2. **Twisted conjugation is descent transport** (section `Core`). The *model projection*
   of an integral section `s` of `D.neutral` is the projection to `M` of `ρ⁻¹(s)`. Let
   `σ ∈ Aut(K/F)`, and let `σ_O` be the induced automorphism `fixedIntegerBaseAut F σ` of
   `Spec O`. `exists_twisted_section` gives an integral section `s'` with
   - generic point `θ_σ` of the generic point of `s`, and
   - model projection `σ_O` composed with the model projection of `s`.

   The section `s'` is the canonical descent transport (`descentBasePoint`) of `ρ⁻¹(s)`
   along `σ_O`, carried back through `ρ`. Its generic point is computed in two steps:
   - `integralPointMap_descentBasePoint`: descent transport of integral sections of `M_O`
     induces Galois conjugation `rationalConjugate` on generic points. Generic points are
     compared through their projections to `M` (`generic_hom_ext`).
   - `map_rationalConjugate_of_innerGalois`: `ψ` turns Galois conjugation into twisted
     conjugation by `c`.

3. **Residue square** (section `Residue`). The hypothesis `hφ` says that `φ` reduces to
   `x ↦ x^q`. By `residueBaseMap_frobenius`, the square of spectra formed by reduction
   `Spec Ω → Spec O`, `φ_O` and `Spec(Frob)` commutes. `specialFibreIso` is the comparison
   between the base change of `M`'s special fibre from `𝓀[F]` to `Ω` and the special fibre
   of `D.neutral`. It is built from two base-change comparisons (`Descent.pullbackComparison`)
   along the square `fixedResidueBaseMap_square F`, followed by `ρ`.
   `reduction_projection_frobenius` combines the residue square with step 2. When the model
   projections satisfy `proj(s') = φ_O ∘ proj(s)`, the reductions of `s'` and `s` satisfy
   the corresponding Frobenius relation after projection to `M`.

4. **The group `R` and the isomorphism `e`** (`exists_residueQuotient`,
   `exists_residueDescent`). The special fibre `M_𝓀` is smooth and affine. It is connected
   because connectedness of the fibres descends from `D.neutral` through `ρ`
   (`hasConnectedFibres_of_baseChangeUnramified`, `hasConnectedSpecialFibre_of_hasConnectedFibres`).
   - `unipotentRadicalExistence` and `unipotentRadicalQuotient` give the quotient
     `π : M_𝓀 → R` by the unipotent radical, with `R` pseudo-reductive.
   - `R` is connected reductive because `𝓀[F]` is perfect (`perfectFieldPseudoReductive`).
   - The unipotent radical commutes with the separable algebraic extension `Ω/𝓀[F]`
     (`separableAlgebraicUnipotentRadical`). After transport through `specialFibreIso`, its
     range is the radical of `Q` (`range_eq` with `hQ.1`).
   - The generic lemma `isFppfQuotient_transport` therefore shows that
     `specialFibreIso⁻¹ ≫ π_Ω` is an fppf quotient of the special fibre of `D.neutral` by the
     radical of `Q`. `Q.projection` is another such quotient (`hQ.2.1`).
   - `FppfQuotientComparison.iso` gives `e : R_Ω ≅ Q.quotient`, and
     `FppfQuotientComparison.fac` gives `Q.projection ≫ e⁻¹ = specialFibreIso⁻¹ ≫ π_Ω`.
     The quasi-compactness hypotheses come from `quasiCompact_hom_left`.

5. **Frobenius compatibility** (`residueQuotient_frobenius`). Let `g ∈ G^0(O)` with
   `θ_φ g ∈ G^0(O)`. Write `g` as the generic point of an integral section `s`
   (`D.neutralSectionsEquiv`), and take `s'` from step 2 with `σ = φ`. Then `θ_φ g` is the
   generic point of `s'`. Step 3 relates the reductions of `s` and `s'`. Reductions are
   transported through `specialFibreIso⁻¹` (`comparisonIso_inv_descentBasePoint`) and then
   through `π_Ω` and `e⁻¹` using the factorization of step 4 (`map_inv_descentBasePoint`,
   with `descentBasePoint_map`). This yields
   `e⁻¹(Q.parahoricReduction(θ_φ g)) = Frob(e⁻¹(Q.parahoricReduction g))`, the conclusion of
   the statement.

The final theorem instantiates step 1 and applies `exists_residueDescent`. It also
supplies `Fintype 𝓀[F]`, the residue algebra structure and the algebraicity of `Ω` over
`𝓀[F]` (from `fixedFieldResidueIsAlgClosure`).

## Implementation notes

- In the section `General`, the lemmas `comparisonIso_inv_descentBasePoint`,
  `map_inv_descentBasePoint` and `comparison_map_inv_descentBasePoint` state all group
  schemes and comparison isomorphisms as variables. The concrete objects are matched with
  them by `rfl` and `HEq.rfl` arguments. Otherwise the kernel must unify large composites
  whose implicit objects are written in different but definitionally equal forms, and
  type-checking does not finish.
- `square_point_eq` takes its implicit objects from the compatibility hypothesis `hall σ`,
  for the same reason.
- The local instances `coreIntegerAlgebra`, `coreIntegerTower` and `coreResidueAlgebra`
  are definitionally the instances used by the statement and the Library. They are named
  so that the sections can share them.

## Ingredients

All ingredients are published Library results. The supporting lemmas in the namespace
`Langlands.BruhatTits.IntegralModels.TwistedResidueFrobenius` are proved in this module and
are not separate statements.
