# Unitary and nonunitary parts of a normalized Jacquet module

Author: Worker 6. Module `Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

Source: Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. VII.2.3, printed p.229 / PDF p.235, writes the normalized Jacquet module as

`r_P^G V = (r_P^G V)_0 ⊕ (r_P^G V)_+`,

where `(r_P^G V)_0` is the sum of the characteristic spaces `(r_P^G V)_χ` over the exponents `χ ∈ Exp(A_M, r_P^G V)` with `ℜ(χ) = 0`, and `(r_P^G V)_+` is the sum over those with `ℜ(χ) ≠ 0`. The same parts are used in VII.2.4 and VII.2.5 (printed pp.229–230 / PDF pp.235–236).

This module defines the two parts, records elementary lattice facts about them, and transports them to smooth representations of `M(F)`. It proves neither the direct-sum decomposition nor any temperedness statement.

## Setting

The variables are those of the published arbitrary-parabolic exponent construction `ArbitraryParabolic`: a nonarchimedean local field `k` with `[T2Space k]`, a group scheme `G` with `[IsAffineHom G.X.hom]` whose points carry the canonical topology `RationalPointFamily.pointTopology`, and the hypotheses `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`. A parabolic `p : P ⟶ G` (`hp`), a rational Levi `l : M ⟶ P` (`hl`), a matching geometric unipotent radical `r : U ⟶ P` (`hr`) with `hmul : IsIso (subgroupMultiplication l r)`, a split component `a : A.toGrp ⟶ M` (`ha : IsSplitComponent a`) and a smooth representation `π` of `G(F)` are fixed.

The weight spaces are the published `normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ`, the generalized eigenspace `(r_P^G π)_χ` of the split component acting on the published normalized Jacquet module `(jacquetFunctor p l r hp hr hl hmul).obj π`. The exponents are the published `IsNormalizedJacquetExponent`: `χ` has open kernel and its weight space is nonzero. The real part is the published `Plancherel.SplitTorus.normalizedRealPart` for the split torus `ha.isCentralSplitTorus.1.1`. It is the `q^(-s)` parameter, and Renard's raw-log real part `rawLogRealPart` is `-log q` times it. Since `q > 1`, the conditions `= 0` and `≠ 0` are the same for both parameters, so no normalization choice affects this module.

## Definitions

- `unitaryJacquetPart p l r hp hl hr hmul ha π`, Renard's `(r_P^G π)_0`: the supremum, in the lattice of subrepresentations of the normalized Jacquet module, of `normalizedJacquetWeightSpace … χ` over the `χ` with `IsNormalizedJacquetExponent … χ` and `normalizedRealPart … χ = 0`.
- `nonunitaryJacquetPart p l r hp hl hr hmul ha π`, Renard's `(r_P^G π)_+`: the same supremum over the exponents with `normalizedRealPart … χ ≠ 0`.

The supremum of subrepresentations has as underlying subspace the sum of the underlying subspaces (`unitaryJacquetPart_toSubmodule`, `nonunitaryJacquetPart_toSubmodule`, from the published `Langlands.Subrepresentation.toSubmodule_iSup`). These are Renard's sums of characteristic spaces.

## Elementary facts

- `normalizedJacquetWeightSpace_eq_bot_of_not_isNormalizedJacquetExponent`: if `χ` is not an exponent, its weight space is `⊥`. The proof combines the published `isNormalizedJacquetExponent_iff` and `normalizedJacquetWeightSpace_ne_bot_iff`, which show that both conditions are equivalent to `χ` being a generalized eigencharacter. So the open-kernel condition is automatic for a nonzero weight space.
- `normalizedJacquetWeightSpace_le_unitaryJacquetPart` and `normalizedJacquetWeightSpace_le_nonunitaryJacquetPart`: the weight space of an exponent with zero (resp. nonzero) real part lies in the unitary (resp. nonunitary) part.
- `unitaryJacquetPart_eq_iSup` and `nonunitaryJacquetPart_eq_iSup`: the exponent condition may be dropped from the supremum. Each part equals the supremum of the weight spaces of all characters with zero (resp. nonzero) real part, because non-exponents contribute `⊥`.

## Transport to `M(F)`

These declarations use the published Levi-point interface `ArbitraryParabolicLeviPoints`: the canonical topology `leviPointTopology l hl` on `M(F)` and the topological-group isomorphism `leviPointsEquiv p l hp hl : M(F) ≃ₜ* pointImage (l ≫ p)`.

- `leviUnitaryJacquetModule p l r hp hl hr hmul ha π` and `leviNonunitaryJacquetModule …` are the smooth representations of `M(F)` obtained from the published `SmoothRep.subrepresentation` of the Jacquet module on the respective part, pulled back along `leviPointsEquiv` with the published `SmoothRep.pullback`. `leviUnitaryJacquetModule_representation` and `leviNonunitaryJacquetModule_representation` state, by `rfl`, that `m ∈ M(F)` acts as `leviPointsEquiv p l hp hl m` acts on the part.
- `leviUnitaryJacquetModuleι …` and `leviNonunitaryJacquetModuleι …` are the inclusions into `(leviJacquetFunctor p l r hp hr hl hmul).obj π`, the published transported Jacquet module. Each is the image under `SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl)` of the published `SmoothRep.subtype`. `leviUnitaryJacquetModuleι_injective` and `leviNonunitaryJacquetModuleι_injective` state that the underlying linear maps are injective, since they are submodule inclusions.

## Provenance and scope

The two parts are Renard's definitions. The supremum presentation, the lemmas and the transport to `M(F)` are implementation content, needed because the published temperedness predicate applies to representations of `M(F)` itself.

The published `Langlands.unitaryCentralPart` (`Langlands/Representation/Exponents/UnitaryPart.lean`) is a related but different construction: it sums generalized eigenspaces of the full abstract center of an arbitrary group for characters of absolute value one. The parts here use the split component `A_M` acting on the normalized Jacquet module, as in VII.2.3, with the open-kernel exponents of the published VII.1.1 interface.

Not proved here:

- the direct-sum decomposition `r_P^G V = (r_P^G V)_0 ⊕ (r_P^G V)_+`, which follows from the decomposition of the Jacquet module into characteristic spaces in VII.1.1 for admissible `π` (published statement `ArbitraryParabolicExponentStatement`);
- the VII.2.3 lemma that `(r_P^G π)_0` is tempered when `π` is tempered;
- the VII.2.4 Frobenius reciprocity and square-integrability criterion, and the VII.2.5 geometric lemma.

These are separate statement units.
