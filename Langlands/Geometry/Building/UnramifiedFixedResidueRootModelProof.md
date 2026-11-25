# Proof of fixed-point residue-root models

Module `Langlands.Geometry.Building.UnramifiedFixedResidueRootModelProof`.

`Langlands.Geometry.Building.unramifiedFixedResidueRootModel` proves the
published statement
`Langlands.Geometry.Building.UnramifiedFixedResidueRootModelStatement.{u}`,
with exactly that proposition as its type. The universe is arbitrary and both
characteristics are allowed. Every binder and hypothesis of the statement is
kept, including the local `HenselianLocalRing ↥𝒪[F]` instance and the four `let`
bodies `fixed`, `φ`, `P`, `Q`. No premise, unproved proposition or new axiom is
added.

## Notation

`F` is the nonarchimedean local field, `K = inertiaFixedField F` and
`O = fixedFieldIntegers F`. `iS : S → G` is the maximal split torus and
`f : S → T` the factorization through `iT`, whose base change `iT_K` is
maximal split. `D` and `C` are the upper apartment and centralizer datum, with
Ω-compatibility `hDC`. `x` is a Galois-fixed apartment point. `φ x` is the
torus-then-field restricted root function family.

## The constructed objects

Fix `x` with `fixed x`.

- The models. The published `unramifiedFixedRecoveredParabolicModels`
  (`UnramifiedNearbyParabolicComparisons`) supplies:
  - actual lower and upper relative-component models `L` and `E`;
  - a compatible unramified recovery `e`;
  - the equality `hfull` of `E.full.integralPoints` with the character
    kernel intersected with the full pointwise fixer of `{x}`;
  - the nearby parabolic root comparisons `hnear`.

  Take `D₀ = L`.
- The torus. `exists_closedSplitIntegralTorus_of_fullRecovery`
  (`UnramifiedRecoveredTorus`) gives `T₀ : IntegralTorusData L S iS` with
  `T₀.IsClosedSplit`. Its splitness is the witness `hT₀`.
- The quotient. `SpecialFibreQuotientData.exists_isReductiveQuotient L` gives
  `Q₀` with `Q₀.IsReductiveQuotient`.

## The six clauses

1. `IsClosedSubgroup T₀.inclusion` is the second part of `T₀.IsClosedSplit`.
2. `T₀.HasMaximalSplitSpecialFibre` comes from
   `IntegralTorusData.satisfiesTorusClause_of_generic`
   (`UnramifiedRecoveredTorusClause`), over the Henselian ring `𝒪[F]`.
3. `Q₀.IsReductiveQuotient` is the quotient construction.
4. Maximality of `T₀.specialFibreInclusion ≫ Q₀.projection` is the published
   `IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel`. It
   applies to the smooth connected unipotent radical and its fppf quotient
   over the finite, hence perfect, residue field, together with clause 2. This
   is the argument of `isMaximalSplitTorus_quotientTorusInclusion` in
   `CommonTorusQuotientMaximality`.
5. Let `a` be a relative root and `g ∈ U_a(F)`.
   - Integrality is `mem_neutral_integralPoints_iff_nonnegative_restrictedDepth`
     (`UnramifiedRootIntegrality`).
   - If `g ∈ Q₀.positivePoints`, then `0 < φ x a g` by the published
     `strictPositive_of_mem_positivePoints_of_parabolicRootComparisons`
     (`UnramifiedRootRadicalPositivity`) and `hnear`.
   - The converse is `mem_positivePoints_of_pos_restrictedDepth` below.
6. For an upper affine root `ψ` with `ψ x = 0` and `ψ.linear ∘ P ≠ 0`, the
   lemma `exists_quotient_root_of_vanishing_affineRoot` below gives:
   - an upper root `b` with `ψ.linear = rootForm iT_K b`;
   - a lower root `a` with `f_K ≫ b = a_K`;
   - membership of `T₀.characterSpecialization hT₀ a` in the roots of the
     quotient torus.

   The published `rootForm_comp_torusFieldTranslationMap_of_comp_eq`
   (`UnramifiedAffineRootRestrictionReduction`) then gives
   `(rootForm iS a).comp Q = ψ.linear.comp P`. This is the required identity
   with `c = 1`.

## The upstairs model

The helper declarations in section `Recovered` use the base change
`L.baseChange O K`. By `e.full_integralPoints_eq` and `hfull`, its full
integral points are the upper full fixer of `{x}`
(`baseChange_full_integralPoints_of_recovery`). For the building datum
`MaximalUnramified.buildingDataOfApartment hG hiT D C hDC`:

- `rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer` gives
  `HasRootFixerIntersections` for this base change
  (`baseChange_hasRootFixerIntersections`);
- `unramifiedIntegralSplitTorusData` followed by `factorNeutral` gives the
  closed split upper torus `baseChangeApartmentTorus` with generic inclusion
  `iT_K`.

No equality of the whole neutral subgroup with a zero-subgroup fixer (KP
Theorem 8.3.13, `UnramifiedParahoricModelStatement`) is used.

## Clause 5, strictly positive depth: `mem_positivePoints_of_pos_restrictedDepth`

Let `0 < φ x a g`.

1. By `mem_positivePoints_iff_unramifiedBaseChange`
   (`UnramifiedQuotientBaseChange`), it suffices to show that
   `rationalExtend g` is positive for `Q₀.unramifiedBaseChange`. That quotient
   is reductive by `isReductiveQuotient_unramifiedBaseChange`.
2. Choose a real `r > 0` with `r ≤ φ x a g`. The published
   `rootFiltration_torusFieldRestrictedRootFunctionFamily` turns the depth
   condition into membership of `rationalExtend g` in
   `torusRestrictedRootDepthSubgroup`. This is the supremum of the upper
   filtration subgroups `U_{χ, x, m r}` over relative roots `χ` of `iT_K`
   with `f_K ≫ χ = m · a_K`, `m > 0`.
3. Each generator `u` has positive depth at `x`, so it lies in the root fixer
   of `{x}`, and hence in the neutral integral points by the root
   intersections. `mem_positivePoints_iff_of_rootFixerIntersections`
   (`UnramifiedRootIntersectionReduction`) then makes it positive. This is the
   positivity half of KP Lemma 8.4.4 over `K`, proved from integral opposite
   factors and V5 for the upper valuation.
4. Positive points form a subgroup, so the whole supremum is positive.

## Clause 6, vanishing affine roots: `exists_quotient_root_of_vanishing_affineRoot`

1. The quotient `Q₀.baseChange O K` (`FacetRootSignBaseChange`) is reductive by
   `isReductiveQuotient_baseChange`, since `𝓀[F] → O/𝔪` is separable and
   algebraic.
2. `exists_quotient_root_of_incidentAffineRoot_of_rootFixerIntersections`
   gives an upper relative root `b` with `ψ.linear = rootForm iT_K b`, whose
   canonical specialization through the upper torus is a root of that
   quotient. This is KP Proposition 9.4.23 over `K` for the point `x`.
3. `exists_torusHom_of_baseChange` (`QuotientRootCoefficientDescent`) maps the
   base change of `T₀.torus` into the upper torus, compatibly with both
   inclusions. Its generic fibre is induced by `f_K`. The ring `O` is a
   Henselian discrete valuation ring with algebraically closed residue field.
4. Let `ψb` be the integral character with generic character `b`, and let `m`
   be the integral character of `T₀.torus` whose base change is `ρ ≫ ψb`.
   `baseChange_genericCharacter_eq_of_baseChangeComparisonGenericMap` gives
   `f_K ≫ b = a_K` for `a = T₀.genericCharacter m`.
5. If `m = 0`, then `f_K ≫ b = 0`. By `eval_descentCocharacterMap_of_comp_eq`
   this forces `ψ.linear ∘ P = 0`, which is excluded.
6. `specialCharacter_mem_roots_of_baseChange` descends the upper root to the
   root `T₀.characterSpecialization hT₀ a` of the original quotient, through
   restriction to the subtorus and the residue-field extension.
7. `relativeRoots_subset_specialFibre` (`ReductiveQuotientRoots`) and
   `mem_relativeRoots_characterSpecialization_iff` (`IntegralTorusRootSupport`)
   show that `a` is a relative root of `iS`.

## Provenance

The implemented route follows the structure of Kaletha–Prasad, but it uses the
Library's actual recovered models instead of the Bruhat–Tits group schemes.
The source is Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`:

- Proposition 9.4.9 and Axiom 4.1.22(4) give the comparisons in clause 5.
- Propositions 9.4.23 and 9.4.25 give the quotient roots and the maximal split
  torus image.
- The proof of Proposition 9.4.28 gives base change to the maximal unramified
  extension and restriction of roots, which yield clause 6.

The constant dependency closure of the theorem was checked:
`UnramifiedSpecialPointDescentStatement`,
the building-descent statements, `UnramifiedRootSpecializationStatement` and
`UnramifiedRootJumpDescentStatement` occur in none of its Langlands constants,
so no result consuming them is used.
