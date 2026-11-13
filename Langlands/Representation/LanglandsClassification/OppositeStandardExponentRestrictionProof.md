# Restriction of opposite standard exponents to a larger standard Levi: proof

Worker 5295, Task 5295. This module proves
`Langlands.Aubert.General.RepresentedParabolic.OppositeStandardExponentRestrictionStatement`
(R1) as `oppositeStandardExponentRestriction`. R1 is an intermediate claim of
the proof of Renard VII.4.2 (iii), printed p.244 / PDF p.250. The statement and
its correspondence with the source are documented in the Markdown of
`OppositeStandardExponentRestrictionStatement`.

## Notation

`P̄_J` is the published chosen opposite of the standard parabolic `P_J`
(`OppositeStandardJacquetFamily.datum`). Its Levi is the standard Levi `M_J`,
and `A_J → M_J` is its chosen split component (`component`), with map
`g_J : A_J → T`. For an exponent `x`, `realPart x` is the normalized real
part of its character. `fullRealPart … D x` is the unique lift of
`realPart x` to `Vstar T` that annihilates the coroots of `x.1`.

## Declarations

* `isNormalizedJacquetExponent_outer_of_fine_of_isAdmissible` (generic). This
  is the variant of the published
  `isNormalizedJacquetExponent_outer_of_fine_scheme` with an admissible source
  in place of a tempered one. It uses the published nested setting: a fine
  parabolic `p` with Levi `M`, an outer parabolic `q` with Levi `L`, and an
  inner parabolic `pL` of `L` with Levi `M`, satisfying `hPQ`, `hM` and `hPL`.
  Let `e : A → B` be a morphism of split components with
  `e ≫ b ≫ mL ≫ pL = a`. If `π` is admissible and `χ` is a normalized Jacquet
  exponent of `π` along the fine parabolic, then `χ ∘ e` is a normalized
  Jacquet exponent of `π` along the outer parabolic.
* `OppositeStandardJacquetFamily.isNormalizedJacquetExponent_val`: the
  character of an element `x` of the opposite family is a normalized Jacquet
  exponent for the opposite datum of its label. This unpacks the subtype
  membership.
* `OppositeStandardJacquetFamily.restrictExponent hadm z h`. Take an
  admissible `π`, an exponent `z` and a label `K` with `h : z.1 ⊆ K`. The
  result is the element of the opposite family with label `K` and character
  `z.2 ∘ e`, where `e : A_K → A_J` is the split-component morphism of the
  published nesting datum `Nesting.nestedData h`.
  `restrictExponent_fst` records that its label is `K`.
* `realPart_restrictExponent`: its real part is the restriction of
  `realPart z` along `e`.
* `restrict_eq_zero_of_mem_span`: restriction along `g_K` kills the real span
  of the roots in `K`.
* `fullRealPart_restrictExponent`: suppose `w` annihilates the coroots of `K`
  and `fullRealPart z − w` lies in the real span of the roots of `K`. Then the
  full real parameter of `restrictExponent hadm z h` is `w`.
* `oppositeStandardExponentRestriction`: the statement R1. The witness is
  `restrictExponent hadm z h`.

## Proof

1. **Outer exponent.** `isNormalizedJacquetExponent_outer_of_fine_of_isAdmissible`
   follows the published proof of `isNormalizedJacquetExponent_outer_of_fine`
   with one change. The published
   `isNormalizedJacquetExponent_nested_of_fine` puts `χ` in the iterated
   Jacquet module of `σ = r_q(π)` along `pL`, with the same split component
   `B`. The published `normalizedJacquetExponent_restrict` then restricts it
   to an exponent of `σ` on `A`. It needs `σ` admissible. Here this comes from
   the proved `arbitraryParabolicJacquetAdmissibility`, transported to the
   Levi points by `isAdmissible_comp_continuousMulEquiv` and
   `leviPointsEquiv`. The published version instead takes it from
   temperedness. The point-level compatibility of `e` follows from the
   scheme-level equation, as in `isNormalizedJacquetExponent_outer_of_fine_scheme`.
   Finally, `isNormalizedJacquetExponent_iff_leviEigencharacter` and
   `isGroupExponent_iff_isOpen_ker_and` turn the group exponent of `σ` back
   into a normalized Jacquet exponent.
2. **Restricted exponent.** `restrictExponent` applies step 1. The fine datum
   is `P̄_J`, the outer datum is `P̄_K`, the inner datum is `nestedData h`, and
   the morphism is its `e`. The hypotheses `hPQ`, `hM`, `hPL` and the
   compatibility of `e` are the published nesting lemmas
   `pointImage_opposite_p_le`, `levi_comp`, `inner_eq` and `e_comp_inner`.
3. **Real part.** `realPart_restrictExponent` is the naturality
   `Plancherel.SplitTorus.normalizedRealPart_comp_points` of normalized real
   parts under the morphism `e` of split tori. Its openness hypothesis on the
   kernel of `z.2` is part of being a normalized Jacquet exponent.
4. **Roots of `K` vanish on `A_K`.** For `α ∈ K`, restricting `1 ⊗ α` along
   `g_K` gives `1 ⊗ (g_K ≫ α)`. This is zero by
   `ParabolicRootPresentation.selectedRoot_restrict_eq_zero`, applied to the
   published standard root presentation of `K`. Span induction then gives
   `restrict_eq_zero_of_mem_span`.
5. **Full parameter.** `fullRealPart_eq_of_restrict_eq` characterizes the
   full parameter of the restricted exponent by two conditions: its
   restriction along `g_K` and the vanishing of its pairings with the coroots
   of `K`. The second condition is the hypothesis on `w`. For the first, the
   real part of the restricted exponent is computed as follows:

   `realPart(restricted) = e^*(realPart z)` (step 3)
   `= e^*(g_J^*(fullRealPart z))` (`restrict_fullRealPart`)
   `= (e ≫ g_J)^*(fullRealPart z)` (`rationalCharacterRestrictReal_comp_apply`)
   `= g_K^*(fullRealPart z)` (`e_g`).

   By step 4, `g_K^*(fullRealPart z − w) = 0`, so this equals `g_K^*(w)`.
6. `oppositeStandardExponentRestriction` introduces the data, then returns
   `restrictExponent`, `rfl` for the label, and step 5.

Only the admissibility of `π` is used. The finite-length hypothesis of the
statement and the minimality of the dynamic parabolic of `ν` are not needed.
The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
