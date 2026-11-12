# The depth-zero reduction map of supplied KP models

This module formalizes, for supplied models and quotients, the reduction
statement of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
13.2.6 (printed p. 470 / PDF p. 501). There KP compose reduction
`G_x^0(o) → \underline{G}_x^0(f)` with the projection to the maximal
reductive quotient. They state that the composite `P_{x,0} → \bar G_x(f)` is
surjective with kernel `P_{x,0+}`, so `P_{x,0}/P_{x,0+}` is identified with
`\bar G_x(f)`. The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The construction is derived from published interfaces and makes no model,
radical, quotient or building existence assertion.

## Setting

`R` is a domain with fraction field `K`, in an arbitrary universe `u`, and `G`
is a group scheme over `Spec K`. The Lean `K` is the fraction field of `R`. It
is not KP's maximal unramified extension. The data are the published
`D : RelativeComponentModelData R K G` and `Q : SpecialFibreQuotientData D` of
`Langlands.BruhatTits.IntegralModels.RelativeComponent` and
`Langlands.BruhatTits.IntegralModels.SpecialFibre`. The smooth model
`D.neutral` with connected fibres plays the role of KP's `G_x^0`. Its actual
special fibre `D.neutral.specialFibre` plays the role of
`\underline{G}_x^0`. `Q.radical`, `Q.quotient` and `Q.projection` play the
roles of the unipotent radical, the maximal reductive quotient `\bar G_x` and
the quotient map. Nothing identifies `D.neutral` with a Bruhat–Tits parahoric
group scheme, or `D.neutral.integralPoints` with a parahoric subgroup.

The theorems use only the first two conjuncts of `Q.IsReductiveQuotient`.
`hrad : IsUnipotentRadical Q.radicalInclusion` says that the radical is the
represented ground-field unipotent radical. `hQ` says that the projection is
the represented fppf quotient by the subgroup functor of that radical.
Connected reductivity of the quotient is never used.

## Declarations

For a general domain base:

- `RelativeComponentModelData.neutralSectionsEquiv` is the group isomorphism
  from `D.neutral.integralSections = G_R^0(R)` onto its image
  `D.neutral.integralPoints = G^0(R) ≤ G(K)`. It is `MonoidHom.ofInjective`
  of the injectivity theorem `integralPointMap_injective` in
  `Langlands.GroupScheme.IntegralModel.HenselianReduction`.
  `neutralSectionsEquiv_apply` records that the underlying generic point is
  `D.neutral.integralPointMap x`.

For a local domain base (`IsLocalRing R`):

- A local instance records that the structural morphism of the neutral special
  fibre is affine, as the base change of the affine model.
- `projectionPoints` is `rationalPoints.map Q.projection`, the map
  `\underline{G}_x^0(f) → \bar G_x(f)` on residue-field points.
- `ker_projectionPoints hQ` identifies its kernel with `Q.radicalPoints`.
  It uses `mem_range_kernelι_iff` and the kernel clause of
  `RelativeRoot.IsFppfQuotient`, both on the residue spectrum.
- `projectionPoints_surjective hrad hQ` additionally assumes a perfect residue
  field, as in KP Proposition 2.4.3 (printed p. 84 / PDF p. 115, in the
  perfect-field setting of §2.4(c), printed p. 83 / PDF p. 114). KP derive it
  from the Galois cohomology of Lemma 2.4.2. The Lean proof instead uses a
  scheme section. The radical is smooth by `hrad`. It is affine by
  `HomogeneousQuotient.affine_subgroup_of_closed`. It is split unipotent by
  the published `perfectFieldUnipotentSplit`, using its connectedness and
  unipotence. `HomogeneousQuotient.fppf_section_of_split_unipotent_torsors`,
  with the published proof `splitUnipotentAffineTorsorStatement`, then gives a
  scheme section `s` of the projection, and `y ↦ y ≫ s` is a right inverse on
  points.
- `reductiveReduction` is `projectionPoints ∘ D.neutral.reduction`, the
  composite `G_R^0(R) → \underline{G}_x^0(f) → \bar G_x(f)`.
  `ker_reductiveReduction hQ` identifies its kernel with `Q.positiveSections`,
  the reduction preimage of the radical's residue-field points.
- `parahoricReduction` is the same map on `G^0(R) ≤ G(K)`, precomposed with
  the inverse of `neutralSectionsEquiv`. The simp lemma
  `parahoricReduction_neutralSectionsEquiv` evaluates it on a section.
- `ker_parahoricReduction hQ` identifies its kernel with
  `Q.positivePoints.subgroupOf D.neutral.integralPoints`. This is the
  subgroup `G(K)^{0+}` of `SpecialFibre`, viewed inside `G^0(R)`. The proof
  transports `ker_reductiveReduction` along the injective integral-point map.

For a Henselian local domain base with perfect residue field
(`HenselianLocalRing R` and `PerfectField (IsLocalRing.ResidueField R)`):

- `reductiveReduction_surjective hrad hQ` composes the Henselian lifting
  theorem `IntegralModel.reduction_surjective`, applied with
  `D.neutral_smooth`, with `projectionPoints_surjective`. This is how KP
  obtain the surjectivity in 13.2.6 from Lemma 8.1.3 and Proposition 2.4.3.
  `parahoricReduction_surjective hrad hQ` is the same statement on `G^0(R)`.
- `depthZeroQuotientEquiv hrad hQ` is the first isomorphism theorem
  `QuotientGroup.quotientKerEquivOfSurjective` for `parahoricReduction`.
  It is a group isomorphism
  `D.neutral.integralPoints ⧸ Q.parahoricReduction.ker ≃* rationalPoints Q.quotient`.
  The quotient is taken by the kernel, which is normal automatically. By
  `ker_parahoricReduction`, this kernel is `G(K)^{0+} ∩ G^0(R)`. No separate
  normality instance or restated equivalence with
  `Q.positivePoints.subgroupOf D.neutral.integralPoints` is declared.

## Relation to the source

KP's kernel in 13.2.6 is the Moy–Prasad subgroup `P_{x,0+}`. KP get it from
Corollary 8.4.12 (printed p. 306 / PDF p. 337), which identifies the preimage
of the unipotent radical's points with `G(K)_{Ω,0+}`. The Lean kernel is the
radical preimage `Q.positivePoints`. This is the subgroup `G(K)^{0+}_F` that
KP Axiom 4.1.22(7) (printed pp. 163–164 / PDF pp. 194–195) uses and that
`SpecialFibre` defines. Corollary 8.4.12, which compares it with the
Moy–Prasad filtration subgroup, is not formalized.

The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, do not
amend 13.2.6, Lemma 8.1.3, Proposition 2.4.3 or Corollary 8.4.12. Their
Chapter 8 corrections (PDF pp. 37–38) restate where a perfect residue field
is assumed: from §8.3 on, including §8.4. Lemma 8.1.3 does not use that
assumption.

The hypotheses are mathematically met in KP's setting. There `o` is a
Henselian discrete valuation ring with perfect residue field, and the
Henselian ring of integers of the maximal unramified extension, for KP's
"same over K" sentence, is another such base. This module supplies no such
instances or models. It also does not formalize the cokernel description
`\bar G_x = cok(\bar G_{x,0+} → \bar G_{x,0})` of 13.2.6, which depends on
Theorem 8.5.2 and 8.5.17. Topologies, openness of the kernel, inflation and
compact induction are separate work.
