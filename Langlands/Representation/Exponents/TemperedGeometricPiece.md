# The unitary part of one piece of the geometric lemma (Renard VII.2.5)

Author: Worker 1221. Module `Langlands.Representation.Exponents.TemperedGeometricPiece`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. This is an internal supporting
module for the proof of Renard VII.2.5 (`TemperedGeometricLemmaStatement`). It treats one
piece of the geometric lemma at a time. It shows that the zero-real-part selection of the
piece `i^L_{Q'} ∘ ι ∘ r^M_{P'} ρ` is the piece `i^L_{Q'} ∘ ι ∘ (r^M_{P'} ρ)_0`
(`D.unitaryPieceRep`) of the target statement. The passage from the pieces to a filtration
of `(r_Q^G i_P^G ρ)_0` is separate work (Worker 1725's `LeviUnitaryFiltration`).

## Jacquet-level lemmas

These lemmas are in section `JacquetParts`. The setting is a group scheme `G` over a
nonarchimedean local field `k` with `[IsAffineHom G.X.hom]`, the canonical topology on
`G(k)`, `[LocallyCompactSpace G(k)]` and `[NonarchimedeanGroup G(k)]`. Also given are a
rational parabolic `p : P ⟶ G` with rational Levi `l : M ⟶ P`, matching radical `r` and
`hmul`, a split component `a : A → M` (`ha : IsSplitComponent a`) and a smooth
representation `π` of `G(k)`. `IsGeneralizedEigencharacter σ χ` means that some
characteristic space `characterSpace σ χ d` is nonzero. The split component acts through
`splitComponentPointsMap (l ≫ p) a`.

| Lean name | Statement |
| --- | --- |
| `exists_mem_normalizedJacquetWeightSpace_of_subrepresentation` | Let `S` be a subrepresentation of the normalized Jacquet module `(jacquetFunctor p l r …).obj π`, and let `χ` be a generalized eigencharacter of `A(k)` on `S`. Then `χ` is a normalized Jacquet exponent (`IsNormalizedJacquetExponent … ha π χ`), and some nonzero `v ∈ S` lies in `normalizedJacquetWeightSpace … ha π χ`. |
| `normalizedRealPart_eq_zero_of_unitaryJacquetPart` | A generalized eigencharacter `χ` of `A(k)` on the unitary part `unitaryJacquetPart … ha π` is a normalized Jacquet exponent with `normalizedRealPart χ = 0`. |
| `normalizedRealPart_ne_zero_of_nonunitaryJacquetPart` | A generalized eigencharacter `χ` of `A(k)` on the nonunitary part `nonunitaryJacquetPart … ha π` is a normalized Jacquet exponent with `normalizedRealPart χ ≠ 0`. |

In all three, `normalizedRealPart` is `Plancherel.SplitTorus.normalizedRealPart
ha.isCentralSplitTorus.1.1`.

Proofs. For the first, push a nonzero characteristic vector of `S` into the Jacquet module
with `subrepresentationInclusion` (`map_mem_characterSpace_of_intertwiningMap`). It stays
nonzero, which gives the exponent (`isGeneralizedEigencharacter_of_map_ne_zero`,
`isNormalizedJacquetExponent_iff`), and it lies in the weight space
(`mem_normalizedJacquetWeightSpace`). For the other two: if the real part had the wrong
value, the weight space of `χ` would lie in the other part
(`normalizedJacquetWeightSpace_le_nonunitaryJacquetPart`, resp.
`normalizedJacquetWeightSpace_le_unitaryJacquetPart`). The two parts are disjoint
(`unitaryJacquetPart_disjoint_nonunitaryJacquetPart`), so the nonzero vector would be zero.

## The piece theorem

`GeometricLemmaIntersectionDatum.nonempty_selectedWeightPart_pieceFunctor_equiv`.

Setting: `k`, `G` with `[IsAffineHom G.X.hom] [Smooth G.X.hom]`, the canonical topology on
`G(k)`, `[LocallyCompactSpace G(k)]` and `[NonarchimedeanGroup G(k)]`. Further, rational
parabolics `P = M N` and `Q = L U` of `G` as in the target statement, and an intersection
datum `D : GeometricLemmaIntersectionDatum p l r … q lQ rQ … z` of the published
represented geometric lemma. Hypotheses:

- `hcompact : ArbitraryParabolicQuotientCompactStatement.{u}`: for every connected
  reductive group over a nonarchimedean local field and every parabolic `p`, the quotient
  of the rational points by `pointImage p` is compact;
- a split component `aL : AL → L` (`haL : IsSplitComponent aL`) and a parabolic root
  presentation `presQ : ParabolicRootPresentation q lQ aL`;
- a split component `a' : A' → D.M'` (`ha' : IsSplitComponent a'`).

The statement installs on `M(F)` and `L(F)` the same canonical topologies and derived
instances as `TemperedGeometricLemmaStatement`. It then asserts: for every smooth complex
representation `ρ` of `M(F)` such that

- `ρ` is tempered (`IsNormalizedExponentTempered hl.isConnectedReductive ρ`), and
- the normalized Jacquet module `(jacquetFunctor D.p' D.l' D.r' …).obj ρ` of `ρ` along
  `P'` is admissible,

there is an equivalence of representations of `L(F)` (`Representation.Equiv`) from

`selectedWeightPart (D.pieceFunctor.obj ρ).ρ (rationalPoints.map aL) _ (fun χ => normalizedRealPart haL.isCentralSplitTorus.1.1 χ = 0)`

to `(D.unitaryPieceRep ha' ρ).ρ`. The source is the sum of the generalized weight spaces of
`AL(F)` with zero normalized real part in the published piece `D.pieceFunctor.obj ρ` of
the geometric lemma. Its form is the one used by Worker 1725's
`exists_leviUnitaryJacquetInductionFiltration_of_isGluedFrom`.

### Proof

Write `Jac` for the Jacquet module of `ρ` along `P'`, and `J`, `J₀`, `J₁` for
`leviJacquetFunctor … ρ`, `leviUnitaryJacquetModule … ha' ρ` and
`leviNonunitaryJacquetModule … ha' ρ`, all representations of `M'(F)`. Write `E` for
restriction along `D.e : L'(F) ≃ M'(F)` and `I` for `leviInductionFunctor` along `Q'`.
Then `D.pieceFunctor.obj ρ` is `SmoothRep.toRep.obj (I (E J))`, and
`D.unitaryPieceRep ha' ρ` is `SmoothRep.toRep.obj (I (E J₀))`.

1. Split components. Write `a' = b ≫ D.φ.hom` with `b : A' → L'`, which is a split
   component of `L'` (`IsSplitComponent.comp_iso`). `exists_isCentralSplitTorus_factor`
   and `IsSplitComponent.exists_factor` give `f : AL → A'` with
   `f ≫ b ≫ D.lQ' ≫ D.q' = aL`.
2. Splitting. Since `Jac` is admissible, its unitary and nonunitary parts are complementary
   (`unitaryJacquetPart_isCompl_nonunitaryJacquetPart_of_admissible`). The projections
   `SmoothRep.subrepresentationProjection` (from `SelectedWeightSplitting`), transported to
   `M'(F)`, and the inclusions `leviUnitaryJacquetModuleι`, `leviNonunitaryJacquetModuleι`
   give `ι₀ ∘ π₀ + ι₁ ∘ π₁ = id` on `J`. `E` does not change vectors, and
   `normalizedInductionFunctor_map_add_map` gives the same identity on `I (E J)`.
   `I (E ι₀)` is injective (`normalizedInductionFunctor_map_injective`,
   `leviUnitaryJacquetModuleι_injective`).
3. Admissibility. `J` is admissible (`isAdmissible_comp_continuousMulEquiv`), so are `J₀`
   and `J₁` (`isAdmissible_of_injective`) and their restrictions along `D.e`. Their
   inductions are admissible by
   `leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement hcompact`.
4. Weights of induced parts. Let `S` be `unitaryJacquetPart` or `nonunitaryJacquetPart`, and
   let `X` be its transport to `M'(F)`. Since `I (E X)` is admissible, its generalized
   weight spaces for `AL(F)` span (`generalizedWeightSpace_iSup_eq_top` with
   `CentralDecomposition.admissible_centerFinite`). It therefore suffices
   (`selectedWeightPart_eq_top_of_forall`) to check the predicate on each `χ` with a
   nonzero weight space. Such a `χ` is a generalized eigencharacter
   (`generalizedWeightSpace_ne_bot_iff`). By the published
   `exists_isGeneralizedEigencharacter_of_leviInduction` (Renard VII.1.1 (i)) it is
   `ψ ∘ f` for a generalized eigencharacter `ψ` of `A'(F)`, acting through `b`, on `E X`.
   The action of `A'(F)` through `b` on `E X` is the action of `A'(F)` through
   `b ≫ D.φ.hom` on `S` (`leviPointsEquiv_comp_map`, `D.e_apply`).
5. Unitary part. By `normalizedRealPart_eq_zero_of_unitaryJacquetPart`, `ψ` is an exponent
   with `normalizedRealPart ψ = 0`. Its kernel is open
   (`isNormalizedJacquetExponent_iff_isOpen_ker_and`), so `normalizedRealPart_comp_points`
   expresses `normalizedRealPart (ψ ∘ f)` as the real restriction along `f` of
   `normalizedRealPart ψ`. This restriction is `0`.
6. Nonunitary part. By `normalizedRealPart_ne_zero_of_nonunitaryJacquetPart`, `ψ` is an
   exponent with `normalizedRealPart ψ ≠ 0`. Temperedness of `ρ`, through
   `IsNormalizedExponentTempered.parabolic` for `(D.p', D.l', b ≫ D.φ.hom)`, gives a
   presentation `presM` and puts `normalizedRealPart ψ` in `presM.nonnegCone`. As in step
   5, `normalizedRealPart (ψ ∘ f)` is the restriction of `normalizedRealPart ψ`, and it is
   nonzero by `restrictReal_ne_zero_of_mem_nonnegCone` (`TemperedGeometricPieceCone`).
7. Steps 2, 5 and 6 are the hypotheses of `nonempty_selectedWeightPart_equiv`
   (`SelectedWeightSplitting`) for `i₀ = I (E ι₀)`, `i₁ = I (E ι₁)` and the induced
   projections. It gives the equivalence. Its target `I (E J₀)` is
   `(D.unitaryPieceRep ha' ρ).ρ` by definition.

## Provenance and scope

This is derived content for the proof of the Proposition of Renard VII.2.5 (David Renard,
*Représentations des groupes réductifs p-adiques*, 2026, printed p.230 / PDF p.236).
Renard says the only change from VI.5.1 is to take the tempered part
`(r^M_{w·Q∩M} W)_0` in the pieces. He then shows that the exponents for `A_L` of the
pieces built from `(r^M_{w·Q∩M} W)_0` are unitary, and that those built from
`(r^M_{w·Q∩M} W)_+` have nonzero real part. The piece theorem is this comparison for one
represented intersection datum, with the conclusion stated as an equivalence of the
selected part.

The Lean route differs in three ways:

- Renard proves the unitary half by noting that the piece is tempered (VII.2.2 and
  Remark VII.2.1). The Lean proof instead restricts exponents with VII.1.1 (i), as in the
  nonunitary half. VII.2.2 and VII.2.3 are not used.
- Renard reduces to standard `P` and `Q` and uses simple roots and `w ∈ W_{L,M}`. The Lean
  proof works with the represented intersection datum and the cone argument of
  `TemperedGeometricPieceCone`.
- The splitting `r^M_{P'} ρ = (·)_0 ⊕ (·)_+` uses admissibility of the Jacquet module. That
  admissibility is a hypothesis here, as is quotient compactness
  (`ArbitraryParabolicQuotientCompactStatement`), which gives admissibility of the induced
  pieces. The root presentation `presQ` of `Q` is also a hypothesis.

The theorem does not prove the geometric lemma VI.5.1, the existence of the presentation
`presQ`, Jacquet admissibility or quotient compactness. It does not assemble the
filtration of `(r_Q^G i_P^G ρ)_0`.
