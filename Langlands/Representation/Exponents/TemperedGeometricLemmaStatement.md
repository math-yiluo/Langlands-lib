# The geometric lemma for tempered representations (Renard VII.2.5)

Author: Worker 6. Module `Langlands.Representation.Exponents.TemperedGeometricLemmaStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. One helper definition `GeometricLemmaIntersectionDatum.unitaryPieceRep` and the statement `TemperedGeometricLemmaStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.2.5, Proposition, printed p.230 / PDF p.236, with its proof on the same page. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, the Proposition says: let `P = MN` and `Q = LU` be two parabolic subgroups of `G` and `(ρ, W)` a tempered representation of `M`. Then `r_Q^G(i_P^G(ρ, W))_0` has a filtration whose graded pieces are the

`i^L_{L ∩ w⁻¹·P} ∘ w ∘ (r^M_{w·Q ∩ M} W)_0`,

where `w` runs through the set `W_{Q,P}` of V.4.7 parametrizing the orbits of `Q` on `X = P\G`. The proof says that the only change from the geometric lemma VI.5.1 is that one takes the tempered part `(r^M_{w·Q∩M} W)_0` in the formula. It then shows, for standard `P` and `Q`, that the exponents of the pieces built from `(r^M_{w·Q∩M} W)_0` are unitary and that those of the pieces built from `(r^M_{w·Q∩M} W)_+` have nonzero real part.

Here `V_0` is the unitary part of VII.2.3 (printed p.229 / PDF p.235): the sum of the characteristic spaces of the split component over the exponents with zero real part. In the pieces, `(r^M_{w·Q∩M} W)_0` is taken for the split component of the Levi `w·L ∩ M` of `w·Q ∩ M`, as in the proof.

This is a **derived** formulation, for four reasons. Temperedness is the published derived predicate `IsNormalizedExponentTempered`. The unitary parts are the published `leviUnitaryJacquetModule` of `ArbitraryParabolicUnitaryJacquetPart`, for explicitly quantified split components. The representatives and intersection data are those of the published represented geometric lemma `RepresentedGeometricLemmaStatement` (Renard VI.5.1). The filtration is an actual finite filtration of one representation, with the pieces in some order.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over

- an actual rational parabolic `p : P ⟶ G` with rational Levi `l : M ⟶ P`, matching geometric unipotent radical `r : N ⟶ P` and `hmul : IsIso (subgroupMultiplication l r)`;
- an actual rational parabolic `q : Q ⟶ G` with rational Levi `lQ : L ⟶ Q`, matching radical `rQ : U ⟶ Q` and `hmulQ`;
- a split component `aL : AL.toGrp ⟶ L` with `haL : IsSplitComponent aL`.

It installs on `rationalPoints M` and `rationalPoints L` the canonical topologies `leviPointTopology l hl` and `leviPointTopology lQ hlQ`, and on `rationalPoints M` the derived instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl`. For every `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` with `IsNormalizedExponentTempered hl.isConnectedReductive ρ`, it asserts that there exist

- a number `m`, an equivalence `c : Fin m ≃ DoubleCoset.Quotient P(F) Q(F)` and representatives `z : Fin m → G(F)` with `DoubleCoset.mk P(F) Q(F) (z i) = c i`;
- intersection data `D i : GeometricLemmaIntersectionDatum … (z i)` for each `i`, the published structure of `RepresentedGeometricLemmaStatement`;

such that for every family of split components `a' i : (A' i).toGrp ⟶ (D i).M'` with `ha' i : IsSplitComponent (a' i)` there are

- an `s : ObjectRepFiltration (SmoothRep.toRep.obj (leviUnitaryJacquetModule q lQ rQ hq hlQ hrQ hmulQ haL ((leviInductionFunctor p l r hp hr hl hmul).obj ρ))) m`, an actual filtration `0 = V_0 ≤ V_1 ≤ … ≤ V_m = (r_Q^G i_P^G ρ)_0` by invariant subspaces;
- a permutation `e` of `Fin m`;

with an isomorphism of representations of `L(F)` (`Representation.Equiv`) from the graded piece `V_{j+1}/V_j` (`s.gradedRepresentation j`) to `(D (e j)).unitaryPieceRep (ha' (e j)) ρ` for every `j`.

## The pieces

For an intersection datum `D` at `z` and a split component `a'` of `D.M'`, `D.unitaryPieceRep ha' ρ` is

`SmoothRep.toRep.obj (i^L_{Q'} (e^* (leviUnitaryJacquetModule D.p' D.l' D.r' … ha' ρ)))`.

That is: the unitary part `(r^M_{P'} ρ)_0` of the normalized Jacquet module of `ρ` along `P' = M ∩ zQz⁻¹`, for the split component `a'` of its Levi `M' = M ∩ zLz⁻¹`; then restriction along `D.e : L'(F) ≃ M'(F)`, the rational points of conjugation by `z`; then normalized induction `leviInductionFunctor` from `L'(F)` to `L(F)` along `Q' = L ∩ z⁻¹Pz`. It is the published `pieceFunctor` of the represented geometric lemma with `r^M_{P'}` replaced by its unitary part, exactly the change the source's proof describes. The source's `w ∈ W_{Q,P}` is the representative `z`, with `w·Q ∩ M = P'` and `L ∩ w⁻¹·P = Q'`.

## Relation to the source

- **Arbitrary parabolics.** The Proposition is stated for arbitrary `P` and `Q`. The statement quantifies over all actual rational parabolics with a rational Levi and a matching radical, without standardness. The source's proof reduces to standard `P` and `Q`; that reduction is part of the proof obligation.
- **Representatives.** As in `RepresentedGeometricLemmaStatement`, the representatives `z i` and their intersection data are conclusions, and they meet every double coset exactly once. The data include the published fields of `GeometricLemmaIntersectionDatum`, among them a maximal split torus of `G` contained in each `M'`. The specific set `W_{Q,P}` of V.4.7 is not used.
- **One representation.** The source asserts a filtration of the representation `r_Q^G(i_P^G ρ)_0` for each tempered `ρ`, and so does the statement. It does not assert naturality in `ρ`, and it does not assert that the filtration is induced by the natural filtration of VI.5.1.
- **Order.** The filtration has the pieces in some order, given by the permutation `e`, as with `IsGluedFrom` in the published geometric lemma. The source does not specify an order here.
- **Split components.** Renard's `(·)_0` uses the split component of the relevant Levi: `A_L` for `r_Q^G`, and `A_{w·L∩M}` for `r^M_{w·Q∩M}`. The statement takes an arbitrary split component `aL` of `L` as a binder, and asserts the filtration for every choice of split components of the Levis `M'`. Since any choice is allowed, the statement does not depend on a choice of split components. It does not assert that the unitary parts are independent of that choice.
- **Representations.** Both sides are valued in `Rep.{max u v} ℂ L(F)`, through `SmoothRep.toRep`, because the published object filtrations `ObjectRepFiltration` and their graded quotients live in `Rep`. Each side contains exactly one normalized induction, which raises the carrier universe from `v` to `max u v`.
- **Normalization.** All functors are the normalized ones, `leviInductionFunctor` and `leviJacquetFunctor`, as in Renard.

## Remaining obligations

The proof is a separate obligation. The source's route takes the filtration of the geometric lemma VI.5.1, whose represented form is the published `RepresentedGeometricLemmaStatement` with proof task `c060fb34-b423-4ac5-8448-788ac7627913`. It splits each `r^M_{P'} ρ` into its unitary and nonunitary parts. It then shows that the pieces built from the unitary parts have only unitary exponents for `A_L`, because they are tempered by VII.2.2 and VII.2.3, and that the pieces built from the nonunitary parts have only exponents with nonzero real part. The latter uses the root decomposition from the proof of VII.2.2 and the fact that `A_L` has no zero weight on the Lie algebra of `U`. A proof also has to pass from the filtration of `r_Q^G i_P^G ρ` to a filtration of its unitary part, for example through the decomposition of admissible representations into generalized weight spaces of the split component (VII.1.1), and to supply the represented-parabolic structural facts these steps use. None of this is asserted here.

## Provenance

This is a derived statement of the Proposition of VII.2.5 for the represented-parabolic interface. It reuses, without change, the published intersection data of Worker 1585's `RepresentedGeometricLemmaStatement` (Renard VI.5.1), the unitary parts of `ArbitraryParabolicUnitaryJacquetPart`, the normalized functors of the represented-parabolic interface and Worker 14's object filtrations `ObjectRepFiltration`.
