# Finitely many rational translations preserve an ample line bundle

This module proves the Library statement
`Langlands.AbelianScheme.AlgClosedFieldAmpleTranslationStabilizerFiniteStatement`: for an
abelian scheme `A` over `Spec K`, `K` an algebraically closed field, and an ample line bundle
`L` on `A`, only finitely many rational points `x : Spec K ⟶ A` over `Spec K` satisfy
`t_x^* L ≅ L`, where `t_x = GroupScheme.translation A.toGrp x`.

The final theorem `algClosedFieldAmpleTranslationStabilizerFinite` has exactly the type
`AlgClosedFieldAmpleTranslationStabilizerFiniteStatement.{u}` and no hypotheses. It applies
the intermediate theorem `algClosedFieldAmpleTranslationStabilizerFinite_of_equalizer` to the
Library proof `Langlands.AbelianScheme.rigidifiedClassesEqualizerClosed` of
`RigidifiedClassesEqualizerClosedStatement.{u}` (module
`Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedProof`).

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Lemma (2.19)
(printed p.23, PDF p.27): if `L` is ample then `K(L)` is finite; the target statement's
Markdown derives the rational-point form. The source proof restricts `L` to
`Y = K(L)^0_red`, shows that `L|_Y ⊗ (-1)^*L|_Y` is trivial and ample on `Y`, and concludes
`dim Y = 0`. The implemented proof follows the same idea, but replaces `Y` by the closed
locus `Z` below: it does not construct the group scheme `K(L)` (Proposition (2.4)) and uses
neither the theorem of the square nor the seesaw principle beyond the closed agreement locus.
Algebraic closure of `K` is not used: every step below holds over an arbitrary field.

## Route

Write `S = Spec K`, `m` for the addition of `A`, `e` for its unit section and
`ι = GrpObj.inv (X := A.X)` for its inversion.

1. **Closed locus (part A).** Choose a line bundle `M` with `M ⊗ L ≅ O_A`
   (`LineBundle.exists_tensorObj_iso_structureSheaf`) and rigidify it along `e`, using that
   every line bundle on `Spec K` is trivial (`fieldLineBundleTriviality`). The Mumford bundle
   `P = mumfordBundle A preservation M L evaluation` is the rigidified family on `A ×_S A`
   (parameter first) with carrier `(m^* M ⊗ p₁^* L) ⊗ p₂^* L`. The proposition
   `RigidifiedClassesEqualizerClosedStatement`, applied with `T = A` to the class of `P` and
   the trivial class, gives a closed immersion `i : Z ⟶ A` such that a point `h : T' ⟶ A`
   factors through `i` exactly when both classes agree after pullback along `h`.
   - *Stabilizing points factor through `i`.* If `t_x^* L ≅ L`, then
     `t_x^* M ⊗ L ≅ t_x^* M ⊗ t_x^* L ≅ t_x^*(M ⊗ L) ≅ O_A`, and the published
     `fieldMumfordPointComparison` turns this into an isomorphism between the pullback of `P`
     along `x` and the trivial family, so the classes agree at `x`.
   - *`i^* L ⊗ (i ≫ ι)^* L` is trivial.* The tautological point `i` lies in the locus, so the
     pullback of `P` along `i` is isomorphic to the trivial family on `Z ×_S A`. Pulling this
     isomorphism back along the section `z ↦ (z, -i z)` of `Z ×_S A → Z` gives
     `O_Z ≅ (i, -i)^*((m^* M ⊗ p₁^* L) ⊗ p₂^* L)`. Since `m ∘ (i, -i)` is the constant unit
     point, the factor `(i, -i)^* m^* M` is the pullback of `e^* M`, which the rigidification
     of `M` trivializes; the remaining factors are `i^* L ⊗ (-i)^* L`.
2. **Finiteness of `Z` (part B).** Both `i^* L` and `(i ≫ ι)^* L` are ample, since `i` and
   `i ≫ ι` are closed immersions (`ι` is an isomorphism) and ampleness is preserved by
   pullback along closed immersions (`closedImmersionPullbackAmple`). Their tensor product is
   therefore ample (`ampleTensor`), so the trivial line bundle on `Z` is ample. The morphism
   `i ≫ A.X.hom : Z ⟶ Spec K` is proper (a closed immersion followed by the proper structure
   morphism), so `properAmpleTrivialFinite` shows that it is finite.
3. **Counting.** The published
   `Langlands.AlgebraicGeometry.FiniteEtale.finite_sections_of_isFinite` in
   `GeometricFiberFiniteProof` shows that a finite `K`-scheme has only finitely many
   `K`-rational sections. It uses the injective map from sections to algebra maps
   from the finite-dimensional coordinate algebra to `K`. Each
   stabilizing point `x` factors as `g ≫ i` with `g` a section of `Z ⟶ Spec K`; since `i` is
   fixed, the map `x ↦ g` is injective, so the stabilizer is finite.

The canonical comparison maps `f^*(E ⊗ F) → f^*E ⊗ f^*F` are inverted using the published
`pullbackTensorComparisonIsIso`.

## Declarations

Namespace `Langlands.AbelianScheme.TranslationStabilizer` (helpers for part A):

- `inversion A`: the inversion `(𝟙 A.X)⁻¹` of `A` as a morphism over `S`;
  `inversion_inversion` proves that it is an involution, hence its underlying scheme
  morphism is an isomorphism.
- `testObject A j`, `tautological A j`: a scheme morphism `j : Z ⟶ A` viewed as a test object
  over `S` and as a point of `A` with values in it; `tautological_inversion` identifies its
  composite with `inversion A` as its group inverse.
- `antidiagonal A j`: the section `z ↦ (z, -j z)` of `Z ×_S A → Z`. `antidiagonalPoint A j`
  is its composite with `FieldMumfordPoint.pointMap`, the point `(j, -j)` of `A ×_S A`;
  `antidiagonalPoint_fst` and `antidiagonalPoint_snd` compute its projections, and
  `antidiagonalPoint_addition` proves `m ∘ (j, -j) = e ∘ (structure map of Z)` from
  `mul_inv_cancel` in the group of points.
- `antidiagonalMumfordIso`: the pullback of `(m^* M ⊗ p₁^* L) ⊗ p₂^* L` along `(j, -j)` is
  isomorphic to `j^* L ⊗ (-j)^* L`, using the addition identity, the inverse of the
  rigidification of `M`, the unit isomorphism and the left unitor.
- `antidiagonalTrivialization`: from an isomorphism between the pullbacks of the Mumford family
  and of the trivial family along `tautological A j`, it builds `j^* L ⊗ (-j)^* L ≅ O_Z` by
  pulling back along `antidiagonal A j` (with `RigidifiedLineBundle.pullbackTrivialIso`).
- `baseChangeSection_left_fst`: the rational point of the trivial base change attached to `x`
  lies over `x`.
- `pointPremise`: for `e : t_x^* L ≅ L`, an isomorphism between `t_x^* M ⊗ L` on the trivial base
  change and the trivial family, built from `GroupScheme.fibreTranslationIso`,
  `pullbackTensorEvaluation` and the supplied evaluation `M ⊗ L ≅ O_A`.
- `mumfordClass_point`: for such `x`, the pulled-back classes of the Mumford family and the
  trivial family agree (`fieldMumfordPointComparison` with `b = 𝟙`).

Namespace `Langlands.AbelianScheme`:

- `stabilizer_equalizer_locus`: part A. Given the closed-locus proposition, a closed
  immersion `i : Z ⟶ A`, an isomorphism `tensorObj (i^* L) ((i ≫ ι)^* L) ≅ O_Z`, and the
  factorization of every stabilizing rational point through `i`.
- `stabilizer_finite_of_locus`: part B and step 3. Given a closed immersion `i : Z ⟶ A`, an
  isomorphism `tensorObj (i^* L) ((i ≫ ι)^* L) ≅ O_Z`, and the factorization of every
  stabilizing point through `i`, the stabilizer subtype is finite.
- `algClosedFieldAmpleTranslationStabilizerFinite_of_equalizer`: the target statement from
  `RigidifiedClassesEqualizerClosedStatement.{u}`, combining `stabilizer_equalizer_locus` and
  `stabilizer_finite_of_locus`.
- `algClosedFieldAmpleTranslationStabilizerFinite`: the target statement, obtained by supplying
  `rigidifiedClassesEqualizerClosed` to
  `algClosedFieldAmpleTranslationStabilizerFinite_of_equalizer`.

Part A was written by Worker 839 and part B by Worker 920.
