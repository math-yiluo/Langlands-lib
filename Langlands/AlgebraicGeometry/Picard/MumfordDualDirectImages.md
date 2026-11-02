# Higher direct images of the Mumford coefficient along the parameter projection

Author: Worker 1164.

Module `Langlands.AlgebraicGeometry.Picard.MumfordDualDirectImages`, steps 1–4 of the
proof of `Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement` (task
`6b1ab3e8-b3b0-4567-9251-7566e7a6dba3`). Steps 5 and 7 are in
`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerReduction`, Step 6 is in
`Langlands.AlgebraicGeometry.Picard.FiniteFlatPointFibreSections`, and the assembly is in
`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerFromPrerequisites`.

## Setting

`A` is an abelian scheme over `S` with chosen dual `D = dualScheme A hA` and Poincaré bundle
`P = poincareLineBundle A hA` on the conventional total space `A ×_S D`
(Lean: `pullback A.X.hom D.hom`, which is the underlying scheme of
`(baseChange D.hom).obj A`). The parameter-first self-product is `pullback A.X.hom A.X.hom` with
parameter projection `p = pullback.fst` and `A`-factor `pullback.snd`; `m = mumfordAddition A`.
`N` is the normalized bundle `LineBundle.normalize … L B evaluationB`, `M` is a line bundle with
`evaluation : N ⊗ M ≅ 𝒪`, and `f` is the Mumford scheme map
`mumfordSchemeMapOfLineBundle … square hA` of `N`.
The Mumford coefficient is `Q = m^* N ⊗ snd^* M`.

## Declarations

- `Langlands.Scheme.Modules.isZero_tensorObj_of_isZero_right`: `M ⊗ Z` is zero when `Z` is
  zero. Proof: on every open `U`, the presheaf tensor product is the module tensor product
  `M(U) ⊗ Z(U)`, which is a subsingleton since `Z(U)` is (`TensorProduct.uniqueRight`); so the
  presheaf tensor product is zero, and sheafification (a left adjoint) preserves zero objects.
- `mumfordDualPoincareMap f : A ×_S A ⟶ A ×_S D`, the map `(a₁, a₂) ↦ (a₂, f a₁)`
  (`pullback.lift snd (fst ≫ f.left)`).
- `mumfordDualPoincareMap_symmetry`: followed by the inverse of `relativeSpaceSymmetry`, it is
  the relative-space map `(relativeSpace A.X.hom).map f`. Proof: both components agree by
  `pullbackSymmetry_inv_comp_fst/snd` and `pullback.lift_fst/snd`.
- `mumfordDualPoincareMap_isPullback`: the square with `mumfordDualPoincareMap f`, `p`, the
  projection `A ×_S D ⟶ D` and `f.left` is a pullback. Proof: pasting with the defining pullback
  square of `A ×_S D` (`IsPullback.of_right`), whose composite is the flipped defining square of
  `A ×_S A`.
- `mumfordDualPoincarePullback f = Λ`, the pullback of `P` along `mumfordDualPoincareMap f`, and
  `mumfordDualPoincarePullbackIso`: `Λ` is the line bundle underlying the relative pullback of
  the Poincaré family along `f`. Proof: `P` is by definition the pullback of the family's bundle
  along the inverse symmetry, so `LineBundle.pullbackCompEqIso` with the symmetry lemma applies.
- `mumfordDual_coefficient_iso` (step 1): `m^* N ⊗ snd^* M ≅ fst^* N ⊗ Λ`. Proof in the
  commutative group `LineBundle.IsoClasses` of line-bundle isomorphism classes on `A ×_S A`:
  by `mumfordSchemeMapOfLineBundlePullbackIso`, the class of `Λ` is that of the Mumford family
  `m^* N ⊗ fst^* M ⊗ snd^* M` (`mumfordFamilyOfLineBundle_forget`); `evaluation` gives
  `[N][M] = 1`, hence `[fst^* N][fst^* M] = 1` after pulling back along `fst`; the identity then
  follows by commutativity and associativity.
- `mumfordDual_higherDirectImage` (steps 2–4). Over an algebraically closed field `K`, with `A`
  of relative dimension `g` and `f.left` flat, assuming the three published statements
  `AlgClosedFieldPoincareDirectImageStatement`, `FlatHigherDirectImageBaseChangeStatement` and
  `LineBundleHigherProjectionFormulaStatement` as hypotheses:
  `Rⁿ p_* Q = 0` for `n ≠ g`, and `R^g p_* Q ≅ N ⊗ f^* (e_D)_* 𝒪_{Spec K}`. Proof:
  `Rⁿ p_* Q ≅ Rⁿ p_*(fst^* N ⊗ Λ) ≅ N ⊗ Rⁿ p_* Λ` by step 1 and the projection formula;
  `Rⁿ p_* Λ ≅ f^* Rⁿ q_* P` by flat base change along the pullback square above (`q` is proper,
  hence quasi-compact and separated; `P` is quasi-coherent as a line bundle); then the Poincaré
  direct images give vanishing (via `isZero_tensorObj_of_isZero_right`) and the degree-`g`
  isomorphism.

## Status

Compiles against Library `2c43e36f` with no errors or warnings. The three prerequisite
statements enter only as hypotheses of `mumfordDual_higherDirectImage`; their proofs (tasks
`32297f48-…` Poincaré direct images, `5b778a75-…` flat base change, `d0088789-…` projection
formula) will replace them once published.
