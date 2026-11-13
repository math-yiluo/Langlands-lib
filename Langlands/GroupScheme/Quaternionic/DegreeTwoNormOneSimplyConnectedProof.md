# Proof: actual degree-two reduced-norm-one groups are simply connected

Author: Worker 170.

The closing theorem
`Langlands.GroupScheme.CentralSimpleUnits.degreeTwoNormOneSimplyConnected.{u}`
has exactly the type of the published proposition
`Langlands.GroupScheme.CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u}`,
imported from `Langlands.GroupScheme.Quaternionic.DegreeTwoNormOneSimplyConnectedStatement`.

For every field `K : Type u` and every finite-dimensional central simple `K`-algebra
`A : Type u` (`Ring A`, `Algebra K A`, `FiniteDimensional K A`, `Algebra.IsCentral K A`,
`IsSimpleRing A`) with `Module.finrank K A = 4`, it proves
`IsSimplyConnected (normOne K A)` for the actual reduced-norm-one group scheme. The
universe `u` is arbitrary and the characteristic of `K` is unrestricted; no division-ring,
splitting, local-field, perfectness or geometric-model premise is added. Both
semisimplicity and the incoming-central-isogeny criterion are proved, as parts of
`IsSimplyConnected`.

## Implemented proof

1. **Reduced degree.** `reducedDegree_eq_two_of_finrank_eq_four` proves
   `Langlands.CentralSimple.reducedDegree K A = 2` from `Module.finrank K A = 4`:
   `reducedDegree K A` is by definition `Nat.sqrt (Module.finrank K A)`, and
   `Nat.sqrt (2 * 2) = 2` is Mathlib's `Nat.sqrt_eq 2`. This lemma needs no
   central-simplicity hypotheses.

2. **`SL_2` is simply connected.** For `L = AlgebraicClosure K`, the helper theorem
   `Langlands.GroupScheme.SpecialLinear.BinarySymplectic.isSimplyConnected L`
   (module `Langlands.GroupScheme.SpecialLinearBinarySymplectic`, submitted with this
   proof) gives `IsSimplyConnected (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of L))`.
   It transports the published simple connectedness of the split symplectic group
   `SymplecticMatrix.isSimplyConnected (Fin 1) L` along the isomorphism `Sp_2 ≅ SL_2`
   built from the identity `g J gᵀ = det(g) J` for `2 × 2` matrices. Inside the proof the
   statement is generalized to `∀ n, n = 2 → IsSimplyConnected
   (SpecialLinear.groupScheme (Fin n) (CommRingCat.of L))` so that it can be applied at
   `n = reducedDegree K A`, which equals `2` only propositionally.

3. **Splitting over the algebraic closure.** The published chart
   `Langlands.CentralSimple.algebraicClosureChart K A :
   L ⊗[K] A ≃ₐ[L] Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L` and the
   published isomorphism
   `Langlands.GroupScheme.CentralSimpleUnits.Splitting.splittingIso K A e`
   (module `Langlands.GroupScheme.CentralSimpleNormOneSplitting`) identify the base change
   of `normOne K A` along `Spec.map (CommRingCat.ofHom (algebraMap K L))` with
   `SpecialLinear.groupScheme (Fin (reducedDegree K A)) (CommRingCat.of L)`.
   `IsSimplyConnected.of_iso` along this isomorphism, with steps 1 and 2, makes the base
   change simply connected.

4. **Descent along the algebraic extension.** `AlgebraicClosure K` is algebraic over `K`,
   so the published
   `Langlands.GroupScheme.IsSimplyConnected.of_algebraicExtension`
   (module `Langlands.GroupScheme.SimplyConnected.AlgebraicExtensionReflection`), which
   reflects simple connectedness along every algebraic field extension, gives
   `IsSimplyConnected (normOne K A)`.

## Library declarations used

- `Langlands.CentralSimple.reducedDegree`, `Langlands.CentralSimple.algebraicClosureChart`
  (`Langlands.Algebra.CentralSimpleScalarExtension`).
- `Langlands.GroupScheme.CentralSimpleUnits.Splitting.splittingIso`
  (`Langlands.GroupScheme.CentralSimpleNormOneSplitting`).
- `Langlands.GroupScheme.IsSimplyConnected.of_iso`
  (`Langlands.GroupScheme.SimplyConnected.Basic`).
- `Langlands.GroupScheme.IsSimplyConnected.of_algebraicExtension`
  (`Langlands.GroupScheme.SimplyConnected.AlgebraicExtensionReflection`).
- `Langlands.GroupScheme.SymplecticMatrix.isSimplyConnected`, through the helper module
  `Langlands.GroupScheme.SpecialLinearBinarySymplectic` described in its paired Markdown.
- Mathlib: `Nat.sqrt_eq`, `AlgebraicClosure`.
