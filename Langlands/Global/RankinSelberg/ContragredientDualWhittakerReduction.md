# Reduction of the contragredient Whittaker identity

Module `Langlands.Global.RankinSelberg.ContragredientDualWhittakerReduction`. Author:
Worker 381, with Worker 126 (sphericity of the dual cusp form).

## 1. Content

The target is the published premise
`Langlands.Global.RankinSelbergGlobal.ContragredientDualWhittakerStatement.{u}` of
[EqualDualEulerFactorizationReduction](EqualDualEulerFactorizationReduction.md): for a number
field `F`, a unitary character `ψ` of `𝔸_F` trivial on `F`, actual cuspidal realizations `T`,
`Td` of `GL_(r+1)` with `Td` realizing the contragredient of `T`, a finite set `S` of finite
places and a vector `x` of `T` spherical outside `S`, there is a vector `xd` of `Td`,
spherical outside `S`, whose `ψ⁻¹`-Whittaker function is `W̃_x(g) = W_x(w_n ᵗg⁻¹)`.

This module, in the namespace `Langlands.Global.RankinSelbergGlobal`, contains

* `cuspidalOperatorRealization_ext`: two actual cuspidal operator realizations with the same
  underlying operator realization are equal (the other two fields are propositions);
* the statement

  ```lean
  def ContragredientDualWhittakerReductionStatement : Prop :=
    Automorphic.CuspidalOperatorMultiplicityOneStatement.{u} →
      CuspidalTransposeInverseContragredientStatement.{u} →
        ContragredientDualWhittakerStatement.{u}
  ```

* the theorem `contragredientDualWhittakerReduction`, which proves it.

The two premises are open statements:

* (A) [`Automorphic.CuspidalOperatorMultiplicityOneStatement`](../../Automorphic/CuspidalOperatorMultiplicityOneStatement.md):
  equivalent actual cuspidal operator realizations have the same underlying realization
  (multiplicity one, Cogdell 2004 p.202);
* (B) [`CuspidalTransposeInverseContragredientStatement`](CuspidalTransposeInverseContragredientStatement.md):
  every `T` has an actual cuspidal contragredient `T'` containing the dual cusp form
  `φ̃(g) = φ(w_n ᵗg⁻¹)` of every vector of `T` (Gelfand–Kazhdan, Cogdell 2004 pp.201, 203,
  206).

The theorem is a reduction. It is an intermediate result of Task 7121 in the sense of the
"Intermediate results" section of that task's revision 2; the task's required result, an
unconditional proof of the target, stays open.

## 2. Provenance

Internal. In Cogdell 2004 (`cogdell-2004-analytic-theory-gln`) the vector `xd` is the cusp
form `φ̃` itself: `φ̃ ∈ V_π̃` (p.203, from Gelfand–Kazhdan's `π̃ ≅ π^ι`, p.201) and its
`ψ⁻¹`-Whittaker function is `W̃_φ` (pp.201 and 207). In the Library the contragredient `Td`
is an arbitrary actual realization, so the argument needs in addition that the space of
`π̃` among cusp forms is unique, which is multiplicity one (p.202). The decomposition into
(A), (B) and the three proved ingredients below is ours.

## 3. Proof

Let `T`, `Td`, `ψ`, `S`, `x` be as in the target, with `hTd : Td` realizes the contragredient
of `T`.

1. By (B) there is a cuspidal `T'` realizing the contragredient of `T` such that every dual
   cusp form `φ̃_y`, `y ∈ T`, is the cusp form of a vector of `T'`.
2. `T'` and `Td` both realize the contragredient of `T`, so they are equivalent
   (`Automorphic.OperatorRealization.IsContragredientOf.nonempty_equivalence`, in
   [ContragredientUniqueness](../../Automorphic/ContragredientUniqueness.md)).
3. By (A), `T'.realization = Td.realization`, hence `T' = Td`
   (`cuspidalOperatorRealization_ext`); substitute.
4. Choose `xd` in `Td` with cusp form `φ̃_x` (step 1).
5. `xd` is spherical outside `S`: `isSphericalOutside_of_cuspFunction_eq_dual` (Worker 126,
   module `Langlands.Global.RankinSelberg.ContragredientDualSpherical`), since `x` is.
6. The `ψ⁻¹`-Whittaker function of `xd` is `W̃_x`:
   `cuspWhittaker_inv_eq_dualFunction` (in
   [ContragredientDualWhittakerIdentity](ContragredientDualWhittakerIdentity.md)) for the
   standard character `ψ.complex` (`isStandardAdditiveCharacter_of_unitary`).

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
