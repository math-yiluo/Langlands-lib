/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Profinite
public import WeilConjectures.AlgebraicGeometry.Curve.Brauer
public import WeilConjectures.AlgebraicGeometry.Sites.GaloisModule
public import WeilConjectures.AlgebraicGeometry.Sites.QuasiAlgClosedCohomology
public import WeilConjectures.CategoryTheory.Sites.Point.Torsion
public import WeilConjectures.RepresentationTheory.DiscreteModule.Torsion

/-!
# Cohomological dimension of algebraic extensions of function fields of curves

Let `k` be an algebraically closed field, `C` an integral curve over `k` and `L` an algebraic
extension of the function field `k(C)`. Then `Hᵠ(Spec L_ét, M) = 0` for every torsion abelian
étale sheaf `M` on `Spec L` and every `q ≥ 2`.

More generally this holds for every quasi-algebraically closed (`C₁`) field `L` containing an
algebraically closed field, and `L` is `C₁` by Tsen's theorem. The proof goes through Galois
cohomology: by `AlgebraicGeometry.Scheme.sheafHAddEquivGaloisH`,
`Hᵠ(Spec L_ét, M) ≃ Hᵠ(Gal(Lˢᵉᵖ/L), M_{Lˢᵉᵖ})`, and the Galois group has cohomological
dimension at most one by the degree-two criterion
`DiscreteModule.subsingleton_H_of_two_le_of_isTorsion`. Its hypothesis asks for
`H²(U, 𝔽_ℓ) = 0` for the open subgroups `U = Gal(Lˢᵉᵖ/E)`, `E/L` finite; by the comparison for
the field `E` this is `H²(Spec E_ét, ℤ/ℓ) = 0`, which holds since `E` is again `C₁`
(`AlgebraicGeometry.Scheme.subsingleton_sheafH_two_constantZMod_of_isAlgClosed_subfield`).

## Main statements

- `AlgebraicGeometry.Scheme.subsingleton_sheafH_of_isQuasiAlgClosed`: the vanishing for a `C₁`
  field containing an algebraically closed field.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_isAlgebraic_functionField`: the vanishing
  for algebraic extensions of function fields of curves.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

/-- `H²(Gal(Ω/E), 𝔽_ℓ) = 0` for a `C₁` field `E` containing an algebraically closed field and a
separable closure `Ω` of `E`: by the comparison of Galois and étale cohomology this is
`H²(Spec E_ét, ℤ/ℓ) = 0`. -/
lemma subsingleton_H_two_trivialZMod_of_isQuasiAlgClosed (k E Ω : Type u) [Field k]
    [IsAlgClosed k] [Field E] [Algebra k E] [IsQuasiAlgClosed E] [Field Ω] [Algebra E Ω]
    [IsSepClosed Ω] [Algebra.IsSeparable E Ω] (ℓ : ℕ) [Fact ℓ.Prime] :
    Subsingleton (DiscreteModule.H Gal(Ω/E) (DiscreteModule.trivialZMod.{u + 1} Gal(Ω/E) ℓ) 2) :=
  have := subsingleton_sheafH_two_constantZMod_of_isAlgClosed_subfield k E ℓ
  (sheafHConstantSheafAddEquivGaloisH E Ω _ 2).symm.injective.subsingleton

/-- **Cohomological dimension of a `C₁` field.** Let `L` be a quasi-algebraically closed field
containing an algebraically closed field `k`. Then `Hᵠ(Spec L_ét, M) = 0` for every torsion
abelian étale sheaf `M` on `Spec L` and every `q ≥ 2`. -/
theorem subsingleton_sheafH_of_isQuasiAlgClosed (k L : Type u) [Field k] [IsAlgClosed k]
    [Field L] [Algebra k L] [IsQuasiAlgClosed L]
    (M : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1}) (hM : M.IsTorsion)
    {q : ℕ} (hq : 2 ≤ q) : Subsingleton (Sheaf.H M q) := by
  let Ω := SeparableClosure L
  have h2 : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (U : Subgroup Gal(Ω/L)), IsOpen (U : Set Gal(Ω/L)) →
      Subsingleton (DiscreteModule.H U (DiscreteModule.trivialZMod.{u + 1} U ℓ) 2) := by
    intro ℓ _ U hU
    have hE := InfiniteGalois.fixingSubgroup_fixedField_of_isOpen U hU
    have : FiniteDimensional L (IntermediateField.fixedField U) :=
      InfiniteGalois.finiteDimensional_fixedField_of_isOpen U hU
    set E := IntermediateField.fixedField U
    rw [← hE]
    have : IsQuasiAlgClosed E := IsQuasiAlgClosed.of_isAlgebraic L E
    let : Algebra k E := ((algebraMap L E).comp (algebraMap k L)).toAlgebra
    have : Algebra.IsSeparable E Ω := Algebra.isSeparable_tower_top_of_isSeparable L E Ω
    have := subsingleton_H_two_trivialZMod_of_isQuasiAlgClosed k E Ω ℓ
    exact DiscreteModule.subsingleton_H_trivialZMod_of_continuousMulEquiv
      E.fixingSubgroupContinuousMulEquiv ℓ 2
  have htors : ∀ x : ((etaleSheafEquivDiscreteModule L Ω).functor.obj M).obj.V,
      IsOfFinAddOrder x :=
    ((pointSmallEtale (specAlgebraMap L Ω)).ulift.{u + 1}).isAddTorsion_sheafFiber hM
  have := DiscreteModule.subsingleton_H_of_two_le_of_isTorsion h2 _ htors hq
  exact (sheafHAddEquivGaloisH L Ω M q).injective.subsingleton

end Scheme

namespace IsCurve

/-- **Cohomology of an algebraic extension of a curve function field.** Let `k` be an
algebraically closed field, `C` an integral curve over `k` and `L` an algebraic extension of
its function field `k(C)`. Then `Hᵠ(Spec L_ét, M) = 0` for every torsion abelian étale sheaf
`M` on `Spec L` and every `q ≥ 2`: the field `L` is `C₁` by Tsen's theorem
(`AlgebraicGeometry.IsCurve.isQuasiAlgClosed_functionField`), and
`AlgebraicGeometry.Scheme.subsingleton_sheafH_of_isQuasiAlgClosed` applies.
(blueprint: `theorem-cohomology-curves`) -/
theorem subsingleton_sheafH_of_isAlgebraic_functionField {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsIntegral C] (L : Type u) [Field L]
    [Algebra C.functionField L] [Algebra.IsAlgebraic C.functionField L]
    (M : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1}) (hM : M.IsTorsion)
    {q : ℕ} (hq : 2 ≤ q) : Subsingleton (Sheaf.H M q) := by
  have := isQuasiAlgClosed_functionField f
  have : IsQuasiAlgClosed L := IsQuasiAlgClosed.of_isAlgebraic C.functionField L
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  have : Nonempty (⊤ : C.Opens) := ⟨⟨x, trivial⟩⟩
  let : Algebra k L := ((algebraMap C.functionField L).comp ((C.germToFunctionField ⊤).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom))).toAlgebra
  exact Scheme.subsingleton_sheafH_of_isQuasiAlgClosed k L M hM hq

end IsCurve

end AlgebraicGeometry
