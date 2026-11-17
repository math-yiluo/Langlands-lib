import Langlands.Automorphic.LocalComponentFinitePlace
import Langlands.Automorphic.OperatorSubquotientPlaceComponentComplex

/-!
# Local components of automorphic representations at every place

Proof of `LocalComponentExistenceStatement` (Getz–Hahn, Theorem 6.3.7; Flath, Theorem 3): an
irreducible jointly admissible operator subquotient `Q` of `GL_(r+1)` over a number field is
isotypic, at every place, for an irreducible admissible local representation.

* The finite places are `localComponentExistence_finitePlace`
  (`Langlands.Automorphic.LocalComponentFinitePlace`).
* At a real or complex place `v`, `exists_realPlaceComponent` and
  `exists_complexPlaceComponent` give an irreducible admissible place-stable subspace `W` of
  `Q`. The restricted actions on `W` form the required `(𝔤, K)`-module: the structure axioms
  pass to `W` by `PlaceComponent.isRealGKModule_restrict` and
  `PlaceComponent.isComplexGKModule_restrict`, irreducibility and admissibility by
  `PlaceComponent.isIrreducibleGKModule_restrict` and
  `PlaceComponent.isAdmissibleGKModule_restrict`, and `Q` is `W`-isotypic at `v` by
  `isRealPlaceIsotypic_restrict` and `isComplexPlaceIsotypic_restrict`.
-/

noncomputable section

universe u

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open PlaceComponent

variable {F : Type u} [Field F] [NumberField F]

namespace IrreducibleOperatorSubquotient

/-- **Local components at a real place.** An irreducible jointly admissible operator
subquotient of `GL_(r+1)` is, at every real place `v`, isotypic for an irreducible admissible
`(𝔤𝔩_(r+1)(ℝ), O(r+1))`-module, realized on a subspace of `Q`. -/
theorem exists_realPlace_localComponent {r : ℕ} (Q : IrreducibleOperatorSubquotient F r)
    (hQ : Q.subquotient.IsJointlyAdmissible)
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) :
    ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      Archimedean.IsRealGKModule (r + 1) ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
        Archimedean.IsAdmissibleGKModule ρ ∧ Q.subquotient.IsRealPlaceIsotypic v ρ π := by
  have hW := Q.subquotient.exists_realPlaceComponent Q.irreducible hQ v
  obtain ⟨W, hWirr, hWadm⟩ := hW
  exact ⟨ModuleCat.of ℂ W, restrictCompact hWirr.2.1, restrictLie hWirr.2.1,
    isRealGKModule_restrict hWirr.2.1 (Q.subquotient.isRealGKModule_realPlace v),
    isIrreducibleGKModule_restrict hWirr, isAdmissibleGKModule_restrict hWirr.2.1 hWadm,
    Q.subquotient.isRealPlaceIsotypic_restrict Q.irreducible v hWirr⟩

/-- **Local components at a complex place.** An irreducible jointly admissible operator
subquotient of `GL_(r+1)` is, at every complex place `v`, isotypic for an irreducible
admissible `(𝔤𝔩_(r+1)(ℂ), U(r+1))`-module, realized on a subspace of `Q`. -/
theorem exists_complexPlace_localComponent {r : ℕ} (Q : IrreducibleOperatorSubquotient F r)
    (hQ : Q.subquotient.IsJointlyAdmissible)
    (v : {v : NumberField.InfinitePlace F // v.IsComplex}) :
    ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      Archimedean.IsComplexGKModule (r + 1) ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
        Archimedean.IsAdmissibleGKModule ρ ∧ Q.subquotient.IsComplexPlaceIsotypic v ρ π := by
  have hW := Q.subquotient.exists_complexPlaceComponent Q.irreducible hQ v
  obtain ⟨W, hWirr, hWadm⟩ := hW
  exact ⟨ModuleCat.of ℂ W, restrictCompact hWirr.2.1, restrictLie hWirr.2.1,
    isComplexGKModule_restrict hWirr.2.1 (Q.subquotient.isComplexGKModule_complexPlace v),
    isIrreducibleGKModule_restrict hWirr, isAdmissibleGKModule_restrict hWirr.2.1 hWadm,
    Q.subquotient.isComplexPlaceIsotypic_restrict Q.irreducible v hWirr⟩

end IrreducibleOperatorSubquotient

/-- **Local components of irreducible jointly admissible operator subquotients**
(Getz–Hahn, Theorem 6.3.7; Flath, Theorem 3): at every finite, real and complex place, an
irreducible jointly admissible operator subquotient of `GL_(r+1)` is isotypic for an
irreducible admissible local representation. -/
theorem localComponentExistence : LocalComponentExistenceStatement.{u} :=
  localComponentExistenceStatement_of_infinitePlaces fun _ _ _ _ Q hQ =>
    ⟨fun v => Q.exists_realPlace_localComponent hQ v,
      fun v => Q.exists_complexPlace_localComponent hQ v⟩

end Langlands.Automorphic
