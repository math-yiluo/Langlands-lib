import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerStatement
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeGeometryStatement
import Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportLerayProof
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Steps 5 and 7 of the dual-side Euler computation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Step 5. If all higher direct images of `Q` along `p` vanish outside degree `g`, and the
degree-`g` one has finite closed support, then the Euler characteristic of `Q` over the field is
`(-1)^g` times the dimension of the global sections of `R^g p_* Q`. -/
theorem eulerCharacteristic_comp_eq_of_concentrated
    {K : Type u} [Field K] {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ Spec (CommRingCat.of K))
    (Q : X.Modules) (g : ℕ)
    (hzero : ∀ n : ℕ, n ≠ g → IsZero ((higherDirectImage p n).obj Q))
    (hsupp : HasFiniteClosedSupport ((higherDirectImage p g).obj Q))
    (hQ : HasFiniteCohomology (p ≫ s) Q) :
    eulerCharacteristic (p ≫ s) Q hQ =
      (-1) ^ g * (Module.finrank K
        ((relativeGlobalSections s).obj ((higherDirectImage p g).obj Q)) : ℤ) := by
  have hall : ∀ q : ℕ, HasFiniteClosedSupport ((higherDirectImage p q).obj Q) := by
    intro q
    by_cases hq : q = g
    · subst hq
      exact hsupp
    · exact HasFiniteClosedSupport.of_isZero (hzero q hq)
  have e := finiteClosedSupportLeray X Y (CommRingCat.of K) p s Q hall
  unfold eulerCharacteristic
  rw [finsum_eq_single _ g]
  · obtain ⟨e⟩ := e g
    rw [LinearEquiv.finrank_eq e.toLinearEquiv]
  · intro n hn
    obtain ⟨e⟩ := e n
    have : (relativeGlobalSections s).Additive :=
      (inferInstance : ∀ {R : CommRingCat.{u}} (f : Y ⟶ Spec R),
        (relativeGlobalSections f).Additive) s
    have hz : IsZero ((relativeGlobalSections s).obj ((higherDirectImage p n).obj Q)) :=
      Functor.map_isZero _ (hzero n hn)
    have : Subsingleton ((relativeGlobalSections s).obj ((higherDirectImage p n).obj Q)) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    rw [LinearEquiv.finrank_eq e.toLinearEquiv, Module.finrank_zero_of_subsingleton]
    simp

end Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AbelianScheme

/-- Step 7. Over a field, given the geometry of the chosen dual (connectedness), the native degree
of a finite flat map `A ⟶ D` is the same at every point of `D`. -/
theorem finrank_eq_of_fieldDualSchemeGeometry
    (hgeom : FieldDualSchemeGeometryStatement.{u})
    (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
    (f : A.X ⟶ dualScheme A hA) [IsFinite f.left] [Flat f.left]
    (y y' : (dualScheme A hA).left) :
    f.left.finrank y = f.left.finrank y' := by
  obtain ⟨hsm, -, hgc⟩ := hgeom K A hA
  have : ConnectedSpace (dualScheme A hA).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := (dualScheme A hA).hom)
  have : IsLocallyNoetherian (dualScheme A hA).left :=
    LocallyOfFiniteType.isLocallyNoetherian (dualScheme A hA).hom
  have : LocallyOfFinitePresentation f.left := inferInstance
  exact f.left.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace y y'

end Langlands.AbelianScheme
