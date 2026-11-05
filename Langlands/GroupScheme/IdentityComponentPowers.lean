import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.SchemeActionOrbit
import Langlands.AlgebraicGeometry.LocallyNoetherianConnectedComponentOpenProof
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.GroupTheory.OrderOfElement

/-! # Positive powers as points of the actual identity component -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))

/-- The permutation of scheme connected components induced by left translation
by a rational section. -/
def translationComponents (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    Equiv.Perm (_root_.ConnectedComponents H.X.left) := by
  let e := SchemeAction.translationIso (ModObj.regular H.X) x
  exact
    { toFun := e.hom.left.continuous.connectedComponentsMap
      invFun := e.inv.left.continuous.connectedComponentsMap
      left_inv := by
        intro c
        obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
        simp only [Continuous.connectedComponentsMap_mk]
        change _root_.ConnectedComponents.mk ((e.hom ≫ e.inv).left p) = _root_.ConnectedComponents.mk p
        rw [e.hom_inv_id]
        rfl
      right_inv := by
        intro c
        obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
        simp only [Continuous.connectedComponentsMap_mk]
        change _root_.ConnectedComponents.mk ((e.inv ≫ e.hom).left p) = _root_.ConnectedComponents.mk p
        rw [e.inv_hom_id]
        rfl }

@[simp]
theorem translationComponents_mk
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) (p : H.X.left) :
    translationComponents H x (_root_.ConnectedComponents.mk p) =
      _root_.ConnectedComponents.mk
        ((SchemeAction.translation (ModObj.regular H.X) x).left p) :=
  rfl

/-- On rational sections the component permutation computes ordinary multiplication. -/
theorem translationComponents_point
    (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    translationComponents H x (_root_.ConnectedComponents.mk (y.left (basePoint k))) =
      _root_.ConnectedComponents.mk ((x * y).left (basePoint k)) := by
  rw [translationComponents_mk]
  change _root_.ConnectedComponents.mk
      ((y ≫ SchemeAction.translation (ModObj.regular H.X) x).left (basePoint k)) = _
  have h : y ≫ SchemeAction.translation (ModObj.regular H.X) x = x * y := by
    rw [SchemeAction.comp_translation]
    have hu : toUnit (𝟙_ (Over (Spec (CommRingCat.of k)))) = 𝟙 _ :=
      toUnit_unique _ _
    rw [hu, Category.id_comp]
    rfl
  rw [h]

/-- Iterating translation sends the identity component class to the class of a power. -/
theorem translationComponents_pow_point
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) (n : ℕ) :
    (translationComponents H x ^ n) (_root_.ConnectedComponents.mk (identityPoint H)) =
      _root_.ConnectedComponents.mk ((x ^ n).left (basePoint k)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, translationComponents_point, ← pow_succ']

variable [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- The actual scheme of a smooth affine field group has finitely many connected
components. -/
theorem finite_connectedComponents : Finite (_root_.ConnectedComponents H.X.left) := by
  let : IsLocallyNoetherian H.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  let : CompactSpace H.X.left := QuasiCompact.compactSpace_of_compactSpace H.X.hom
  let : DiscreteTopology (_root_.ConnectedComponents H.X.left) := by
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro c
    obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    rw [← _root_.ConnectedComponents.isQuotientMap_coe.isOpen_preimage,
      connectedComponents_preimage_singleton]
    exact Langlands.AlgebraicGeometry.locallyNoetherianConnectedComponentOpen_proof H.X.left p
  exact finite_of_compact_of_discrete

/-- The order of the component permutation induced by translation. It is
positive when the group is smooth and affine over the field. -/
def positivePowerExponent
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) : ℕ :=
  orderOf (translationComponents H x)

theorem positivePowerExponent_pos
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    0 < positivePowerExponent H x := by
  let := finite_connectedComponents H
  exact orderOf_pos _

omit [Smooth H.X.hom] [IsAffineHom H.X.hom] in
theorem positivePower_mem_identitySet
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    (x ^ positivePowerExponent H x).left (basePoint k) ∈ identitySet H := by
  apply _root_.ConnectedComponents.coe_eq_coe'.mp
  have h := congrArg
    (fun e : Equiv.Perm (_root_.ConnectedComponents H.X.left) =>
      e (_root_.ConnectedComponents.mk (identityPoint H)))
    (pow_orderOf_eq_one (translationComponents H x))
  rw [translationComponents_pow_point] at h
  exact h

theorem positivePower_range_subset
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    Set.range (x ^ positivePowerExponent H x).left ⊆
      Set.range (identityComponentι H).hom.hom.left := by
  rw [range_identityComponentι]
  rintro _ ⟨p, rfl⟩
  have hp : p = basePoint k :=
    @Subsingleton.elim (Spec (CommRingCat.of k)) _ p _
  rw [hp]
  exact positivePower_mem_identitySet H x

/-- The chosen positive power as an actual rational point of the identity component. -/
def positivePowerPoint
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ (identityComponent H).X :=
  FiniteEtaleImage.liftOver (identityComponentι H).hom.hom
    (x ^ positivePowerExponent H x) (positivePower_range_subset H x)

/-- The constructed rational point includes to the chosen positive power. -/
@[reassoc (attr := simp)]
theorem positivePowerPoint_inclusion
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    positivePowerPoint H x ≫ (identityComponentι H).hom.hom =
      x ^ positivePowerExponent H x :=
  FiniteEtaleImage.liftOver_fac _ _ _

end Langlands.GroupScheme.IdentityComponent
