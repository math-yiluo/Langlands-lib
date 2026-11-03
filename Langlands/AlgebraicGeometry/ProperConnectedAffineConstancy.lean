import Langlands.AlgebraicGeometry.GlobalFunctionsFieldProof

/-! # Affine-valued maps from a proper connected reduced scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Global functions on a proper connected reduced scheme over an algebraically
closed field are precisely the base-field constants. -/
theorem isIso_appTop_of_proper_connected_reduced
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    [IsProper p] [ConnectedSpace X] [_root_.AlgebraicGeometry.IsReduced X] :
    IsIso p.appTop := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  have : CompactSpace X := (quasiCompact_iff_compactSpace p).mp inferInstance
  have : PreconnectedSpace (PrimeSpectrum Γ(X, ⊤)) :=
    (show DenseRange X.toSpecΓ from (isDominant_iff _).mp inferInstance).preconnectedSpace
      X.toSpecΓ.continuous
  let g := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop
  have hg : g.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  algebraize [g.hom]
  have : Algebra.IsIntegral k Γ(X, ⊤) := ⟨hg⟩
  have : IsIso g := (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨RingHom.injective _,
      GlobalFunctionsFieldProof.scalar_surjective_of_integral_of_preconnected k Γ(X, ⊤)⟩
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of k)).inv p.appTop

/-- If the structure morphism induces an isomorphism on global functions,
an affine-valued map is constant at its value on any section. -/
theorem affineMap_eq_constant_of_isIso_appTop
    {X S Y : Scheme.{u}} [IsAffine Y] (p : X ⟶ S) [IsIso p.appTop]
    (s : S ⟶ X) (hs : s ≫ p = 𝟙 S) (f : X ⟶ Y) :
    f = p ≫ s ≫ f := by
  apply ext_of_isAffine
  have hps : p.appTop ≫ s.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    ← IsIso.inv_eq_of_hom_inv_id hps]
  simp

/-- Every affine-valued map from a pointed proper connected reduced scheme over
an algebraically closed field equals its constant value at the given point. -/
theorem affineMap_eq_constant_of_proper_connected_reduced
    {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [ConnectedSpace X] [_root_.AlgebraicGeometry.IsReduced X]
    [IsAffine Y] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (s : Spec (CommRingCat.of k) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (f : X ⟶ Y) : f = p ≫ s ≫ f := by
  let := isIso_appTop_of_proper_connected_reduced k X p
  exact affineMap_eq_constant_of_isIso_appTop p s hs f

/-- Evaluation at a specified point identifies affine-valued maps on a proper
connected reduced scheme with their constant values. -/
def properConnectedAffineHomEquiv
    {k : Type u} [Field k] [IsAlgClosed k]
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsProper X.hom] [ConnectedSpace X.left]
    [_root_.AlgebraicGeometry.IsReduced X.left] [IsAffine Y.left]
    (s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    (X ⟶ Y) ≃ (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y) where
  toFun f := s ≫ f
  invFun y := Over.homMk X.hom (by simp) ≫ y
  left_inv f := by
    apply Over.OverMorphism.ext
    exact (affineMap_eq_constant_of_proper_connected_reduced X.hom s.left
      (Over.w s) f.left).symm
  right_inv y := by
    apply Over.OverMorphism.ext
    change s.left ≫ (X.hom ≫ y.left) = y.left
    rw [← Category.assoc, Over.w s]
    change 𝟙 _ ≫ y.left = y.left
    exact Category.id_comp _

end Langlands.AlgebraicGeometry
