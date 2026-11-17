import Langlands.GroupScheme.Reductive.GeometricAdjoint
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Adjointness recovered from local finite-base comparisons -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Adjointness of a geometric fibre reflects from any point of any
base change above it, without surjectivity of the entire base morphism. -/
theorem isAdjoint_geometricFiber_of_baseChange_at
    {S T : Scheme.{u}} (G : GroupScheme S) (b : T ⟶ S) (t : T)
    (h : IsAdjoint (geometricFiber ((GroupScheme.baseChange b).obj G) t)) :
    IsAdjoint (geometricFiber G (b t)) := by
  have hcomp := h.of_iso (baseChangeCompIso b (geometricPoint T t) G)
  have hfield := (fieldAdjoint_iff_geometricFiber G (geometricPoint T t ≫ b)).mp hcomp
  have himage : (geometricPoint T t ≫ b)
      (IsLocalRing.closedPoint (AlgebraicClosure (T.residueField t))) = b t := by
    change b (T.fromSpecResidueField t _) = b t
    rw [Scheme.fromSpecResidueField_apply]
  rwa [himage] at hfield

namespace AffineWeilPairRecovery

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  {J : Type u} (R D : J → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
  [∀ i, CommRing (D i)] [∀ i, Algebra (R i) (D i)]
  (e : ∀ i, R i ⊗[A] B ≃ₐ[R i] D i)

/-- The actual map of local finite bases obtained from a tensor-algebra
comparison, retaining the original right-hand scalar inclusion. -/
def map (i : J) : Spec (CommRingCat.of (D i)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (e i).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[A] R i ⊗[A] B).toRingHom)

/-- The recovery map is precisely the spectrum of the composite
right-hand inclusion followed by the original algebra equivalence. -/
theorem map_eq (i : J) :
    map A B R D e i = Spec.map (CommRingCat.ofHom
      ((e i).toRingHom.comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] R i ⊗[A] B).toRingHom)) := by
  rw [map, ← Spec.map_comp]
  rfl

/-- A covering family of original base spectra remains covering after
base extension and the supplied tensor-algebra comparisons. -/
theorem covers
    (hcover : ∀ s : Spec (CommRingCat.of A), ∃ i,
      s ∈ Set.range (algebraBaseMap A (R i))) :
    ∀ t : Spec (CommRingCat.of B), ∃ i,
      t ∈ Set.range (map A B R D e i) := by
  intro t
  obtain ⟨i, r, hr⟩ := hcover (algebraBaseMap A B t)
  obtain ⟨q, hqr, hqt⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := algebraBaseMap A (R i)) (g := algebraBaseMap A B) r t hr
  let q' := (pullbackSpecIso A (R i) B).hom q
  let E : Spec (CommRingCat.of (D i)) ≅
      Spec (CommRingCat.of (R i ⊗[A] B)) :=
    Scheme.Spec.mapIso (e i).toRingEquiv.toCommRingCatIso.op
  have hcomp : E.inv ≫ map A B R D e i =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[A] R i ⊗[A] B).toRingHom) := by
    change E.inv ≫ (E.hom ≫ _) = _
    exact E.inv_hom_id_assoc _
  refine ⟨i, E.inv q', ?_⟩
  change (E.inv ≫ map A B R D e i) q' = t
  rw [hcomp]
  change ((pullbackSpecIso A (R i) B).hom ≫ Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] R i ⊗[A] B).toRingHom)) q = t
  exact (congrArg (fun f => f q) (pullbackSpecIso_hom_snd A (R i) B)).trans hqt

variable (G : GroupScheme (Spec (CommRingCat.of B)))
  (H : ∀ i, GroupScheme (Spec (CommRingCat.of (D i))))

/-- If each recovered local group has adjoint geometric fibres, the
original group has adjoint geometric fibres. -/
theorem isFibrewiseAdjoint
    (hcover : ∀ s : Spec (CommRingCat.of A), ∃ i,
      s ∈ Set.range (algebraBaseMap A (R i)))
    (he : ∀ i, Nonempty ((GroupScheme.baseChange (map A B R D e i)).obj G ≅ H i))
    (hH : ∀ i, IsFibrewiseAdjoint (H i)) : IsFibrewiseAdjoint G := by
  intro t
  obtain ⟨i, s, rfl⟩ := covers A B R D e hcover t
  obtain ⟨f⟩ := he i
  have hlocal : IsAdjoint
      (geometricFiber ((GroupScheme.baseChange (map A B R D e i)).obj G) s) :=
    (hH i s).of_iso ((GroupScheme.baseChange (geometricPoint _ s)).mapIso f)
  exact isAdjoint_geometricFiber_of_baseChange_at G (map A B R D e i) s hlocal

end AffineWeilPairRecovery

end Langlands.GroupScheme
