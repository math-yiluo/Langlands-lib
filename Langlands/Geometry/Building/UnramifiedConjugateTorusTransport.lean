import Langlands.Geometry.Building.UnramifiedConjugateSplittingField
import Langlands.GroupScheme.GaloisPointTowerBaseChange
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.GroupScheme.Torus.MaximalFieldIso
import Langlands.GroupScheme.Rational.MaximalSplitTorusFieldIso

/-! # Conjugated torus and splitting-field transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

section FieldSquare

variable {k K L M : Type u} [Field k] [Field K] [Field L] [Field M]
  [Algebra k L] [Algebra K M]

/-- Splitting is preserved by a compatible isomorphism of field extensions. -/
theorem isSplitTorus_fieldIso_square
    (e : k ≃+* K) (f : L ≃+* M)
    (hcomm : (algebraMap K M).comp e.toRingHom =
      f.toRingHom.comp (algebraMap k L))
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus (baseChanged k L T.toGrp)) :
    IsSplitTorus (baseChanged K M ((CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom e.toRingHom))).obj T).toGrp) := by
  let : Algebra k K := e.toRingHom.toAlgebra
  let : Algebra L M := f.toRingHom.toAlgebra
  let : Algebra k M := (f.toRingHom.comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq' hcomm.symm
  exact IsSplitTorus.of_iso (towerBaseChangeIso k K M T.toGrp)
    (IsSplitTorus.of_iso (towerBaseChangeIso k L M T.toGrp).symm
      (hT.baseChange (baseMap L M)))

end FieldSquare

section Torus

variable {k K : Type u} [Field k] [Field K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {H H' : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ H}

/-- A field isomorphism preserves a maximally split maximal torus. -/
theorem IsMaximallySplitMaximalTorus.baseChange_fieldIso
    (hi : IsMaximallySplitMaximalTorus i) (e : k ≃+* K) :
    IsMaximallySplitMaximalTorus (T := (CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom e.toRingHom))).obj T)
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom e.toRingHom))).map i) := by
  let b := Spec.map (CommRingCat.ofHom e.toRingHom)
  obtain ⟨A, a, f, ha, hf⟩ := hi.2
  refine ⟨hi.1.baseChange_fieldIso e, (CommGroupScheme.baseChange b).obj A,
    (GroupScheme.baseChange b).map a, (GroupScheme.baseChange b).map f,
    ha.baseChange_fieldIso e, ?_⟩
  rw [← Functor.map_comp, hf]

/-- Ambient group isomorphisms preserve the maximally split condition. -/
theorem IsMaximallySplitMaximalTorus.comp_iso
    (hi : IsMaximallySplitMaximalTorus i) (e : H ≅ H') :
    IsMaximallySplitMaximalTorus (i ≫ e.hom) := by
  obtain ⟨A, a, f, ha, hf⟩ := hi.2
  exact ⟨hi.1.comp_iso e, A, a ≫ e.hom, f, ha.comp_iso e,
    by rw [← Category.assoc, hf]⟩

end Torus

section Local

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F)

/-- A chosen extension of an unramified-field automorphism commutes with inclusion. -/
theorem unramifiedLift_commutes :
    (algebraMap (UnramifiedClosure F) (SeparableClosure F)).comp σ.toRingEquiv.toRingHom =
      (σ.liftNormal (SeparableClosure F)).toRingEquiv.toRingHom.comp
        (algebraMap (UnramifiedClosure F) (SeparableClosure F)) := by
  apply RingHom.ext
  intro x
  exact (σ.liftNormal_commutes (SeparableClosure F) x).symm

/-- The image inside the fixed separable closure of a prescribed splitting field. -/
def unramifiedConjugateField
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) :
    IntermediateField (UnramifiedClosure F) (SeparableClosure F) :=
  FieldIsoSquare.conjugateIntermediateField σ.toRingEquiv
    (σ.liftNormal (SeparableClosure F)).toRingEquiv (unramifiedLift_commutes F σ) L

/-- The restriction of the chosen lift to the prescribed splitting field. -/
def unramifiedConjugateFieldEquiv
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) :
    L ≃+* unramifiedConjugateField F σ L :=
  FieldIsoSquare.conjugateIntermediateFieldEquiv σ.toRingEquiv
    (σ.liftNormal (SeparableClosure F)).toRingEquiv (unramifiedLift_commutes F σ) L

theorem unramifiedConjugateFieldEquiv_commutes
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) :
    (algebraMap (UnramifiedClosure F) (unramifiedConjugateField F σ L)).comp
        σ.toRingEquiv.toRingHom =
      (unramifiedConjugateFieldEquiv F σ L).toRingHom.comp
        (algebraMap (UnramifiedClosure F) L) :=
  FieldIsoSquare.conjugateIntermediateFieldEquiv_commutes _ _ _ _

instance unramifiedConjugateField_finiteDimensional
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] :
    FiniteDimensional (UnramifiedClosure F) (unramifiedConjugateField F σ L) :=
  FieldIsoSquare.conjugateIntermediateField_finiteDimensional _ _ _ _

instance unramifiedConjugateField_isGalois
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [IsGalois (UnramifiedClosure F) L] :
    IsGalois (UnramifiedClosure F) (unramifiedConjugateField F σ L) :=
  FieldIsoSquare.conjugateIntermediateField_isGalois _ _ _ _

/-- The prescribed intermediate-field valuations agree under the restriction. -/
theorem unramifiedConjugateFieldEquiv_valuation
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) (x : L) :
    intermediateValuation F (unramifiedConjugateField F σ L)
        (unramifiedConjugateFieldEquiv F σ L x) = intermediateValuation F L x := by
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  apply NNReal.eq
  change spectralNorm F (SeparableClosure F)
      ((σ.liftNormal (SeparableClosure F)) (x : SeparableClosure F)) =
    spectralNorm F (SeparableClosure F) (x : SeparableClosure F)
  exact (spectralNorm_eq_of_equiv (σ.liftNormal (SeparableClosure F)) _).symm

/-- Valuation equivalence in the form required by the norm-transport theorem. -/
theorem unramifiedConjugateFieldEquiv_valuation_isEquiv
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) :
    (intermediateValuation F L).IsEquiv
      ((intermediateValuation F (unramifiedConjugateField F σ L)).comap
        (unramifiedConjugateFieldEquiv F σ L).toRingHom) := by
  intro x y
  change intermediateValuation F L x ≤ intermediateValuation F L y ↔
    intermediateValuation F (unramifiedConjugateField F σ L)
        (unramifiedConjugateFieldEquiv F σ L x) ≤
      intermediateValuation F (unramifiedConjugateField F σ L)
        (unramifiedConjugateFieldEquiv F σ L y)
  rw [unramifiedConjugateFieldEquiv_valuation, unramifiedConjugateFieldEquiv_valuation]

end Local

end Langlands.Geometry.Building
