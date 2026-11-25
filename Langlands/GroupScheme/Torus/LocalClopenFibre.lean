import Langlands.GroupScheme.Torus.CompleteLocalSpecialIsoImmersion
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.HomScheme.FibreComparison

/-! # Clopen immersion from a special fibre over a larger residue field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.HomScheme

namespace Langlands.GroupScheme.LocalClopenFibre

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- Pullback evaluation preserves open immersions. -/
theorem isOpenImmersion_evaluate {S : Scheme.{u}} {C D : GroupScheme S}
    {T T' : Over S} (a : T' ⟶ T) (i : RelativeHom C D T)
    (hi : IsOpenImmersion i.hom.hom.left) :
    IsOpenImmersion (evaluate a i).hom.hom.left := by
  have hmap : IsOpenImmersion ((baseChange a.left).map i).hom.hom.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
      (RelativeLevi.isPullback_over_baseChange a.left i.hom.hom).flip hi
  change IsOpenImmersion
    ((Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) C).inv.hom.hom.left ≫
      ((baseChange a.left).map i).hom.hom.left ≫
      (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) D).hom.hom.hom.left)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  infer_instance

/-- Isomorphism of an evaluation is equivalent to isomorphism of its raw pullback. -/
theorem isIso_evaluate_iff {S : Scheme.{u}} {C D : GroupScheme S}
    {T T' : Over S} (a : T' ⟶ T) (i : RelativeHom C D T) :
    IsIso (evaluate a i) ↔ IsIso ((baseChange a.left).map i) := by
  constructor
  · intro hi
    have he : (baseChange a.left).map i =
        (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) C).hom ≫
          evaluate a i ≫
          (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) D).inv := by
      simp [evaluate, Descent.pullHom]
    rw [he]
    infer_instance
  · intro hi
    unfold evaluate Descent.pullHom
    infer_instance

/-- A diagonalizable-source map over a noetherian local ring is clopen if
it becomes an isomorphism over any field whose kernel is the maximal ideal. -/
theorem clopen_of_field_fibre_isIso
    {R K : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K]
    (hker : RingHom.ker (algebraMap R K) = IsLocalRing.maximalIdeal R)
    {C D : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffine D.X.left] [LocallyOfFiniteType D.X.hom]
    (hC : RelativeMultiplicativeType.IsDiagonalizable C) (f : C ⟶ D)
    [IsIso ((baseChange (Spec.algebraMap R K)).map f)] :
    IsOpenImmersion f.hom.hom.left ∧ IsClosedImmersion f.hom.hom.left := by
  let qRing : IsLocalRing.ResidueField R →+* K :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R K)
      (fun x hx => RingHom.mem_ker.mp (hker.symm ▸ hx))
  let : Algebra (IsLocalRing.ResidueField R) K := qRing.toAlgebra
  have hcomp : Spec.algebraMap (IsLocalRing.ResidueField R) K ≫
      Spec.algebraMap R (IsLocalRing.ResidueField R) = Spec.algebraMap R K := by
    rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let q := Spec.algebraMap (IsLocalRing.ResidueField R) K
  obtain ⟨hqsurj, hqflat, hqqc⟩ := fieldExtension_fpqc (IsLocalRing.ResidueField R) K
  have : Surjective q := hqsurj
  have : Flat q := hqflat
  have : QuasiCompact q := hqqc
  have hdir : IsIso ((baseChange
      (q ≫ Spec.algebraMap R (IsLocalRing.ResidueField R))).map f) := by
    rw [hcomp]
    infer_instance
  have : IsIso ((baseChange q).map
      ((baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f)) :=
    (CompleteLocalDeformation.isIso_baseChange_comp_iff _ _ f).mp hdir
  have : IsIso ((baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f) :=
    isIso_of_baseChange q _
  exact CompleteLocalDeformation.open_and_closed_of_special_isIso_of_isDiagonalizable hC f

end Langlands.GroupScheme.LocalClopenFibre
