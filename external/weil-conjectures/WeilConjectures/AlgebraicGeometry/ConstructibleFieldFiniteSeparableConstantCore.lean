/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.PointCount
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.ConstructibleSheaf.Pullback

@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry
/-- A finite trivializing datum on the spectrum of a field yields the finite separable
extension and constant pullback in the target theorem.
Source: Stacks Project, Lemma 02GL and the proof of Lemma 09Z6.
(blueprint: lem-weil-pbc-constructible-field-finite-separable-constant-step3-7) -/
theorem constructible_field_finite_separable_constant_of_datum
    (k : Type u) [Field k]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (G : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
    (d : LocallyConstantDatum G)
    (hd : ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((G.over (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            ((Spec (CommRingCat.of k)).smallEtaleTopology.over
              (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ (K : Type u), ∃ (_ : Field K), ∃ (_ : Algebra k K),
      FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ (M : ModuleCat.{u + 1} Λ), Finite M ∧
        Nonempty
          ((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
            (constantSheaf (Spec (CommRingCat.of K)).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  obtain ⟨i, y, _⟩ := d.cover.exists_eq (IsLocalRing.closedPoint k)
  let U := d.cover.X i
  let f := d.cover.f i
  have : Etale f := d.cover.map_prop i
  let K := U.residueField y
  let : Algebra k K := (f.residueFieldAlgebraMap y).toAlgebra
  have ha : (algebraMap k (f y).asIdeal.ResidueField).Etale :=
    RingHom.Etale.of_bijective (Ideal.algEquivResidueFieldOfField (f y).asIdeal).bijective
  let eb := (Scheme.Spec.residueFieldIso (CommRingCat.of k) (f y)).symm
  have hb : (Scheme.Spec.residueFieldIso (CommRingCat.of k) (f y)).inv.hom.Etale :=
    RingHom.Etale.of_bijective
      eb.commRingCatIsoToRingEquiv.bijective
  have hf : (f.residueFieldAlgebraMap y).Etale := by
    change ((f.residueFieldMap y).hom.comp
      ((Scheme.Spec.residueFieldIso (CommRingCat.of k) (f y)).inv.hom.comp
        (algebraMap k (f y).asIdeal.ResidueField))).Etale
    exact RingHom.Etale.stableUnderComposition
      ((Scheme.Spec.residueFieldIso (CommRingCat.of k) (f y)).inv.hom.comp
        (algebraMap k (f y).asIdeal.ResidueField)) (f.residueFieldMap y).hom
      (RingHom.Etale.stableUnderComposition
        (algebraMap k (f y).asIdeal.ResidueField)
        (Scheme.Spec.residueFieldIso (CommRingCat.of k) (f y)).inv.hom ha hb)
      (f.etale_residueFieldMap y)
  have : Algebra.Etale k K := RingHom.etale_algebraMap.mp hf
  have hfin : FiniteDimensional k K := Algebra.FormallyUnramified.finite_of_free k K
  have hsep : Algebra.IsSeparable k K :=
    (Algebra.FormallyEtale.iff_isSeparable k K).mp inferInstance
  obtain ⟨M, hM, ⟨e⟩⟩ := hd i
  let V := d.cover.etalePrecoverageToEtale i
  let E := Etale.overSheafEquiv V (ModuleCat.{u + 1} Λ)
  let e₁ : (Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
    (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) V G).symm ≪≫
      E.functor.mapIso e ≪≫
      ((Etale.overEquiv V).constantSheafSheafCongrIso _ _
        (ModuleCat.{u + 1} Λ) CategoryTheory.Over.mkIdTerminal).app M
  let g := U.fromSpecResidueField y
  refine ⟨K, inferInstance, inferInstance, hfin, hsep, M, hM, ⟨?_⟩⟩
  have hgf : Spec.map (CommRingCat.ofHom (algebraMap k K)) = g ≫ f :=
    f.specMap_residueFieldAlgebraMap y
  exact (eqToIso (congrArg (fun a ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) a).obj G)
      hgf)) ≪≫
    (Etale.upperStarComp (ModuleCat.{u + 1} Λ) g f).app G ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapIso e₁ ≪≫
    (upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).app M
end AlgebraicGeometry
