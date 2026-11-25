/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.PointCount
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.AlgebraicGeometry.NormalConstantGenericUnit

/-! # General-ring integral stalk detectors

Source: Stacks Project, Tag 09Z6 (3), generic trivialization and normalization.
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Etale

private theorem field_constant
    (k : Type u) [Field k] (Λ : Type (u + 1)) [CommRing Λ]
    (G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf G] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ (M : ModuleCat.{u + 1} Λ), Module.Finite Λ M ∧
        Nonempty
          ((upperStar (ModuleCat.{u + 1} Λ)
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
            (constantSheaf (Spec (.of K)).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := G)
  let x : Spec (.of k) := IsLocalRing.closedPoint k
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
    (S.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
  have hrange : Set.range (S.immersion j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rw [S.range_immersion j]
    exact Subsingleton.elim x y ▸ hj
  let := hS j
  have : IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} Λ) (𝟙 (Spec (.of k)))).obj G) :=
    IsFiniteLocallyConstantSheaf.upperStar_of_range_subset
      (𝟙 (Spec (.of k))) (S.immersion j)
      (by rw [hrange]; exact Set.subset_univ _) G
  have : IsFiniteLocallyConstantSheaf G :=
    IsFiniteLocallyConstantSheaf.of_iso
      ((upperStarId (ModuleCat.{u + 1} Λ) (Spec (.of k))).app G)
  obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
  obtain ⟨i, y, _⟩ := d.cover.exists_eq (IsLocalRing.closedPoint k)
  let U := d.cover.X i
  let f := d.cover.f i
  have : AlgebraicGeometry.Etale f := d.cover.map_prop i
  let K := U.residueField y
  let : Algebra k K := (f.residueFieldAlgebraMap y).toAlgebra
  have ha : (algebraMap k (f y).asIdeal.ResidueField).Etale :=
    RingHom.Etale.of_bijective (Ideal.algEquivResidueFieldOfField (f y).asIdeal).bijective
  let eb := (Scheme.Spec.residueFieldIso (CommRingCat.of k) (f y)).symm
  have hb : (Scheme.Spec.residueFieldIso (CommRingCat.of k) (f y)).inv.hom.Etale :=
    RingHom.Etale.of_bijective eb.commRingCatIsoToRingEquiv.bijective
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
  have hconst := (isConstant_over_iff_upperStar (ModuleCat.{u + 1} Λ)
    (d.cover.etalePrecoverageToEtale i) G).mp (d.isConstant i)
  obtain ⟨M, ⟨e₁⟩⟩ := hconst.mem_essImage
  let g := U.fromSpecResidueField y
  let π := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hgf : π = g ≫ f := f.specMap_residueFieldAlgebraMap y
  let e : (upperStar (ModuleCat.{u + 1} Λ) π).obj G ≅
      (constantSheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
    eqToIso (congrArg (fun a ↦ (upperStar (ModuleCat.{u + 1} Λ) a).obj G) hgf) ≪≫
      (upperStarComp (ModuleCat.{u + 1} Λ) g f).app G ≪≫
      (upperStar (ModuleCat.{u + 1} Λ) g).mapIso e₁.symm ≪≫
      (upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).app M
  let := IsFiniteSheaf.upperStar π G
  let s := (Spec (.of K)).algClosurePoint (IsLocalRing.closedPoint K)
  let P := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have hM : ConcreteCategory.IsFinitelyGenerated M :=
    (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      (F := (upperStar (ModuleCat.{u + 1} Λ) π).obj G) _ s).of_iso
        (P.mapIso e ≪≫ (pointSmallEtale s).sheafFiberConstantSheafIso M)
  exact ⟨K, inferInstance, inferInstance, hfin, hsep,
    M, (ModuleCat.isFinitelyGenerated_iff M).mp hM, ⟨e⟩⟩

/-- Transport the canonical generic-stalk unit along the source-field isomorphism.
The residue-field square makes the generic stalk map invertible; the composition-unit
identity then transfers the normal generic constant theorem (Stacks Project, Tag 09Z5). -/
private theorem isIso_unit_constantSheaf_of_generic_residueFieldIso
    (Λ : Type (u + 1)) [CommRing Λ] (Y : Scheme.{u}) [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (K : Type u) [Field K] (g : Spec (.of K) ⟶ Y) (η : Y)
    (hη : IsGenericPoint η Set.univ) (hgη : g (IsLocalRing.closedPoint K) = η)
    (hres : IsIso (g.residueFieldMap (IsLocalRing.closedPoint K)))
    (M : ModuleCat.{u + 1} Λ) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  have hg : g (IsLocalRing.closedPoint K) = genericPoint Y :=
    hgη.trans (hη.eq (genericPoint_spec Y))
  let : Field ((Spec (.of K)).presheaf.stalk (IsLocalRing.closedPoint K)) :=
    ((stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.isField
      (Field.toIsField K)).toField
  have hyres : IsIso (Y.residue (g (IsLocalRing.closedPoint K))) := by
    rw [hg]
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ⟨RingHom.injective _, Y.residue_surjective _⟩
  have hkres : IsIso ((Spec (.of K)).residue (IsLocalRing.closedPoint K)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ⟨RingHom.injective _, (Spec (.of K)).residue_surjective _⟩
  let := hyres
  let := hkres
  let := hres
  have hstalk : IsIso (g.stalkMap (IsLocalRing.closedPoint K)) := by
    have h := Scheme.residue_residueFieldMap g (IsLocalRing.closedPoint K)
    have : IsIso (g.stalkMap (IsLocalRing.closedPoint K) ≫
        (Spec (.of K)).residue (IsLocalRing.closedPoint K)) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((Spec (.of K)).residue _)
  let := hstalk
  let φ := Scheme.stalkClosedPointTo g
  have : IsIso φ := by
    dsimp [φ, Scheme.stalkClosedPointTo]
    infer_instance
  let e := Spec.map φ
  have : IsIso e := by dsimp [e]; infer_instance
  have hcomp : e ≫ Y.fromSpecStalk (g (IsLocalRing.closedPoint K)) = g :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk g
  have hu : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (Y.fromSpecStalk (g (IsLocalRing.closedPoint K)))).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
    rw [hg]
    exact isIso_unit_constantSheaf_generic_unit Λ hY M
  let := hu
  have hh := upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} Λ) e
    (Y.fromSpecStalk (g (IsLocalRing.closedPoint K)))
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) g hcomp.symm
  have : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) g).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) e
          (Y.fromSpecStalk (g (IsLocalRing.closedPoint K))) g hcomp.symm).hom.app
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
    rw [hh]
    rw [Adjunction.comp_unit_app]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((lowerStar (ModuleCat.{u + 1} Λ) g).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) e
        (Y.fromSpecStalk (g (IsLocalRing.closedPoint K))) g hcomp.symm).hom.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))

/-- A constructible module sheaf over a Noetherian ring admits an integral pushforward map
which is injective on every geometric stalk over a prescribed point.

Source: Stacks Project, Tag 09Z6 (3), proof, Steps 1--5.
(blueprint: new-lem-weil-pbc-noetherian-integral-stalk-embedding).

Proof: Pull back to the residue field of `x`, trivialize after a finite separable extension,
normalize the reduced closure, and use the generic-point constant-sheaf unit. Adjunction
produces the map to the integral pushforward. The lifting of every algebraically closed
geometric point over `x`, together with the stalk comparison and triangle identities, shows
that the map is injective on all stalks above `x`. The coefficient module is finitely
presented because it is a finite module over the Noetherian coefficient ring. This theorem
is the general-ring analogue of the finite-coefficient integral detector.
-/
theorem exists_integral_lowerStar_stalk_injective_noetherian
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] (x : X) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ X), IsIntegralHom ν ∧
      ∃ (M : ModuleCat.{u + 1} Λ), Module.Finite Λ M ∧
        ∃ (φ : F ⟶ (lowerStar (ModuleCat.{u + 1} Λ) ν).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)),
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (s : Spec (.of Ω) ⟶ X),
            ((Scheme.SpecToEquivOfField Ω X) s).1 = x →
              Function.Injective
                (((Scheme.pointSmallEtale s).sheafFiber
                  (A := ModuleCat.{u + 1} Λ)).map φ) := by
  classical
  let G := (upperStar (ModuleCat.{u + 1} Λ) (X.fromSpecResidueField x)).obj F
  let : IsConstructibleSheaf G := IsConstructibleSheaf.upperStar _ F
  obtain ⟨K, hK, hAlg, hfin, _, M, hM, ⟨eK⟩⟩ :=
    field_constant (X.residueField x) Λ G
  let := hK
  let := hAlg
  let := hfin
  obtain ⟨_, _, Y, ν, g, hν, hcomp, hY, hnormal, η, hη, hgη, hres⟩ :=
    normalization_in_finite_residue_field_extension X x K
  let := hY
  have hu := isIso_unit_constantSheaf_of_generic_residueFieldIso Λ Y
    (fun y ↦ (hnormal y).2) K g η hη hgη hres M
  let e : Nonempty
      ((upperStar (ModuleCat.{u + 1} Λ) g).obj
        ((upperStar (ModuleCat.{u + 1} Λ) ν).obj F) ≅
       (upperStar (ModuleCat.{u + 1} Λ) g).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
    ⟨((upperStarComp (ModuleCat.{u + 1} Λ) g ν).app F).symm ≪≫
      eqToIso (congrArg (fun f ↦ (upperStar (ModuleCat.{u + 1} Λ) f).obj F) hcomp.symm) ≪≫
      (upperStarComp (ModuleCat.{u + 1} Λ)
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)))
        (X.fromSpecResidueField x)).app F ≪≫ eK ≪≫
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).app M).symm⟩
  have hlift : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ X), ((SpecToEquivOfField Ω X) s).1 = x →
        ∃ w : Spec (.of Ω) ⟶ Spec (.of K), w ≫ g ≫ ν = s := by
    intro Ω _ _ s hs
    obtain ⟨⟨y, φ⟩, rfl⟩ := (SpecToEquivOfField Ω X).symm.surjective s
    obtain rfl : y = x := by simpa [SpecToEquivOfField] using hs
    let : Algebra (X.residueField y) Ω := φ.hom.toAlgebra
    let l : K →ₐ[X.residueField y] Ω := IsAlgClosed.lift
    refine ⟨Spec.map (CommRingCat.ofHom l.toRingHom), ?_⟩
    rw [← hcomp, ← Spec.map_comp_assoc]
    congr 2
    ext r
    exact l.commutes r
  let : Field K := hK
  let : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := hu
  let A := (upperStar (ModuleCat.{u + 1} Λ) ν).obj F
  let B := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g
  -- Adjunction along g and the invertible unit extend the generic isomorphism.
  let ψ : A ⟶ B := adj.homEquiv A _ e.some.hom ≫ inv (adj.unit.app B)
  have hψ : (upperStar (ModuleCat.{u + 1} Λ) g).map ψ = e.some.hom := by
    dsimp only [ψ]
    rw [Functor.map_comp, Functor.map_inv]
    rw [IsIso.inv_eq_of_hom_inv_id (adj.left_triangle_components B)]
    exact (adj.homEquiv A _).symm_apply_apply e.some.hom
  let adjν := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν
  let φ : F ⟶ (lowerStar (ModuleCat.{u + 1} Λ) ν).obj B := adjν.homEquiv F B ψ
  have hφ : (upperStar (ModuleCat.{u + 1} Λ) ν).map φ ≫ adjν.counit.app B = ψ :=
    (adjν.homEquiv F B).symm_apply_apply ψ
  refine ⟨Y, ν, hν, M, hM, φ, ?_⟩
  intro Ω _ _ s hs
  obtain ⟨w, hw⟩ := hlift Ω s hs
  rw [← Category.assoc] at hw
  subst s
  let c := upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g w
  -- Naturality transports the generic isomorphism to the stalk on Y.
  have hψstalk : IsIso
      (((Scheme.pointSmallEtale (w ≫ g)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map ψ) := by
    have he : IsIso ((upperStar (ModuleCat.{u + 1} Λ) g).map ψ) := by
      rw [hψ]
      infer_instance
    have he' : IsIso
        (((Scheme.pointSmallEtale w).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
          ((upperStar (ModuleCat.{u + 1} Λ) g).map ψ)) := inferInstance
    have hn := c.hom.naturality ψ
    have eq : ((Scheme.pointSmallEtale (w ≫ g)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map ψ =
        c.inv.app A ≫
          ((Scheme.pointSmallEtale w).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
            ((upperStar (ModuleCat.{u + 1} Λ) g).map ψ) ≫ c.hom.app B := by
      rw [← cancel_epi (c.hom.app A)]
      simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.comp_map] using hn.symm
    rw [eq]
    infer_instance
  let d := upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) ν (w ≫ g)
  -- The stalk of φ has an invertible composite, so it is a monomorphism.
  have hfac :
      ((Scheme.pointSmallEtale ((w ≫ g) ≫ ν)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map φ ≫
          (d.inv.app ((lowerStar (ModuleCat.{u + 1} Λ) ν).obj B) ≫
            ((Scheme.pointSmallEtale (w ≫ g)).sheafFiber
              (A := ModuleCat.{u + 1} Λ)).map (adjν.counit.app B)) =
      d.inv.app F ≫ ((Scheme.pointSmallEtale (w ≫ g)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map ψ := by
    rw [← Category.assoc, d.inv.naturality]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp, hφ]
  have : Mono (((Scheme.pointSmallEtale ((w ≫ g) ≫ ν)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map φ) := mono_of_mono_fac hfac
  exact (ModuleCat.mono_iff_injective _).mp this


end AlgebraicGeometry.Etale
