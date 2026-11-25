/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero

/-! # Proper sections over a strictly local base and its geometric closed fibre

Source: Stacks Project, Tags 0A0C, 0A3I and 0A3T.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem isIso_sections_fieldExtension
    (Λ : Type (u + 1)) [CommRing Λ]
    {k K : Type u} [Field k] [Field K] [IsSepClosed k] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) G) := by
  let R := Λ
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let F := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).obj G
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ p) (Type (u + 1))
    (X.smallGrothendieckTopology @Etale)
    ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).smallGrothendieckTopology
      @Etale)
  let H := (sheafCompose _ (forget (ModuleCat.{u + 1} R))).obj
    ((p)^*[ModuleCat.{u + 1} R].obj G)
  let c := (adj.homEquiv F H).symm
    ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G))
  have : IsIso c := isIso_upperStar_forget_comparison R p G
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have hb := etale_sections_base_field_extension k K X F
  have hc : Function.Bijective (c.hom.app
      (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ p).obj (Scheme.Etale.mk (𝟙 X))))) :=
    (isIso_iff_bijective _).mp (inferInstance)
  have hfac := congrArg (fun a ↦ a.hom.app (Opposite.op (Scheme.Etale.mk (𝟙 X))))
    ((adj.homEquiv F H).apply_symm_apply
      ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G)))
  rw [Adjunction.homEquiv_unit] at hfac
  change (adj.unit.app F).hom.app (Opposite.op (Scheme.Etale.mk (𝟙 X))) ≫
    c.hom.app (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ p).obj
      (Scheme.Etale.mk (𝟙 X)))) =
    (forget (ModuleCat.{u + 1} R)).map
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom.app
        (Opposite.op (Scheme.Etale.mk (𝟙 X)))) at hfac
  have hu : Function.Bijective
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom.app
        (Opposite.op (Scheme.Etale.mk (𝟙 X)))) := by
    change Function.Bijective ((forget (ModuleCat.{u + 1} R)).map
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom.app
        (Opposite.op (Scheme.Etale.mk (𝟙 X)))))
    rw [← hfac]
    exact hc.comp hb
  have : IsIso (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom.app
      (Opposite.op (Scheme.Etale.mk (𝟙 X)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hu
  unfold globalSectionsUpperStarMap
  have ht : IsIso (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
      (Opposite.op (⊤_ X.Etale))).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G)) := by
    change IsIso (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom.app
      (Opposite.op (⊤_ X.Etale)))
    let e := terminalIsoIsTerminal (MorphismProperty.Over.mkIdTerminal @Etale X)
    let T := ((p)_*[ModuleCat.{u + 1} R].obj ((p)^*[ModuleCat.{u + 1} R].obj G)).obj
    let α : G.obj ⟶ T := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom
    have he : IsIso (α.app (Opposite.op (⊤_ X.Etale)) ≫ T.map e.inv.op) := by
      rw [← α.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (T.map e.inv.op)
  infer_instance

/-- Restriction to a geometric closed fibre preserves sections over a strictly local base.
Source: Stacks Project, Tags 0A0C, 0A3I and 0A3T
(auxiliary; not a blueprint node).

Proof: factor `t` through the residue field of R; its image is the closed point, so its
ring map kills exactly the maximal ideal. Restrict first to the residue-field fibre.
The henselian-pair comparison for the maximal ideal (Tag 0A0C) makes this restriction
invertible. The residue field is separably closed. Tag 0A3I makes restriction from that
fibre to its extension to Ω bijective on underlying sets, hence invertible on modules.
The pullback pasting isomorphism identifies this iterated fibre with the specified
cartesian model Z₀. Functoriality of globalSectionsUpperStarMap identifies the composite
with the map in the statement. A different cartesian model changes it only by an
isomorphism. This includes the empty fibre and arbitrary, possibly transcendental Ω. -/
theorem isIso_globalSectionsUpperStarMap_of_strictLocal_geometricClosedPoint
    (Λ : Type (u + 1)) [CommRing Λ]
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {Z Z₀ : Scheme.{u}} {p : Z ⟶ Spec (.of R)} [IsProper p]
    {i : Z₀ ⟶ Z} {p₀ : Z₀ ⟶ Spec (.of Ω)} (t : Spec (.of Ω) ⟶ Spec (.of R))
    (ht : t default = IsLocalRing.closedPoint R) (sq : IsPullback i p₀ p t)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F) := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of Ω := Spec.preimage t
  have hφ : Spec.map φ = t := Spec.map_preimage _
  have hker : (⊥ : Ideal Ω).comap φ.hom = IsLocalRing.maximalIdeal R := by
    have hp : (Spec.map φ) default = IsLocalRing.closedPoint R := by
      rw [hφ]
      exact ht
    have hh := congrArg PrimeSpectrum.asIdeal hp
    simpa only [Spec.map_apply, PrimeSpectrum.comap_asIdeal, Scheme.default_asIdeal,
      IsLocalRing.closedPoint] using hh
  let : IsLocalHom φ.hom := ⟨by
    intro a ha
    by_contra h
    have hm : a ∈ IsLocalRing.maximalIdeal R := h
    rw [← hker] at hm
    have hz : φ.hom a = 0 := hm
    exact (isUnit_iff_ne_zero.mp ha) hz⟩
  let κ := IsLocalRing.ResidueField R
  let ψ : κ →+* Ω := IsLocalRing.ResidueField.lift φ.hom
  let : Algebra κ Ω := ψ.toAlgebra
  let t₀ : Spec (.of κ) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let t₁ : Spec (.of Ω) ⟶ Spec (.of κ) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ Ω))
  have htfac : t = t₁ ≫ t₀ := by
    rw [← hφ]
    dsimp [t₀, t₁]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change Spec.map φ = Spec.map (CommRingCat.ofHom
      (ψ.comp (IsLocalRing.residue R)))
    rw [IsLocalRing.ResidueField.lift_comp_residue]
    rfl
  let i₀ := pullback.fst p t₀
  let p₀ := pullback.snd p t₀
  let F₀ := (upperStar (ModuleCat.{u + 1} Λ) i₀).obj F
  have hi₀ : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i₀ F) :=
    isIso_globalSectionsUpperStarMap_of_henselianRing Λ (IsLocalRing.maximalIdeal R)
      p i₀ p₀ (IsPullback.of_hasPullback p t₀) F
  have hi₁ : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (pullback.fst p₀ t₁) F₀) := isIso_sections_fieldExtension Λ p₀ F₀
  let v := (pullbackLeftPullbackSndIso p t₀ t₁).inv ≫ pullback.fst p₀ t₁
  have hv₀ : v ≫ i₀ = pullback.fst p (t₁ ≫ t₀) := by simp [v, p₀, i₀]
  have hv : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) v F₀) := by
    have hc : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) v F₀ ≫
        (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
          ((upperStarComp (ModuleCat.{u + 1} Λ)
            (pullbackLeftPullbackSndIso p t₀ t₁).inv (pullback.fst p₀ t₁)).hom.app F₀)) := by
      rw [globalSectionsUpperStarMap_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right
      (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) v F₀)
      ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ)
          (pullbackLeftPullbackSndIso p t₀ t₁).inv (pullback.fst p₀ t₁) v rfl).hom.app F₀))
  have hcan : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (pullback.fst p t) F) := by
    rw [htfac, ← hv₀]
    have hc : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) (v ≫ i₀) F ≫
        (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) v i₀).hom.app F)) := by
      rw [globalSectionsUpperStarMap_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right
      (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) (v ≫ i₀) F)
      ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) v i₀ (v ≫ i₀) rfl).hom.app F))
  rw [← sq.isoPullback_hom_fst]
  have hc : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (sq.isoPullback.hom ≫ pullback.fst p t) F ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) sq.isoPullback.hom
          (pullback.fst p t)).hom.app F)) := by
    rw [globalSectionsUpperStarMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (sq.isoPullback.hom ≫ pullback.fst p t) F)
    ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) sq.isoPullback.hom
        (pullback.fst p t) (sq.isoPullback.hom ≫ pullback.fst p t) rfl).hom.app F))

end AlgebraicGeometry.Etale
