/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.RingTheory.IntegralOverHenselianPair
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.SixFunctors.BaseChange.GlobalSections
import WeilConjectures.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion
import WeilConjectures.RingTheory.HenselianPairPrimeConnected
import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Integral schemes over strictly henselian local rings

Source: Stacks Project, Tag 0EYP, via Tags 09XK, 09ZH and 0A3I.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
open Scheme

/-- Tag 03D3: for any scheme morphism, bijectivity of the set-valued adjunction
unit on the identity object implies invertibility of module-section restriction.
Transport through the module/set comparison, reflect bijectivity, and change
from the identity object to the chosen terminal object. -/
private theorem isIso_sections_of_bijective_set_unit
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (p : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hb : Function.Bijective
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ p) (Type (u + 1))
        (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)).unit.app
          ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj G)).hom.app
            (Opposite.op (Scheme.Etale.mk (𝟙 X))))) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) p G) := by
  let R := Λ
  let F := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).obj G
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ p) (Type (u + 1))
    (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)
  let H := (sheafCompose _ (forget (ModuleCat.{u + 1} R))).obj
    ((p)^*[ModuleCat.{u + 1} R].obj G)
  let c := (adj.homEquiv F H).symm
    ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G))
  have : IsIso c := isIso_upperStar_forget_comparison R p G
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

/-- Tags 09XK and 09Y6: in the affine spectrum, the intersection is V(P + IB).
The affine homeomorphism transports its connectedness back to the given closed subset. -/
private theorem integral_connected_inter {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) [IsIntegralHom p]
    {C : Set X} (hC : IsClosed C) (hC' : IsIrreducible C) :
    IsConnected (C ∩ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) := by
  have : IsAffine X := isAffine_of_isAffineHom p
  let B := Γ(X, ⊤)
  let φ := ((Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop).hom
  let : Algebra A B := φ.toAlgebra
  have hint : IsIntegralHom p.steinFactorizationBase := by
    apply (MorphismProperty.cancel_left_of_respectsIso
      (P := @IsIntegralHom) X.toSpecΓ p.steinFactorizationBase).mp
    rw [Scheme.toSpecΓ_steinFactorizationBase]
    infer_instance
  have : Algebra.IsIntegral A B :=
    algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp hint)
  let J := I.map φ
  have : HenselianRing B J := henselianRing_of_isIntegral A I B
  let e := X.isoSpec.schemeIsoToHomeo
  let D : Set (PrimeSpectrum B) := e '' C
  have hD : IsClosed D := e.isClosedMap C hC
  have hD' : IsIrreducible D := hC'.image e e.continuous.continuousOn
  let P := PrimeSpectrum.vanishingIdeal D
  have : P.IsPrime := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hD'
  have hDJ : IsConnected (D ∩ PrimeSpectrum.zeroLocus (J : Set B)) := by
    have hc := isConnected_iff_connectedSpace.mpr
      (PrimeSpectrum.connectedSpace_zeroLocus_sup_of_henselian J P)
    rw [PrimeSpectrum.zeroLocus_sup, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      hD.closure_eq] at hc
    exact hc
  have hpre : p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) =
      e ⁻¹' PrimeSpectrum.zeroLocus (J : Set B) := by
    rw [← Scheme.toSpecΓ_steinFactorizationBase p, Scheme.Hom.comp_base, TopCat.coe_comp]
    rw [Set.preimage_comp]
    change X.toSpecΓ ⁻¹' (PrimeSpectrum.comap φ ⁻¹' _) = _
    rw [PrimeSpectrum.preimage_comap_zeroLocus]
    rw [← PrimeSpectrum.zeroLocus_span, ← Ideal.map]
    rfl
  rw [hpre]
  have hc := hDJ.image e.symm e.symm.continuous.continuousOn
  rw [e.image_symm, Set.preimage_inter] at hc
  simpa only [D, Set.preimage_image_eq _ e.injective] using hc

/-- Tags 09ZF and 09ZG: apply the finite-cover criterion using integral connectedness
to each finite cover, whose composite to the affine base remains integral. -/
private theorem isIso_integral_henselianRestriction
    (Λ : Type (u + 1)) [CommRing Λ] {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] {Y Y₀ : Scheme.{u}}
    (p : Y ⟶ Spec (.of A)) [IsIntegralHom p]
    (i : Y₀ ⟶ Y) (p₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i p₀ p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F) := by
  have : IsAffine Y := isAffine_of_isAffineHom p
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion i :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance
  have hrange : Set.range i = p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
    have hi := Scheme.image_preimage_eq_of_isPullback h.flip (Set.univ : Set (Spec
      (.of (A ⧸ I))))
    have hquot : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
        PrimeSpectrum.zeroLocus (I : Set A) := by
      change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    simpa only [Set.preimage_univ, Set.image_univ, hquot] using hi
  apply isIso_globalSectionsUpperStarMap_of_finite_connected_closed_intersections Λ i
  intro X' q hq C hC hC'
  rw [hrange, ← Set.preimage_comp]
  exact integral_connected_inter I (q ≫ p) hC hC'

/-- Restriction to a closed geometric fibre of an integral scheme over a strictly
henselian local ring is an isomorphism on sections of every module sheaf.

Source: Stacks Project, Tag 0EYP, via Tags 09XK, 09ZH and 0A3I.
(blueprint: lem-sbc-integral-strict-henselian-geometric-fibre-sections).

Proof: Since p is integral and its base is affine, write Z = Spec B, with B integral
 over A. Let m be the maximal ideal of A. The pair (A,m) is henselian, so Tag 09XK
makes (B,mB) henselian. Apply the henselian degree-zero theorem to the proper
identity morphism of Spec B. It makes restriction to Spec(B/mB) invertible. The
closed-point hypothesis on t says that the corresponding map A to Omega has
kernel m. It factors uniquely through k = A/m, which is separably closed. The
Cartesian square identifies Z' with the base change of Spec(B/mB) from k to Omega.
Tag 0A3I makes its canonical restriction bijective for sheaves of sets. The
module/set inverse-image comparison and its adjunction-unit formula transport
that bijection to the module restriction. A module homomorphism with bijective
underlying function is an isomorphism. The composition identity for inverse-image
units and pullback pasting identify the composite of the two restriction maps
with globalSectionsUpperStarMap along i, up to isomorphisms. Hence that map is
invertible. If B is zero then both section modules are zero; the same argument
and identities apply. The coefficient ring may be zero. No algebraicity of Omega
 over k is used. -/
theorem isIso_integralStrictHenselianGeometricFibreRestriction
    (Λ : Type (u + 1)) [CommRing Λ]
    (A : Type u) [CommRing A] [IsStrictlyHenselianLocalRing A]
    {Z Z' : Scheme.{u}} (p : Z ⟶ Spec (.of A)) [IsIntegralHom p]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of A))
    (ht : t (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint A)
    {i : Z' ⟶ Z} {p' : Z' ⟶ Spec (.of Ω)} (sq : IsPullback i p' p t)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F) := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of Ω := Spec.preimage t
  have hφ : Spec.map φ = t := Spec.map_preimage _
  have hker : (⊥ : Ideal Ω).comap φ.hom = IsLocalRing.maximalIdeal A := by
    have hp : (Spec.map φ) default = IsLocalRing.closedPoint A := by
      rw [hφ]
      simpa only [show (default : Spec (.of Ω)) = IsLocalRing.closedPoint Ω from
        Subsingleton.elim _ _] using ht
    have hh := congrArg PrimeSpectrum.asIdeal hp
    simpa only [Spec.map_apply, PrimeSpectrum.comap_asIdeal, Scheme.default_asIdeal,
      IsLocalRing.closedPoint] using hh
  let : IsLocalHom φ.hom := ⟨by
    intro a ha
    by_contra h
    have hm : a ∈ IsLocalRing.maximalIdeal A := h
    rw [← hker] at hm
    have hz : φ.hom a = 0 := hm
    exact (isUnit_iff_ne_zero.mp ha) hz⟩
  let κ := IsLocalRing.ResidueField A
  let ψ : κ →+* Ω := IsLocalRing.ResidueField.lift φ.hom
  let : Algebra κ Ω := ψ.toAlgebra
  let t₀ : Spec (.of κ) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let t₁ : Spec (.of Ω) ⟶ Spec (.of κ) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ Ω))
  have htfac : t = t₁ ≫ t₀ := by
    rw [← hφ]
    dsimp [t₀, t₁]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change Spec.map φ = Spec.map (CommRingCat.ofHom
      (ψ.comp (IsLocalRing.residue A)))
    rw [IsLocalRing.ResidueField.lift_comp_residue]
    rfl
  let i₀ := pullback.fst p t₀
  let p₀ := pullback.snd p t₀
  let F₀ := (upperStar (ModuleCat.{u + 1} Λ) i₀).obj F
  have hi₀ : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i₀ F) :=
    isIso_integral_henselianRestriction Λ (IsLocalRing.maximalIdeal A)
      p i₀ p₀ (IsPullback.of_hasPullback p t₀) F
  have hi₁ : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (pullback.fst p₀ t₁) F₀) := by
    let : (pullback p t₀).Over (Spec (.of κ)) := ⟨p₀⟩
    exact isIso_sections_of_bijective_set_unit Λ (pullback.fst p₀ t₁) F₀
      (etale_sections_base_field_extension κ Ω (pullback p t₀)
        ((sheafCompose _ (forget (ModuleCat.{u + 1} Λ))).obj F₀))
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
