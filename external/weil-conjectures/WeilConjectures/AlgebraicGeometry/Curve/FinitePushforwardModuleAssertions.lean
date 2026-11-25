/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.AlgebraicGeometry.EtaleEdgeMapBaseChange
import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardModuleConstructibleReflection

/-! # Finite direct image of module-valued curve assertions

Source: Stacks Project, Lemma 0A5D, finite pushforward statements.
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
/-- Coefficient torsion conditions descend through the finite direct-image counit. -/
private theorem finite_module_torsion_reflection {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (∀ p : ℕ, Scheme.IsPrimaryTorsionSheaf Λ
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) p →
      Scheme.IsPrimaryTorsionSheaf Λ F p) ∧
    (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k))
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) →
      Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F) := by
  classical
  let G := (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F
  let beta := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app F
  have : Epi beta := by
    classical
    have : CategoryTheory.Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      CategoryTheory.Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    let beta := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app F
    have hstalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
        Epi ((Scheme.pointSmallEtale s).sheafFiber.map beta) := by
      let D := fun t : Scheme.Hom.GeometricFiber f (s ≫ f) ↦
        (Scheme.pointSmallEtale t.1).sheafFiber.obj F
      have : CategoryTheory.Limits.HasLimit (Discrete.functor D) :=
        CategoryTheory.Limits.HasLimitsOfShape.has_limit _
      have hrestrict : Epi (Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f
          (s ≫ f) ⟨s, rfl⟩ F) := by
        have he : (Etale.stalkIsoPi (ModuleCat.{u + 1} Λ) f (s ≫ f) F).hom ≫
            CategoryTheory.Limits.Pi.π D ⟨s, rfl⟩ = _ :=
          CategoryTheory.Limits.Pi.lift_comp_π _ _
        rw [← he]
        infer_instance
      exact epi_of_epi_fac
        (Etale.stalkRestrict_eq_counit (ModuleCat.{u + 1} Λ) f s F).symm
    have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1} (C := X.Etale)
    let hpoints := Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale X
    apply (hpoints.jointlyReflectEpimorphisms (ModuleCat.{u + 1} Λ)).epi_iff beta |>.mpr
    rintro ⟨-, ⟨x⟩⟩
    let e := (Scheme.pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} Λ)
    have := hstalk _ (X.algClosurePoint x)
    let Φ := Scheme.pointSmallEtale (X.algClosurePoint x)
    change Epi ((Φ.ulift.{u + 1}).sheafFiber.map beta)
    rw [← epi_comp_iff_of_isIso _ (e.hom.app F)]
    change Epi (((Scheme.pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}).sheafFiber.map
      beta ≫ e.hom.app F)
    erw [e.hom.naturality beta]
    infer_instance
  have hsurj (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
      Function.Surjective ((Scheme.pointSmallEtale s).sheafFiber.map beta) := by
    have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have : ((Scheme.pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction
        ((Scheme.pointSmallEtale s).skyscraperSheafAdjunction)
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  constructor
  · intro p h Ω _ _ s x
    obtain ⟨z, rfl⟩ := hsurj Ω s x
    let e := ((Etale.upperStarCompSheafFiberIso
      (ModuleCat.{u + 1} Λ) f s).app G).toLinearEquiv
    obtain ⟨n, hn⟩ := h Ω (s ≫ f) (e z)
    have hz : p ^ n • z = 0 := e.injective (by
      simpa only [map_nsmul, map_zero] using hn)
    refine ⟨n, ?_⟩
    simpa only [map_nsmul, map_zero] using
      congrArg ((Scheme.pointSmallEtale s).sheafFiber.map beta).hom hz
  · intro h
    let := h
    constructor
    intro Ω _ _ s x
    obtain ⟨z, rfl⟩ := hsurj Ω s x
    let e := ((Etale.upperStarCompSheafFiberIso
      (ModuleCat.{u + 1} Λ) f s).app G).toLinearEquiv
    obtain ⟨n, hn, hu, he⟩ :=
      Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
        (S := Spec (.of k)) Ω (s ≫ f) (e z)
    have hz : n • z = 0 := e.injective (by
      simpa only [map_nsmul, map_zero] using he)
    refine ⟨n, hn, hu, ?_⟩
    simpa only [map_nsmul, map_zero] using
      congrArg ((Scheme.pointSmallEtale s).sheafFiber.map beta).hom hz

/-- Finite direct image transfers the eight module-valued curve assertions.
Source: Stacks Project, Lemma 0A5D, proof of finite pushforward statements.
(blueprint: b3-finite-pushforward-module-assertions)

Proof: Finite direct image is exact, and the cohomology edge map identifies the
cohomology of F with that of its direct image. The finite geometric-stalk formula
expresses each direct-image stalk as the finite product of source stalks; each
source stalk is a direct factor. Thus primary torsion, invertible torsion orders,
imply the respective source torsion conditions. For constructibility use finite
stratification and direct summands through
Scheme.isConstructibleSheaf_of_finite_lowerStar_module, over arbitrary rings.
The edge isomorphism transfers C1. A finite scheme over an affine is affine, giving
C2; the stalk conditions give C3 and C4. A finite scheme over a proper scheme is
proper, giving C5. For C6 and C7 form the cartesian square over the field extension.
Finite base change identifies the inverse image of the direct image with the
direct image on the base changed source, and the edge maps commute with pullback.
The resulting square has horizontal isomorphisms and a bijective source vertical
map by H, so the target vertical map is bijective. Use the stalk condition for C6
and properness for C7. For C8 repeat the square with any open immersion into Y;
its inverse image is open in X. Transport a class through the edge isomorphism,
lift by H.C8 on X, then transport back. Commutativity and injectivity of the edge
isomorphism verify the lift. Empty finite fibres give zero factors throughout. -/
theorem IsCurve.Assertions.of_finite_pushforward_module {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec (.of k))
    [IsCurve g] [IsFinite f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : IsCurve.Assertions Λ (f ≫ g) F) :
    IsCurve.Assertions Λ g ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) := by
  classical
  let G := (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F
  let A := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  let e (q : ℕ) : Sheaf.H
      ((sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q ≃+
      Sheaf.H A q := by
    let edge := (Sheaf.H.map
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app A) q).comp
      (Etale.cohomologyMap f ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj A) q)
    exact AddEquiv.ofBijective edge (Etale.bijective_edgeMap_of_isFinite f A q)
  have hp {X' Y' : Scheme.{u}} {b : X' ⟶ X} {f' : X' ⟶ Y'} {a : Y' ⟶ Y}
      (sq : IsPullback b f' f a) (q : ℕ) :
      (Function.Bijective (Etale.cohomologyMap a
          ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj A) q) ↔
        Function.Bijective (Etale.cohomologyMap b A q)) ∧
      (Function.Surjective (Etale.cohomologyMap a
          ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj A) q) ↔
        Function.Surjective (Etale.cohomologyMap b A q)) := by
    have : IsIso ((Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app A) := by
      have := Etale.isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} sq
      infer_instance
    obtain ⟨hl, hr⟩ := Etale.bijective_edgeMap_baseChange sq A q inferInstance
    have compare {T₁ T₂ T₃ T₄ : Type (u + 1)}
        (l : T₁ → T₂) (r : T₃ → T₄) (w : T₁ → T₃) (v : T₂ → T₄)
        (hl : Function.Bijective l) (hr : Function.Bijective r)
        (comm : v ∘ l = r ∘ w) :
        (Function.Bijective w ↔ Function.Bijective v) ∧
        (Function.Surjective w ↔ Function.Surjective v) := by
      constructor
      · rw [← hr.of_comp_iff' w, ← comm, hl.of_comp_iff v]
      · constructor
        · intro hw
          exact Function.Surjective.of_comp (comm.symm ▸ hr.surjective.comp hw)
        · intro hv
          exact (Function.Surjective.of_comp_iff' hr w).mp
            (comm ▸ hv.comp hl.surjective)
    apply compare _ _ _ _ hl hr
    exact congrArg DFunLike.coe (Etale.cohomology_edgeMap_baseChange sq A q)
  obtain ⟨hprimary, hinvertible⟩ := finite_module_torsion_reflection Λ (k := k) f F
  have hconstructible (h : Scheme.IsConstructibleSheaf G) :
      Scheme.IsConstructibleSheaf F :=
    Scheme.isConstructibleSheaf_of_finite_lowerStar_module Λ f g F h
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ :=
    (IsCurve.assertions_iff Λ (f ≫ g) F).mp H
  apply (IsCurve.assertions_iff Λ g G).mpr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have := a₁ q hq
    exact (e q).injective.subsingleton
  · intro inst q hq
    have : IsAffine X := isAffine_of_isAffineHom f
    have := a₂ q hq
    exact (e q).injective.subsingleton
  · intro p inst inst' ht q hq
    have := a₃ p (hprimary p ht) q hq
    exact (e q).injective.subsingleton
  · intro inst inst' q
    have := hconstructible (inferInstance : Scheme.IsConstructibleSheaf G)
    have := hinvertible
      (inferInstance : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) G)
    have := a₄ q
    exact Finite.of_injective (e q) (e q).injective
  · intro inst inst' q
    have : IsProper (f ≫ g) := inferInstance
    have := hconstructible (inferInstance : Scheme.IsConstructibleSheaf G)
    have := a₅ q
    exact Finite.of_injective (e q) (e q).injective
  · intro inst k' inst' inst'' Y' ι g' a sq q
    have := hinvertible
      (inferInstance : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) G)
    let b := pullback.fst f a
    let f' := pullback.snd f a
    have sq' : IsPullback b f' f a := IsPullback.of_hasPullback f a
    have sqX : IsPullback b (f' ≫ g') (f ≫ g) ι := sq'.paste_vert sq
    exact (hp sq' q).1.mpr (a₆ k' sqX q)
  · intro inst k' inst' inst'' Y' ι g' a sq q
    have : IsProper (f ≫ g) := inferInstance
    let b := pullback.fst f a
    let f' := pullback.snd f a
    have sq' : IsPullback b f' f a := IsPullback.of_hasPullback f a
    have sqX : IsPullback b (f' ≫ g') (f ≫ g) ι := sq'.paste_vert sq
    exact (hp sq' q).1.mpr (a₇ k' sqX q)
  · intro W a inst
    let b := pullback.fst f a
    let f' := pullback.snd f a
    have sq' : IsPullback b f' f a := IsPullback.of_hasPullback f a
    have : IsOpenImmersion b := inferInstance
    exact (hp sq' 2).2.mpr (a₈ b)
end AlgebraicGeometry
