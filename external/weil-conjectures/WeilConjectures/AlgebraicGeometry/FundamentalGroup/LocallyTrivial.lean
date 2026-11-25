/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.Mathlib.RingTheory.TotallySplit

/-!
# Finite étale covers are étale-locally trivial

Let `P ⟶ Y` be finite étale. Every point `y` of `Y` lies in the image of an étale morphism
`U ⟶ Y` over which `P` becomes a trivial cover: `P ×_Y U ≅ ∐_{Fin n} U`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_isPullback_sigma`, blueprint
`lem-fet-locally-trivial`). Over an affine open `Spec R ∋ y` the finite étale `R`-algebra
`A = Γ(P_R)` has constant rank `n` near `y`, so it splits after a faithfully flat finite étale
base change `R_f → T` (`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`), and `U = Spec T`.

The blueprint states the result with a single finite set `S`; since the degree of `P` is only
locally constant, the trivialising cover is given locally around each point.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}}

/-- **Finite étale covers are étale-locally trivial.** For a finite étale `P ⟶ Y` and a point
`y : Y` there are an étale `g : U ⟶ Y` with `y` in its image and a finite set `S` such that the
trivial cover `∐_{s ∈ S} U ⟶ U` is the base change of `P` along `g`.
(blueprint: `lem-fet-locally-trivial`) -/
theorem exists_etale_isPullback_sigma (P : Y.FiniteEtale) (y : Y) :
    ∃ (U : Scheme.{u}) (g : U ⟶ Y) (_ : Etale g) (S : Type u) (_ : Finite S)
      (fst : (∐ fun _ : S ↦ U) ⟶ P.obj.left),
      y ∈ Set.range g ∧ IsPullback fst (Sigma.desc fun _ ↦ 𝟙 U) P.obj.hom g := by
  have : IsFinite P.obj.hom := P.property
  have : Etale P.obj.hom := P.obj.prop
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  let R := Γ(Y, V)
  let A := Γ(P.obj.left, P.obj.hom ⁻¹ᵁ V)
  let φ : R ⟶ A := P.obj.hom.app V
  let : Algebra R A := φ.hom.toAlgebra
  have : Module.Finite R A := Hom.finite_affineAlgebra P.obj.hom hV
  have : Algebra.Etale R A := by
    have := HasRingHomProperty.appLE (P := @Etale) P.obj.hom ‹_› ⟨V, hV⟩
      ⟨_, hV.preimage P.obj.hom⟩ le_rfl
    rw [← Hom.app_eq_appLE] at this
    exact RingHom.etale_algebraMap.mp this
  let p := hV.primeIdealOf ⟨y, hyV⟩
  obtain ⟨f, hpf, n, hrank⟩ := Algebra.exists_rankAtStalk_localizationAway_eq (A := A) p.asIdeal
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hrank
  obtain ⟨m, ⟨e⟩⟩ := hT.nonempty_algEquiv_fun
  let Rf := Localization.Away f
  let : Algebra R T := ((algebraMap Rf T).comp (algebraMap R Rf)).toAlgebra
  have : IsScalarTower R Rf T := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale R T := Algebra.Etale.comp R Rf T
  let e' : T ⊗[R] A ≃ₐ[T] (Fin m → T) :=
    (Algebra.TensorProduct.cancelBaseChange R Rf T T A).symm.trans e
  let ψ : R ⟶ CommRingCat.of T := CommRingCat.ofHom (algebraMap R T)
  let g : Spec (.of T) ⟶ Y := Spec.map ψ ≫ hV.fromSpec
  have hg : Etale g := by
    have : Etale (Spec.map ψ) :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr ‹_›)
    infer_instance
  have hy : y ∈ Set.range g := by
    -- a prime of `R_f` over `p`, and a prime of `T` over it
    have hpf' : f ∉ p.asIdeal := hpf
    let pf : PrimeSpectrum Rf :=
      ⟨p.asIdeal.map (algebraMap R Rf), IsLocalization.isPrime_of_isPrime_disjoint
        (Submonoid.powers f) Rf p.asIdeal p.2 (by
          rw [Set.disjoint_left]
          rintro _ ⟨k, rfl⟩ hk
          exact hpf' (p.2.mem_of_pow_mem k hk))⟩
    obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := Rf) (B := T) pf
    refine ⟨q, ?_⟩
    have hqp : (Spec.map ψ) q = p := by
      rw [Spec.map_apply]
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap R T) q.asIdeal = p.asIdeal
      rw [IsScalarTower.algebraMap_eq R Rf T, ← Ideal.comap_comap]
      change Ideal.comap (algebraMap R Rf) (PrimeSpectrum.comap (algebraMap Rf T) q).asIdeal = _
      rw [hq]
      exact IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) Rf p.2
        (by
          rw [Set.disjoint_left]
          rintro _ ⟨k, rfl⟩ hk
          exact hpf' (p.2.mem_of_pow_mem k hk))
    change hV.fromSpec (Spec.map ψ q) = y
    rw [hqp]
    exact hV.fromSpec_primeIdealOf ⟨y, hyV⟩
  -- the cartesian square `Spec (T ⊗[R] A) → P` over `Spec T → Y`
  have S₁ : IsPullback (hV.preimage P.obj.hom).fromSpec
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) P.obj.hom hV.fromSpec :=
    (Hom.isPullback_SpecMap_app_fromSpec P.obj.hom hV).flip
  have S₂ := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R T A).flip
  have H := S₂.paste_horiz S₁
  let e'' : T ⊗[R] A ≃ₐ[T] (ULift.{u} (Fin m) → T) :=
    e'.trans (AlgEquiv.piCongrLeft' T (fun _ ↦ T) Equiv.ulift.symm)
  let E₁ : Spec (.of (T ⊗[R] A)) ≅ Spec (.of (ULift.{u} (Fin m) → T)) :=
    (Scheme.Spec.mapIso e''.toRingEquiv.toCommRingCatIso.op).symm
  let E : Spec (.of (T ⊗[R] A)) ≅ ∐ fun _ : ULift.{u} (Fin m) ↦ Spec (.of T) :=
    E₁ ≪≫ (asIso (sigmaSpec fun _ : ULift.{u} (Fin m) ↦ CommRingCat.of T)).symm
  refine ⟨Spec (.of T), g, hg, ULift.{u} (Fin m), inferInstance,
    E.inv ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
      A →+* T ⊗[R] A)) ≫ (hV.preimage P.obj.hom).fromSpec, hy,
    H.of_iso E (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp [g, ψ])⟩
  rw [Iso.refl_hom, Category.comp_id, ← cancel_epi E.inv, Iso.inv_hom_id_assoc]
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  simp only [E, E₁, Iso.trans_inv, Iso.symm_inv, asIso_hom, Category.assoc, ι_sigmaSpec_assoc,
    Sigma.ι_comp_desc]
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom e''.toRingEquiv.toRingHom) ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext t
  change e'' (algebraMap T (T ⊗[R] A) t) i = t
  rw [AlgEquiv.commutes]
  rfl

end AlgebraicGeometry.Scheme.FiniteEtale
