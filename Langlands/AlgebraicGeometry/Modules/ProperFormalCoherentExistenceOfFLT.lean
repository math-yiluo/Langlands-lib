/-
The hypothesis `hflt` of `properFormalCoherentExistence_of_flt` restates the theorem in
`Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.lean`
of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the
Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The rest of this file was written for this development; see the paired Markdown file.
-/
import Langlands.AlgebraicGeometry.Modules.FormalModuleSystemPresheaves
import Langlands.AlgebraicGeometry.Modules.CoherentPresheafRealization
import Langlands.AlgebraicGeometry.Modules.BasisHomGluing
import Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceStatement
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Proper coherent formal existence from the presheaf existence theorem

Assume the existence theorem for compatible systems of coherent quasi-coherent module presheaves
on a proper scheme over an adically complete noetherian ring (the hypothesis `hflt` below). For
a formal module system `F` with finitely presented terms, the presheaves `U ↦ Γ(F_n, p_n⁻¹ U)`
of `FormalModuleSystemPresheaves` satisfy its hypotheses, so they are the reductions of one
coherent presheaf `G`. Realizing `G` as a finitely presented module sheaf `M` on `X`, the
adjoints of the maps `M ⟶ p_n_* F_n` glued from affine opens are isomorphisms
`p_n^* M ≅ F_n` commuting with all transitions.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceOfFLT

open Langlands.Scheme.Modules FormalModuleSystemPresheaves

section General

variable {Y Z : Scheme.{u}}

/-- The sections of a morphism of module sheaves over an open, as a linear map. -/
def appLinear {A B : Z.Modules} (φ : A ⟶ B) (V : Z.Opens) : Γ(A, V) →ₗ[Γ(Z, V)] Γ(B, V) where
  toFun := φ.app V
  map_add' := map_add _
  map_smul' := AlgebraicGeometry.Scheme.Modules.Hom.app_smul φ

/-- A morphism of module sheaves that is bijective on sections over every member of a basis of
opens is an isomorphism. -/
theorem isIso_of_bijective_of_basis {P : Z.Opens → Prop}
    (hP : ∀ (y : Z) (U : Z.Opens), y ∈ U → ∃ V, P V ∧ y ∈ V ∧ V ≤ U)
    {A B : Z.Modules} (φ : A ⟶ B) (hφ : ∀ V, P V → Function.Bijective (φ.app V)) :
    IsIso φ := by
  let θ : ∀ V : Z.Opens, P V → (Γ(B, V) →ₗ[Γ(Z, V)] Γ(A, V)) := fun V hV =>
    (LinearEquiv.ofBijective (appLinear φ V) (hφ V hV)).symm.toLinearMap
  have hθφ : ∀ V hV (x : Γ(A, V)), θ V hV (φ.app V x) = x := fun V hV x =>
    (LinearEquiv.ofBijective (appLinear φ V) (hφ V hV)).symm_apply_apply x
  have hφθ : ∀ V hV (y : Γ(B, V)), φ.app V (θ V hV y) = y := fun V hV y =>
    (LinearEquiv.ofBijective (appLinear φ V) (hφ V hV)).apply_symm_apply y
  have hθ : ∀ (V V' : Z.Opens) (hV : P V) (hV' : P V') (h : V' ≤ V) (s : Γ(B, V)),
      A.presheaf.map (homOfLE h).op (θ V hV s) = θ V' hV' (B.presheaf.map (homOfLE h).op s) := by
    intro V V' hV hV' h s
    apply (hφ V' hV').1
    rw [hφθ V' hV', ← OpenCoverHomGluing.hom_map_app φ h, hφθ V hV]
  refine ⟨⟨BasisHomGluing.hom hP θ hθ, ?_, ?_⟩⟩
  · refine BasisHomGluing.hom_ext_of_basis hP _ _ fun V hV => ?_
    ext x
    change (BasisHomGluing.hom hP θ hθ).app V (φ.app V x) = x
    rw [BasisHomGluing.hom_app_basis hP θ hθ V hV, hθφ V hV]
  · refine BasisHomGluing.hom_ext_of_basis hP _ _ fun V hV => ?_
    ext y
    change φ.app V ((BasisHomGluing.hom hP θ hθ).app V y) = y
    rw [BasisHomGluing.hom_app_basis hP θ hθ V hV, hφθ V hV]

/-- The adjunction bijection for pullback and pushforward, on sections. -/
lemma homEquiv_app_apply (g : Z ⟶ Y) {M : Y.Modules} {N : Z.Modules}
    (a : (AlgebraicGeometry.Scheme.Modules.pullback g).obj M ⟶ N) (U : Y.Opens) (m : Γ(M, U)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M N) a).app U m =
      a.app (g ⁻¹ᵁ U) (sectionPullback g M U m) := by
  rw [Adjunction.homEquiv_unit, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.pushforward_map_app]
  rfl

/-- Morphisms out of a pullback agree when they agree on pulled-back sections over a basis. -/
lemma pullback_hom_ext_of_basis (g : Z ⟶ Y) {P : Y.Opens → Prop}
    (hP : ∀ (y : Y) (U : Y.Opens), y ∈ U → ∃ V, P V ∧ y ∈ V ∧ V ≤ U)
    {M : Y.Modules} {N : Z.Modules}
    (a b : (AlgebraicGeometry.Scheme.Modules.pullback g).obj M ⟶ N)
    (h : ∀ U, P U → ∀ m : Γ(M, U),
      a.app (g ⁻¹ᵁ U) (sectionPullback g M U m) = b.app (g ⁻¹ᵁ U) (sectionPullback g M U m)) :
    a = b := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M N).injective
  refine BasisHomGluing.hom_ext_of_basis hP _ _ fun U hU => ?_
  ext m
  rw [homEquiv_app_apply, homEquiv_app_apply, h U hU m]

/-- Pullback of a morphism acts on pulled-back sections through the morphism. -/
lemma pullback_map_sectionPullbackLE (g : Z ⟶ Y) {M N : Y.Modules} (c : M ⟶ N) {W : Z.Opens}
    {V : Y.Opens} (h : W ≤ g ⁻¹ᵁ V) (m : Γ(M, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback g).map c).app W (sectionPullbackLE g M h m) =
      sectionPullbackLE g N h (c.app V m) := by
  rw [sectionPullbackLE, sectionPullbackLE, sectionPullback_naturality,
    OpenCoverHomGluing.hom_map_app]

/-- The inverse of the isomorphism `a^* b^* M ≅ c^* M` (for `a ≫ b = c`) on a pulled-back
section. -/
lemma pullbackComp_trans_congr_inv_app {S : Scheme.{u}} (a : S ⟶ Z) (b : Z ⟶ Y) {c : S ⟶ Y}
    (hc : a ≫ b = c) (M : Y.Modules) (V : Y.Opens) (hW : c ⁻¹ᵁ V ≤ a ⁻¹ᵁ (b ⁻¹ᵁ V))
    (m : Γ(M, V)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackComp a b).app M ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr hc).app M).inv.app (c ⁻¹ᵁ V))
        (sectionPullback c M V m) =
      sectionPullbackLE a ((AlgebraicGeometry.Scheme.Modules.pullback b).obj M) hW
        (sectionPullback b M V m) := by
  subst hc
  rw [Iso.trans_inv, Iso.app_inv, Iso.app_inv, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, ← sectionPullbackLE_self (a ≫ b),
    pullbackCongr_inv_sectionPullbackLE rfl M le_rfl le_rfl,
    pullbackComp_inv_sectionPullbackLE a b M le_rfl hW le_rfl, sectionPullbackLE_self b M V m]

lemma basis_affineOpens (Y : Scheme.{u}) :
    ∀ (y : Y) (U : Y.Opens), y ∈ U → ∃ V, V ∈ Y.affineOpens ∧ y ∈ V ∧ V ≤ U := fun _ _ hy => by
  obtain ⟨W, hW, hyW, hWU⟩ := exists_isAffineOpen_mem_and_subset hy
  exact ⟨W, hW, hyW, hWU⟩

/-- For a closed immersion, inverse images of affine opens form a basis of the source. -/
lemma basis_preimage_affineOpens (g : Z ⟶ Y) [IsClosedImmersion g] :
    ∀ (z : Z) (W : Z.Opens), z ∈ W →
      ∃ V, (∃ U : Y.affineOpens, g ⁻¹ᵁ U.1 = V) ∧ z ∈ V ∧ V ≤ W := by
  intro z W hz
  obtain ⟨t, ht, hWt⟩ := g.isClosedEmbedding.isInducing.isOpen_iff.mp W.2
  have hzt : g.base z ∈ t := by
    have : z ∈ W.carrier := hz
    rw [← hWt] at this
    exact this
  obtain ⟨V, hV, hzV, hVt⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨t, ht⟩) hzt
  refine ⟨g ⁻¹ᵁ V, ⟨⟨V, hV⟩, rfl⟩, hzV, fun x hx => ?_⟩
  change x ∈ W.carrier
  rw [← hWt]
  exact hVt hx

end General

section Comparison

open Picard.FormalLineBundle

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {I : Ideal R} (F : FormalModuleSystem f I) {G : OModulePresheaf f}
  (ψ : ∀ n, OModulePresheaf.AffHom G (presheaf F n))
  (M : X.Modules) (e : ∀ U : X.affineOpens, Γ(M, U.1) ≃ₗ[Γ(X, U.1)] G.obj U.1)

/-- On an affine open `V`, the map `Γ(M, V) ⟶ Γ(F_n, p_n⁻¹ V)` given by `ψ_n ∘ e_V`. -/
def thetaLinear (n : ℕ) (V : X.Opens) (hV : V ∈ X.affineOpens) :
    Γ(M, V) →ₗ[Γ(X, V)]
      Γ((AlgebraicGeometry.Scheme.Modules.pushforward (adicProjection f I n)).obj (F.obj n), V) where
  toFun s := (ψ n).app ⟨V, hV⟩ (e ⟨V, hV⟩ s)
  map_add' s t := by simp only [map_add]
  map_smul' a s := by
    change (ψ n).app ⟨V, hV⟩ (e ⟨V, hV⟩ (a • s)) =
      (adicProjection f I n).app V a •
        (show Γ(F.obj n, adicProjection f I n ⁻¹ᵁ V) from (ψ n).app ⟨V, hV⟩ (e ⟨V, hV⟩ s))
    rw [map_smul, (ψ n).app_smul, ← Scheme.Hom.appLE_eq_app]
    rfl

variable {F M e}

lemma thetaLinear_map
    (he : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (s : Γ(M, U.1)),
      e V (M.presheaf.map (homOfLE h).op s) = G.res h (e U s))
    (n : ℕ) (V V' : X.Opens) (hV : V ∈ X.affineOpens) (hV' : V' ∈ X.affineOpens) (h : V' ≤ V)
    (s : Γ(M, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pushforward (adicProjection f I n)).obj
        (F.obj n)).presheaf.map (homOfLE h).op (thetaLinear F ψ M e n V hV s) =
      thetaLinear F ψ M e n V' hV' (M.presheaf.map (homOfLE h).op s) := by
  change _ = (ψ n).app ⟨V', hV'⟩ (e ⟨V', hV'⟩ (M.presheaf.map (homOfLE h).op s))
  rw [he ⟨V, hV⟩ ⟨V', hV'⟩ h]
  exact (OModulePresheaf.AffHom.naturality_apply (ψ n) (U := ⟨V', hV'⟩) (U' := ⟨V, hV⟩) h
    (e ⟨V, hV⟩ s)).symm

variable (he : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (s : Γ(M, U.1)),
  e V (M.presheaf.map (homOfLE h).op s) = G.res h (e U s))

/-- The morphism `M ⟶ p_n_* F_n` glued from `ψ_n ∘ e` on affine opens. -/
def theta (n : ℕ) :
    M ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward (adicProjection f I n)).obj (F.obj n) :=
  BasisHomGluing.hom (basis_affineOpens X) (thetaLinear F ψ M e n) (thetaLinear_map ψ he n)

/-- The comparison `p_n^* M ⟶ F_n`, adjoint to `theta`. -/
def comp (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (adicProjection f I n)).obj M ⟶ F.obj n :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (adicProjection f I n)).homEquiv
    M (F.obj n)).symm (theta ψ he n)

lemma comp_app_sectionPullback (n : ℕ) (U : X.Opens) (hU : U ∈ X.affineOpens) (m : Γ(M, U)) :
    (comp ψ he n).app (adicProjection f I n ⁻¹ᵁ U) (sectionPullback (adicProjection f I n) M U m) =
      (ψ n).app ⟨U, hU⟩ (e ⟨U, hU⟩ m) := by
  rw [← homEquiv_app_apply, comp, Equiv.apply_symm_apply, theta,
    BasisHomGluing.hom_app_basis _ _ _ U hU]
  rfl

/-- Over the inverse image of an affine open, the comparison is bijective on sections. -/
lemma comp_app_bijective [M.IsQuasicoherent] (n : ℕ)
    (hsurj : ∀ U : X.affineOpens, Function.Surjective ((ψ n).app U))
    (hker : ∀ U : X.affineOpens,
      LinearMap.ker ((ψ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)))
    (U : X.affineOpens) :
    Function.Bijective ((comp ψ he n).app (adicProjection f I n ⁻¹ᵁ U.1)) := by
  set p := adicProjection f I n with hp
  have hσ : Function.Surjective (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact Scheme.Hom.app_surjective p U.1 U.2
  have hT := pullbackTensorMap_bijective p M (le_refl (p ⁻¹ᵁ U.1)) (U.2.preimage p) U.2
  let g := ((comp ψ he n).app (p ⁻¹ᵁ U.1)).hom.comp
    (pullbackTensorMap p M (le_refl (p ⁻¹ᵁ U.1))).hom.toAddMonoidHom
  have hg1 : ∀ m : Γ(M, U.1),
      g ((1 : Γ(adicSpace f I n, p ⁻¹ᵁ U.1)) ⊗ₜ[Γ(X, U.1), (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom] m) =
        (ψ n).app U (e U m) := by
    intro m
    change (comp ψ he n).app (p ⁻¹ᵁ U.1) (pullbackTensorMap p M (le_refl (p ⁻¹ᵁ U.1))
      ((1 : Γ(adicSpace f I n, p ⁻¹ᵁ U.1)) ⊗ₜ[Γ(X, U.1), (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom]
        m)) = _
    rw [pullbackTensorMap_one_tmul, sectionPullbackLE_self,
      comp_app_sectionPullback ψ he n U.1 U.2]
  have hg : Function.Bijective g := by
    refine bijective_of_one_tmul hσ g (fun t => ?_) (fun m hm => ?_)
    · obtain ⟨y, rfl⟩ := hsurj U t
      obtain ⟨m, rfl⟩ := (e U).surjective y
      exact ⟨m, hg1 m⟩
    · rw [hg1] at hm
      have h1 : e U m ∈ I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)) := by
        rw [← hker U]
        exact hm
      let _ := Scheme.TwoAffineOpenCover.algebraOfHom f U.1
      have : IsScalarTower R Γ(X, U.1) (G.obj U.1) := G.isScalarTower U.1
      set J : Ideal Γ(X, U.1) := (I ^ (n + 1)).map (algebraMap R Γ(X, U.1)) with hJ
      have h2 : e U m ∈ J • (⊤ : Submodule Γ(X, U.1) (G.obj U.1)) := by
        rw [← Submodule.restrictScalars_mem R, hJ, Ideal.smul_restrictScalars,
          Submodule.restrictScalars_top]
        exact h1
      have h3 : m ∈ (J • (⊤ : Submodule Γ(X, U.1) (G.obj U.1))).map (e U).symm.toLinearMap :=
        ⟨e U m, h2, (e U).symm_apply_apply m⟩
      rw [Submodule.map_smul''] at h3
      have hJσ : J ≤ RingHom.ker (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom := by
        rw [hJ, Ideal.map_le_iff_le_comap]
        intro r hr
        rw [Ideal.mem_comap, RingHom.mem_ker]
        exact (appLE_algebraMap_comp f p U.1 (p ⁻¹ᵁ U.1) le_rfl r).trans
          (algebraMap_adicProjection_eq_zero f I n _ hr)
      exact Submodule.smul_mono hJσ le_top h3
  exact (Function.Bijective.of_comp_iff _ hT).mp hg

lemma isIso_comp [M.IsQuasicoherent] (n : ℕ)
    (hsurj : ∀ U : X.affineOpens, Function.Surjective ((ψ n).app U))
    (hker : ∀ U : X.affineOpens,
      LinearMap.ker ((ψ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1))) :
    IsIso (comp ψ he n) := by
  refine isIso_of_bijective_of_basis (basis_preimage_affineOpens (adicProjection f I n)) _ ?_
  rintro V ⟨U, rfl⟩
  exact comp_app_bijective ψ he n hsurj hker U

omit F in
/-- The inverse transition of the restrictions of `M` on a pulled-back section. -/
lemma ofModule_transition_inv_app (M : X.Modules) (n : ℕ) (U : X.Opens) (m : Γ(M, U)) :
    (((FormalModuleSystem.ofModule f I M).transition n).inv.app (adicProjection f I n ⁻¹ᵁ U))
        (sectionPullback (adicProjection f I n) M U m) =
      sectionPullbackLE (adicTransition f I n)
        ((AlgebraicGeometry.Scheme.Modules.pullback (adicProjection f I (n + 1))).obj M)
        (le_adicTransition_preimage f I n U)
        (sectionPullback (adicProjection f I (n + 1)) M U m) := by
  exact pullbackComp_trans_congr_inv_app (adicTransition f I n) (adicProjection f I (n + 1))
    (adicTransition_projection f I n) M U _ m

/-- The comparisons commute with the transitions of `F` and of the restrictions of `M`. -/
lemma comp_commutes
    (hcomp : ∀ n (U : X.affineOpens),
      (phi F n).app U ∘ₗ (ψ (n + 1)).app U = (ψ n).app U) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (adicTransition f I n)).map (comp ψ he (n + 1)) ≫
        (F.transition n).hom =
      ((FormalModuleSystem.ofModule f I M).transition n).hom ≫ comp ψ he n := by
  rw [← Iso.inv_comp_eq]
  refine pullback_hom_ext_of_basis (adicProjection f I n) (basis_affineOpens X) _ _
    fun U hU m => ?_
  change (F.transition n).hom.app _
      (((AlgebraicGeometry.Scheme.Modules.pullback (adicTransition f I n)).map
        (comp ψ he (n + 1))).app _
        (((FormalModuleSystem.ofModule f I M).transition n).inv.app _
          (sectionPullback (adicProjection f I n) M U m))) = _
  rw [ofModule_transition_inv_app, pullback_map_sectionPullbackLE]
  have hc := LinearMap.congr_fun (hcomp n ⟨U, hU⟩) (e ⟨U, hU⟩ m)
  rw [LinearMap.comp_apply, phi_app] at hc
  refine Eq.trans ?_ (comp_app_sectionPullback ψ he n U hU m).symm
  refine Eq.trans ?_ hc
  exact congrArg (transitionSections F n U) (comp_app_sectionPullback ψ he (n + 1) U hU m)

end Comparison

/-- Proper coherent formal existence, assuming the existence theorem for compatible systems of
coherent quasi-coherent module presheaves on a proper scheme over an adically complete noetherian
ring. -/
theorem properFormalCoherentExistence_of_flt
    (hflt : ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
      {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
      (F : ℕ → OModulePresheaf q), (∀ k, (F k).IsCoherent) → (∀ k, (F k).IsQuasicoherent) →
      ∀ (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k)),
      (∀ k (U : P.affineOpens), Function.Surjective ((φ k).app U)) →
      (∀ k (U : P.affineOpens), LinearMap.ker ((φ k).app U) =
        I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) →
      ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
        G.IsCoherent ∧ G.IsQuasicoherent ∧
        (∀ k (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
        (∀ k (U : P.affineOpens), LinearMap.ker ((ψ k).app U) =
          I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
        (∀ k (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U)) :
    ProperFormalCoherentExistenceStatement.{u} := by
  intro R _ _ _ _ X f hf F hF
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨G, ψ, hGc, hGq, hsurj, hker, hcomp⟩ := hflt (IsLocalRing.maximalIdeal R) f
    (presheaf F) (isCoherent_presheaf F hF) (isQuasicoherent_presheaf F hF) (phi F)
    (fun n U => (surjective_and_ker_phi F hF n U).1)
    (fun n U => (surjective_and_ker_phi F hF n U).2)
  obtain ⟨M, e, hM, he⟩ := CoherentPresheafRealization.exists_modules_sectionsEquiv hGq hGc
  have : M.IsFinitePresentation := hM
  have hiso := fun n => isIso_comp ψ he n (hsurj n) (hker n)
  exact ⟨M, hM, ⟨{
    component := fun n => @asIso _ _ _ _ (comp ψ he n) (hiso n)
    commutes := comp_commutes ψ he hcomp }⟩⟩

end Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceOfFLT
