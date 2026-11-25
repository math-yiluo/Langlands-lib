/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.GenericFiniteAlgebraSplitting
import WeilConjectures.AlgebraicGeometry.SplitTensorAlgebraSchemeComponents

/-!
# Scheme-level generic splitting of a finite morphism

Source: smooth purity blueprint, `sk-prop-sf-cbc`, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`.
(blueprint: lem-weil-pbc-generic-finite-scheme-splitting).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem isUniversalHomeomorphism_of_finite_universally_isHomeomorph
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (hf : (topologically IsHomeomorph).universally f) : IsUniversalHomeomorphism f := by
  have : Surjective f := ⟨(hf _ _ _ .of_id_snd).surjective⟩
  have : UniversallyInjective f := by
    constructor
    intro X' Y' i₁ i₂ f' H
    exact (hf i₁ i₂ f' H).injective
  exact {}

/-- Restriction of a finite étale splitting along a smaller open.
(blueprint: lem-weil-pbc-generic-finite-scheme-splitting) -/
private theorem finite_scheme_splitting_restrict
    (S : Scheme.{u}) {Z : Scheme.{u}} (g : Z ⟶ S)
    (U : S.Opens) (T : Scheme.{u}) (p : T ⟶ U.toScheme)
    [IsFinite p] [Etale p] [Surjective p]
    (n : ℕ) (W : Fin n → (pullback g (p ≫ U.ι)).Opens)
    (hcover : (⨆ i, W i) = ⊤)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    (hW : ∀ i, IsUniversalHomeomorphism
      ((W i).ι ≫ pullback.snd g (p ≫ U.ι))) :
    ∀ V : S.Opens, V ≤ U →
      ∃ (T' : Scheme.{u}) (p' : T' ⟶ V.toScheme),
        IsFinite p' ∧ Etale p' ∧ Surjective p' ∧
        ∃ (W' : Fin n → (pullback g (p' ≫ V.ι)).Opens),
          (⨆ i, W' i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (W' i) (W' j)) ∧
          ∀ i, IsUniversalHomeomorphism
            ((W' i).ι ≫ pullback.snd g (p' ≫ V.ι)) := by
  intro V hVU
  let a := S.homOfLE hVU
  let T' := pullback p a
  let p' : T' ⟶ V.toScheme := pullback.snd p a
  let t : T' ⟶ T := pullback.fst p a
  have ht : t ≫ p ≫ U.ι = p' ≫ V.ι := by
    dsimp [t, p', a]
    rw [← Category.assoc, pullback.condition, Category.assoc, homOfLE_ι]
  let k : pullback g (p' ≫ V.ι) ⟶ pullback g (p ≫ U.ι) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ t) (by
      rw [Category.assoc, ht, pullback.condition])
  have hk : IsPullback (pullback.snd g (p' ≫ V.ι)) k t
      (pullback.snd g (p ≫ U.ι)) := by
    apply IsPullback.of_bot _ _ (IsPullback.of_hasPullback g (p ≫ U.ι)).flip
    · simpa only [k, pullback.lift_fst, ht] using
        (IsPullback.of_hasPullback g (p' ≫ V.ι)).flip
    · simp [k]
  let W' : Fin n → (pullback g (p' ≫ V.ι)).Opens := fun i ↦ k ⁻¹ᵁ W i
  refine ⟨T', p', inferInstance, inferInstance, inferInstance, W', ?_, ?_, ?_⟩
  · apply eq_top_iff.mpr
    intro x _
    have hx : k x ∈ (⨆ i, W i) := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i j hij
    apply disjoint_iff.mpr
    ext x
    change (k x ∈ W i ∧ k x ∈ W j) ↔ False
    have hd := disjoint_iff.mp (hdisjoint hij)
    constructor
    · intro hx
      have : k x ∈ W i ⊓ W j := hx
      rw [hd] at this
      exact this
    · exact False.elim
  · intro i
    have H := (isPullback_morphismRestrict k (W i)).paste_vert hk.flip
    exact MorphismProperty.of_isPullback (P := @IsUniversalHomeomorphism) H (hW i)

/-- A finite map over an integral Noetherian affine base has a dense open on every
subopen of which an etale surjective base change splits its source into finitely
many open components universally homeomorphic to the cover.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, finite-algebra calculation;
steps 1 and 2 of `lem-weil-pbc-finite-map-generic-lisse-preservation`.
(blueprint: lem-weil-pbc-generic-finite-scheme-splitting).

Proof: Write S = Spec A and Z = Spec B, using affineness of finite morphisms.
Apply `lem-weil-pbc-generic-finite-algebra-splitting` to B over A. Its nonzero
c defines a dense principal open U, and its finite etale surjective algebra A'
provides the cover of U. The product decomposition of the reduced tensor algebra
identifies its spectrum with a finite disjoint union of spectra of the factors.
The reduction map is a universal homeomorphism, hence these open-and-closed
components lift uniquely to open-and-closed components of the unreduced source.
Their maps to Spec A' are finite universal homeomorphisms: reduction does not
change integrality, surjectivity, or universal injectivity. For V contained in U,
base change the cover and each component to V. Etaleness, finiteness, surjectivity,
and universal homeomorphisms survive this base change. The pulled-back components
are disjoint opens and cover the source. Their composite maps to the restricted
cover have the required property. If the finite algebra is zero, the source is
empty and the family has no components; the supremum of the empty family is top
in the lattice of opens of the empty source. The choice of U uses no sheaf. -/
theorem exists_dense_open_finite_scheme_splitting
    (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S] [IsAffine S]
    {Z : Scheme.{u}} (g : Z ⟶ S) [IsFinite g] :
    ∃ U : S.Opens, Dense (U : Set S) ∧
      ∀ (V : S.Opens), V ≤ U →
        ∃ (T : Scheme.{u}) (p : T ⟶ V.toScheme),
          IsFinite p ∧ Etale p ∧ Surjective p ∧
          ∃ (n : ℕ) (W : Fin n → (pullback g (p ≫ V.ι)).Opens),
            (⨆ i, W i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (W i) (W j)) ∧
            ∀ i, IsUniversalHomeomorphism
              ((W i).ι ≫ pullback.snd g (p ≫ V.ι)) := by
  let : IsAffine Z := isAffine_of_isAffineHom g
  let : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  let : Algebra Γ(S, ⊤) Γ(Z, ⊤) := g.appTop.hom.toAlgebra
  have : Module.Finite Γ(S, ⊤) Γ(Z, ⊤) := by
    exact (RingHom.finite_algebraMap).mp g.finite_appTop
  obtain ⟨c, A', hRing, hAloc, hA, hTower, hc, hFin, hEt, hSurj,
    n, D, hDR, hDA, hD, he⟩ :=
    exists_generic_finite_algebra_splitting Γ(S, ⊤) Γ(Z, ⊤)
  let : CommRing A' := hRing
  let : Algebra (Localization.Away c) A' := hAloc
  let : Algebra Γ(S, ⊤) A' := hA
  let : IsScalarTower Γ(S, ⊤) (Localization.Away c) A' := hTower
  let : Module.Finite (Localization.Away c) A' := hFin
  let : Algebra.Etale (Localization.Away c) A' := hEt
  let : ∀ i, CommRing (D i) := hDR
  let : ∀ i, Algebra A' (D i) := hDA
  obtain ⟨T, p, hpfin, hpeta, hpsurj, W, hcover, hdisjoint, hW⟩ :=
    finite_scheme_components_of_split_tensor_algebra S g c A' hSurj n D
      (fun i ↦ by
        let : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A' (D i)))) :=
          (hD i).2.2.1
        exact isUniversalHomeomorphism_of_finite_universally_isHomeomorph _ (hD i).2.2.2.2)
      he
  let U := S.basicOpen c
  have hU_dense : Dense (U : Set S) := by
    apply U.isOpen.dense
    rw [Set.nonempty_iff_ne_empty, Ne, TopologicalSpace.Opens.coe_eq_empty,
      basicOpen_eq_bot_iff]
    exact hc
  let : IsFinite p := hpfin
  let : Etale p := hpeta
  let : Surjective p := hpsurj
  refine ⟨U, hU_dense, ?_⟩
  intro V hVU
  obtain ⟨T', p', hpfin', hpeta', hpsurj', W', hcov', hdisj', hW'⟩ :=
    finite_scheme_splitting_restrict S g U T p n W hcover hdisjoint hW V hVU
  exact ⟨T', p', hpfin', hpeta', hpsurj', n, W', hcov', hdisj', hW'⟩

end AlgebraicGeometry.Scheme
