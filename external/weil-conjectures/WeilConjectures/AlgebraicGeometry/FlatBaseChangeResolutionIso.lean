/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyGluing
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionAffineSections

/-! # Invertibility of the resolution-defined flat base-change map

Source: Stacks Project, Tag 02KH, part (1).
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives

-- Stacks 02KH, qcqs paragraph: the Mayer–Vietoris alternative.
-- Quantifying over open immersions makes the induction invariant under open-chart models.
private theorem flatCohomologyBaseChange_bijective
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of R)) (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Function.Bijective (Scheme.Modules.H.baseChange (S := B) f M q) := by
  classical
  let P (U : X.Opens) : Prop :=
    ∀ (Y : Scheme.{u}) (j : Y ⟶ X) (_ : IsOpenImmersion j), j.opensRange = U →
      ∀ (N : Y.Modules) (_ : N.IsQuasicoherent) (n : ℕ),
        Function.Bijective (Scheme.Modules.H.baseChange (S := B) (j ≫ f) N n)
  have hP : P ⊤ := by
    apply compact_open_induction_on (P := P) ⊤ isCompact_univ
    · intro Y j hj hjrange N hN n
      have : IsEmpty Y := ⟨fun y ↦ by
        have hy : j y ∈ j.opensRange := ⟨y, rfl⟩
        rw [hjrange] at hy
        exact hy⟩
      exact Scheme.Modules.H.baseChange_bijective_of_isSeparated _ N n
    · intro U hU V ih Y j hj hjrange N hN n
      let A : Y.Opens := j ⁻¹ᵁ U
      let C : Y.Opens := j ⁻¹ᵁ V.1
      have hAimage : j ''ᵁ A = U := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hjrange,
          inf_eq_right.mpr le_sup_left]
      have hC : IsAffineOpen C :=
        V.2.preimage_of_isOpenImmersion j (hjrange.symm ▸ le_sup_right)
      have hAc : IsCompact (A : Set Y) :=
        j.isOpenEmbedding.isEmbedding.isCompact_iff.mpr (by
          change IsCompact (j ''ᵁ A : Set X)
          rw [hAimage]
          exact hU)
      have : CompactSpace A.toScheme := isCompact_iff_compactSpace.mp hAc
      have : QuasiSeparatedSpace Y := j.isOpenEmbedding.quasiSeparatedSpace
      have hIc : IsCompact ((A ⊓ C : Y.Opens) : Set Y) :=
        hAc.inter_of_isOpen hC.isCompact A.isOpen C.isOpen
      have : CompactSpace (A ⊓ C).toScheme := isCompact_iff_compactSpace.mp hIc
      have : IsAffine C.toScheme := hC
      have : (A ⊓ C).toScheme.IsSeparated := ⟨by
        rw [← Limits.terminal.comp_from (Y.homOfLE (inf_le_right : A ⊓ C ≤ C))]
        infer_instance⟩
      apply Scheme.Modules.H.baseChange_bijective_of_openCover _ N A C ?_ ?_ ?_ ?_ n
      · change j ⁻¹ᵁ U ⊔ j ⁻¹ᵁ V.1 = ⊤
        rw [← j.preimage_sup, ← hjrange, j.preimage_opensRange]
      · intro r
        apply ih A.toScheme (A.ι ≫ j) inferInstance ?_ _ inferInstance r
        rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, hAimage]
      · intro r
        exact Scheme.Modules.H.baseChange_bijective_of_isSeparated _ _ r
      · intro r
        exact Scheme.Modules.H.baseChange_bijective_of_isSeparated _ _ r
  have h := hP X (𝟙 X) inferInstance (Scheme.Hom.opensRange_of_isIso _) M inferInstance q
  rw [Category.id_comp] at h
  exact h

/-- The actual resolution-defined comparison is invertible for qcqs direct image
of a quasi-coherent module, for every augmented comparison lift.
Source: Stacks Project, Tag 02KH, part (1), using the map of Tag 02N7.
(blueprint: lem-weil-pbc-flat-base-change-resolution-iso)

Proof: Work locally on the two bases, reducing to a flat map of affine rings A → B.
On a finite affine cover of the qcqs source use the Cech-to-cohomology spectral
sequence. Intersections are quasi-compact separated, so their cohomology is computed
by finite affine Cech covers. Base change of their sections is tensor with B and
flat tensor commutes with cohomology. It therefore identifies the spectral sequences
and their abutments. Quasi-coherence of the higher direct images identifies the
result with the sheaf comparison. The comparison is the resolution-defined map:
its augmented lift induces the unit on cocycles, as in 02N7; different augmented
lifts are homotopic and induce the same map. Thus every displayed beta is invertible.
The argument includes degree zero, a zero module, and an empty source. -/
theorem Scheme.Modules.flatBaseChangeResolutionBeta_isIso
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [Flat (pullback.snd g f)]
    (F : X.Modules) [F.IsQuasicoherent]
    (I : InjectiveResolution F)
    (J : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶
      ((Scheme.Modules.pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex)
    (ht : I.ι.f 0 ≫ t.f 0 =
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
        (pullback.snd g f))).unit.app F ≫
          (Scheme.Modules.pushforward (pullback.snd g f)).map (J.ι.f 0)) (p : ℕ) :
    IsIso (Scheme.Modules.flatBaseChangeResolutionBeta f g I J t p) := by
  classical
  let beta := Scheme.Modules.flatBaseChangeResolutionBeta f g I J t p
  let B : Set S'.Opens := { W | IsAffineOpen W ∧
    ∃ V : S.Opens, IsAffineOpen V ∧ W ≤ g ⁻¹ᵁ V }
  have hB : TopologicalSpace.Opens.IsBasis B := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨V, hV, hxV, _⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
        (show g x ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨W, hW, hxW, hWU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp S'.isBasis_affineOpens
        (show x ∈ U ⊓ g ⁻¹ᵁ V from ⟨hx, hxV⟩)
    exact ⟨W, ⟨hW, V, hV, hWU.trans inf_le_right⟩, hxW, hWU.trans inf_le_left⟩
  have hlocal (W : B) : IsIso (Scheme.Modules.Hom.app beta W.1) := by
    obtain ⟨hW, V, hV, e⟩ := W.2
    let : Algebra Γ(S, V) Γ(S', W.1) := (g.appLE V W.1 e).hom.toAlgebra
    have : Module.Flat Γ(S, V) Γ(S', W.1) := g.flat_appLE hV hW e
    have : CompactSpace (f ⁻¹ᵁ V).toScheme :=
      isCompact_iff_compactSpace.mp (f.isCompact_preimage hV.isCompact)
    have : IsAffine V.toScheme := hV
    have : QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme :=
      quasiSeparatedSpace_of_quasiSeparated (f ∣_ V)
    have hb := flatCohomologyBaseChange_bijective
      (B := Γ(S', W.1)) (f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ)
      ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F) p
    have hb' := (Scheme.Modules.flatBaseChangeResolutionBeta_affine_bijective_iff
      f g F I J t ht p V W.1 hV hW e).mpr hb
    exact (ConcreteCategory.isIso_iff_bijective (Scheme.Modules.Hom.app beta W.1)).mpr hb'
  have hs : IsIso ((SheafOfModules.toSheaf S'.ringCatSheaf).map beta) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun W : B ↦ W.1) ?_ hlocal
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hB
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  exact inferInstanceAs
    (IsIso (((SheafOfModules.toSheaf S'.ringCatSheaf).map beta).hom.app (op W)))

end AlgebraicGeometry
