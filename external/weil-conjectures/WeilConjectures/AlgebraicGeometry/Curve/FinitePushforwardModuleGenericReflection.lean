/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.GenericFiniteNoetherianSchemeSplitting
import WeilConjectures.AlgebraicGeometry.DisjointOpenDirectImageRetract
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.ConstructibleSheaf.GenericConstancy
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Finite.BaseChange

/-! # Generic local constancy reflected by a finite direct image

Source: Stacks Project, Tags 095K, 0959, 04DZ and 0A5D, with the module direct-factor
argument in the parent node's proof, steps 1--3.
(blueprint: lem-weil-pbc-finite-module-generic-reflection)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem locallyConstant_of_retract
    {Λ : Type (u + 1)} [CommRing Λ] {S : Scheme.{u}}
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (e : Retract G F) [IsFiniteLocallyConstantSheaf F] : IsLocallyConstantSheaf G := by
  have h : e.i ≫ (𝟙 F - e.r ≫ e.i) = 0 := by simp
  have := (IsLocallyConstantSheaf.kernel_and_cokernel (𝟙 F - e.r ≫ e.i)).1
  refine IsLocallyConstantSheaf.of_iso (F' := G)
    ⟨Limits.kernel.ι _ ≫ e.r, Limits.kernel.lift _ e.i h,
      (cancel_mono (Limits.kernel.ι _)).1 ?_, by simp⟩
  have := Limits.kernel.condition (𝟙 F - e.r ≫ e.i)
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at this
  simpa using this.symm

private theorem locallyConstant_of_split_lowerStar
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (W : Fin n → X.Opens) (hcover : (⨆ j, W j) = ⊤)
    (hdisjoint : Pairwise (fun j k ↦ Disjoint (W j) (W k)))
    (hW : ∀ j, IsUniversalHomeomorphism ((W j).ι ≫ f))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)] :
    IsLocallyConstantSheaf F := by
  let 𝒲 : OpenCover.{u} X :=
    { I₀ := ULift.{u} (Fin n)
      X i := (W i.down).toScheme
      f i := (W i.down).ι
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
        have hx : x ∈ (⨆ j, W j) := by rw [hcover]; trivial
        obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
        exact ⟨⟨j⟩, ⟨x, hj⟩, rfl⟩ }
  let 𝒲' : Cover.{u} etalePrecoverage X := 𝒲.changeProp (Q := @Etale) fun _ ↦ inferInstance
  have hlocal (i : 𝒲'.I₀) : IsLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒲'.f i)).obj F) := by
    let H := (Etale.upperStar (ModuleCat.{u + 1} Λ) (W i.down).ι).obj F
    let q := (W i.down).ι ≫ f
    let : IsUniversalHomeomorphism q := hW i.down
    obtain ⟨e⟩ := nonempty_retract_lowerStar_of_disjoint_open_partition
      Λ f n W hcover hdisjoint F i.down
    have hG : IsLocallyConstantSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) q).obj H) :=
      locallyConstant_of_retract e
    let := hG
    have hH := IsLocallyConstantSheaf.upperStar q
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) q).obj H)
    let := hH
    let := Etale.isEquivalence_lowerStar (ModuleCat.{u + 1} Λ) q
    exact IsLocallyConstantSheaf.of_iso
      (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) q).obj H))
      (asIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).counit.app H))
  let := hlocal
  exact IsLocallyConstantSheaf.of_cover 𝒲' F

/-- Generic local constancy of the source, after shrinking a dense open where the finite
module direct image is finite locally constant. Only the generic part is asserted;
nothing is claimed on the complement.
Source: Stacks Project, Tags 095K, 0959 and 04DZ; module direct-factor refinement of 0A5D.
(blueprint: lem-weil-pbc-finite-module-generic-reflection)

Proof: Reduce the Noetherian target, using the equivalence of etale sites for reduction.
There are finitely many irreducible components. Remove their pairwise intersections and
choose an affine integral dense open in each component, contained in V. Their union is
still dense. On each affine apply generic finite-algebra splitting and shrink further:
a finite etale surjective cover splits the inverse image into finitely many open-and-closed
pieces universally homeomorphic to the cover, including the unreduced source by reduction.
Finite base change identifies the pushforward there with the pullback of the finite locally
constant direct image. The direct image of each piece is a retract of this sheaf.
A retract of a finite locally constant module sheaf is locally constant: trivialize the
ambient sheaf as M, locally express its projector by a linear endomorphism using the finite
generators of M, and take its image. Equivalently its image is the kernel of one minus the
projector, whose local constancy follows from the module kernel theorem without a
Noetherian coefficient hypothesis. Universal-homeomorphism invariance transports this
local constancy to each source piece. Compose the trivializing covers to descend it along
the surjective etale cover, then along the disjoint affine open cover. The finitely many
shrunk opens give U. For an empty target density is vacuous; an empty finite inverse image
has locally constant zero sheaves. No arbitrary object is constructed from this existential
statement: U is used only as an existential witness in proofs. -/
theorem exists_dense_open_locallyConstant_of_finite_lowerStar_module
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [IsFinite f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Opens) (hV : Dense (V : Set Y))
    (h : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) V.ι).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F))) :
    ∃ U : Y.Opens, U ≤ V ∧ Dense (U : Set Y) ∧
      IsLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (f ⁻¹ᵁ U).ι).obj F) := by
  obtain ⟨U, hUV, hUd, 𝒯, hsplit⟩ :=
    exists_dense_open_finite_noetherian_scheme_splitting f V hV
  refine ⟨U, hUV, hUd, ?_⟩
  let G := (Etale.upperStar (ModuleCat.{u + 1} Λ) (f ⁻¹ᵁ U).ι).obj F
  let g := f ∣_ U
  let a := Y.homOfLE hUV
  let := h
  have hM := IsFiniteLocallyConstantSheaf.upperStar a
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) V.ι).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F))
  let := hM
  let eU := ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) a V.ι).app
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).symm ≪≫
    eqToIso (congrArg (fun m ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) m).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)) (Scheme.homOfLE_ι Y hUV))
  have hU : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)) :=
    IsFiniteLocallyConstantSheaf.of_iso
      (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) a).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) V.ι).obj
          ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F))) eU
  let := hU
  have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ)
    (isPullback_morphismRestrict f U).flip
  have hG : IsFiniteLocallyConstantSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).obj G) :=
    IsFiniteLocallyConstantSheaf.of_iso
      (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F))
      (asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ)
        (isPullback_morphismRestrict f U).flip.toCommSq).app F))
  let := hG
  let 𝒞 := 𝒯.pullback₂ g
  have hlocal (i : 𝒞.I₀) : IsLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒞.f i)).obj G) := by
    obtain ⟨n, W, hcover, hdisjoint, hW⟩ := hsplit i
    have hp := IsFiniteLocallyConstantSheaf.upperStar (𝒯.f i)
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).obj G)
    let := hp
    have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback (𝒯.f i) g).flip
    have hfp : IsFiniteLocallyConstantSheaf
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (Limits.pullback.fst (𝒯.f i) g)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (Limits.pullback.snd (𝒯.f i) g)).obj G)) :=
      IsFiniteLocallyConstantSheaf.of_iso
        (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒯.f i)).obj
          ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).obj G))
        (asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ)
          (IsPullback.of_hasPullback (𝒯.f i) g).flip.toCommSq).app G))
    let := hfp
    exact locallyConstant_of_split_lowerStar Λ (Limits.pullback.fst (𝒯.f i) g)
      n W hcover hdisjoint hW
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (Limits.pullback.snd (𝒯.f i) g)).obj G)
  let := hlocal
  exact IsLocallyConstantSheaf.of_cover 𝒞 G

end AlgebraicGeometry.Scheme
