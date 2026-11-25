/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechModel
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteAffineCechSectionBaseChange
import WeilConjectures.AlgebraicGeometry.LinearCechSheafResolution
import WeilConjectures.AlgebraicGeometry.OpenPushforwardDerivedComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.Exact
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
import WeilConjectures.Topology.Sheaves.CechFlasque
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Universal cohomology comparison for the specified finite affine Čech complex

Source: Stacks Project, Tags 02KE, 01XD and 01XK.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

-- Use the dimension-shifting proof of affine vanishing without the proper finiteness
-- declarations bundled into DirectImage.AffineMorphism, which would form an import cycle.
private theorem injective_cech_acyclic {Y : Scheme.{u}} (I : Y.Modules) [Injective I] :
    cechAcyclicOnAffines Y ((toAb Y).obj I) :=
  have := isFlasque_of_injective I
  fun _ _ _ _ _ q ↦ TopCat.Sheaf.exactAt_cechComplex_of_isFlasque _ q _

private theorem cokernel_cech_acyclic {Y : Scheme.{u}} {Q : ShortComplex Y.Modules}
    (hQ : Q.ShortExact) (h₁ : cechAcyclicOnAffines Y ((toAb Y).obj Q.X₁))
    (h₂ : cechAcyclicOnAffines Y ((toAb Y).obj Q.X₂)) :
    cechAcyclicOnAffines Y ((toAb Y).obj Q.X₃) :=
  cechAcyclicOnAffines_X₃ (S := Q.map (toAb Y)) (hQ.map_of_exact (toAb Y)) h₁ h₂

private theorem affine_pushforward_epi {Y S : Scheme.{u}} (h : Y ⟶ S)
    [IsAffineHom h] {Q : ShortComplex Y.Modules} (hQ : Q.ShortExact)
    (h₁ : cechAcyclicOnAffines Y ((toAb Y).obj Q.X₁)) :
    Epi ((Modules.pushforward h).map Q.g) := by
  refine epi_of_forall_exists_app_eq _ fun W y x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens hx
  obtain ⟨z, hz⟩ := surjective_app_of_cechAcyclicOnAffines
    (hQ.map_of_exact (toAb Y)) h₁ (IsAffineOpen.preimage hV h)
    (Q.X₃.presheaf.map (homOfLE (h.preimage_mono hVW)).op y)
  exact ⟨V, hVW, hxV, z, hz⟩

private theorem affine_pushforward_rightAcyclic {Y S : Scheme.{u}} (h : Y ⟶ S)
    [IsAffineHom h] [HasInjectiveResolutions Y.Modules] (M : Y.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M] :
    (Modules.pushforward h).rightAcyclic M := by
  have : PreservesFiniteLimits (Modules.pushforward h) :=
    have := (Modules.pullbackPushforwardAdjunction h).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  exact Functor.rightAcyclic_of_epi_map_g (Modules.pushforward h)
    (fun N ↦ cechAcyclicOnAffines Y ((toAb Y).obj N))
    (fun I _ ↦ injective_cech_acyclic I)
    (fun _ hQ h₁ h₂ ↦ cokernel_cech_acyclic hQ h₁ h₂)
    (fun _ hQ h₁ ↦ affine_pushforward_epi h hQ h₁)
    (cechAcyclicOnAffines_of_isQuasicoherent M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordinary pullback of the specified affine Čech model computes higher direct images.
The complex is fixed by F, U and V; no assertion about an arbitrary flat complex is made.
No relative flatness is needed for this comparison of ordinary section complexes.
Source: Stacks Project, Tag 02KE, affine termwise base-change calculation in the proof
of flat base change; Tags 01XD, 01XK and 01FK for the cohomology comparison.
(blueprint: lem-pc-finite-affine-cech-model-comparison).

Proof: Put Y=f^{-1}(U), p=f|_U and G=F|_Y. On an affine open W of a new base T',
the inverse images of the V_i form a finite affine cover of X'_W. Separatedness over
the affine U makes every nonempty finite intersection of the V_i affine, and their
base changes to W are affine as well. For such an intersection Z, affine pullback
identifies its new section module with Gamma(W,O) tensor over Gamma(U,O) Gamma(Z,G).
The pure-tensor formula commutes with every restriction. Since the products in each
degree are finite, these identifications assemble into an isomorphism of alternating
complexes between ordinary pullback of the specified model and the section complex
of the new cover. The GammaSpecIso scalar restriction and the final pullback along
the canonical affine chart identify exactly these scalar actions, not new choices.
Affine acyclicity and the Čech comparison (01XD), followed by the increasing-tuple
comparison (01FK), identify its homology with cohomology on X'_W. The affine-base
higher-direct-image comparison (01XK) identifies this with sections of R^q f'_*g'^*F
on W. Both identifications come from the augmented Čech resolution, so commute with
restriction to smaller affine opens. Glue them to the stated sheaf isomorphism on T'.
For a supplied cartesian square use its unique isomorphism to the standard pullback;
pullback composition identifies the restricted coefficient with g'^*F. For r=0 the
cover condition forces Y empty, hence X' empty and both complexes compute zero.
No step commutes tensor with homology: it commutes tensor with the finite section
terms before homology, which is why no flatness hypothesis on F or the new base is needed. -/
theorem finiteAffineCechModel_comparison {X T : Scheme.{u}} (f : X ⟶ T)
    [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U) {r : ℕ}
    (V : Fin r → (f ⁻¹ᵁ U).toScheme.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hcover : iSup V = ⊤) :
    ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
      [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
      Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj
          (finiteAffineCechModel (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι) V)).homology q ≅
        (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by
  classical
  intro T' X' g g' f' _ sq q
  let W : ULift.{u} (Fin r) → X'.Opens :=
    fun i ↦ g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ V i.down)
  have hWcover : iSup W = ⊤ := by
    change (⨆ i : ULift.{u} (Fin r),
      g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ V i.down)) = ⊤
    simp only [iSup_ulift]
    rw [← g'.preimage_iSup,
      ← Scheme.Hom.image_iSup, hcover,
      Scheme.Opens.ι_image_top]
    apply top_unique
    intro x _
    change f (g' x) ∈ U
    have hx := congrArg (fun k : X' ⟶ T ↦ k x) sq.w
    change f (g' x) = U.ι (g (f' x)) at hx
    rw [hx]
    exact (g (f' x)).property
  let M := (Modules.pullback g').obj F
  obtain ⟨D, ε, e, hd, _, hterms, hlinear, hε⟩ := exists_linear_cech_sheaf_resolution W hWcover M
  have : QuasiIso ε := hε
  have : IsAffine U.toScheme := hU
  have : IsSeparated (Limits.terminal.from (f ⁻¹ᵁ U).toScheme) := by
    rw [← Limits.terminal.comp_from (f ∣_ U)]
    infer_instance
  have hD : ∀ p, (Modules.pushforward f').rightAcyclic (D.X p) := by
    intro p
    obtain ⟨ep⟩ := hterms p
    apply (Modules.pushforward f').rightAcyclic.prop_of_iso ep.symm
    have : (Modules.pushforward f').rightAcyclic.IsClosedUnderFiniteProducts :=
      ObjectProperty.IsClosedUnderFiniteProducts.mk'
    apply (Modules.pushforward f').rightAcyclic.prop_product
    intro y
    let Z := ⨅ k, V (y k).down
    have hZ : IsAffineOpen Z := IsAffineOpen.iInf (fun k ↦ hV (y k).down)
    have he : (⨅ k, W (y k)) = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z) := by
      apply TopologicalSpace.Opens.ext
      simp only [W, Z, TopologicalSpace.Opens.coe_iInf, Scheme.Hom.coe_preimage,
        Scheme.Hom.coe_image]
      rw [(f ⁻¹ᵁ U).ι.isOpenEmbedding.injective.injOn.image_iInter_eq,
        Set.preimage_iInter]
    obtain ⟨hj, hf⟩ := finiteAffineCech_intersection_baseChange f U hU Z hZ g g' f' sq
    rw [← he] at hj hf
    have : IsAffineHom (⨅ k, W (y k)).ι := hj
    have : IsAffineHom ((⨅ k, W (y k)).ι ≫ f') := hf
    have := Modules.isGrothendieckAbelian (⨅ k, W (y k)).toScheme
    have hacyclic : (Modules.pushforward (⨅ k, W (y k)).ι).rightAcyclic
        (M.restrict (⨅ k, W (y k)).ι) := by
      intro n
      exact affine_pushforward_rightAcyclic _ _ n
    intro n
    obtain ⟨a⟩ := open_pushforward_rightDerived_comparison f' (⨅ k, W (y k))
      (M.restrict (⨅ k, W (y k)).ι) hacyclic (n + 1)
    exact (affine_pushforward_rightAcyclic _
      (M.restrict (⨅ k, W (y k)).ι) n).of_iso a
  have : PreservesFiniteLimits (Modules.pushforward f') := by
    have := (Modules.pullbackPushforwardAdjunction f').rightAdjoint_preservesLimits.{0, 0}
    infer_instance
  obtain ⟨a⟩ := finiteAffineCech_section_baseChange f F U hU V hV g g' f' sq
    D W (fun _ ↦ rfl) e hd hlinear q
  exact ⟨a ≪≫ ((Modules.pushforward f').rightDerivedObjIsoOfResolution ε hD q).symm⟩

end AlgebraicGeometry.Scheme.Modules
