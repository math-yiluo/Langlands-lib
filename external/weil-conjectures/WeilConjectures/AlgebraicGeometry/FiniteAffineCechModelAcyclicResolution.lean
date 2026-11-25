/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechModel
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechAugmentedConstruction
import WeilConjectures.AlgebraicGeometry.OpenPushforwardDerivedComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import WeilConjectures.AlgebraicGeometry.Cohomology.Exact
import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Topology.Sheaves.CechFlasque

/-! # An acyclic resolution representing the specified section complex

Source: Stacks Project, Tags 01XB, 01XD, 01FK and 01FM.
(blueprint: lem-pc-finite-affine-cech-model-acyclic-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The underlying abelian sheaf of an injective `𝒪_X`-module is Čech-acyclic on affine opens,
since it is flasque. -/
private lemma cechAcyclicOnAffines_toAb_of_injective {X : Scheme.{u}}
    (I : X.Modules) [Injective I] :
    cechAcyclicOnAffines X ((toAb X).obj I) :=
  have := isFlasque_of_injective I
  fun _ _ _ _ _ q ↦ TopCat.Sheaf.exactAt_cechComplex_of_isFlasque _ q _

/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules with `M₁` and `M₂`
Čech-acyclic on affine opens, `M₃` is Čech-acyclic on affine opens. -/
private lemma cechAcyclicOnAffines_toAb_X₃ {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : cechAcyclicOnAffines X ((toAb X).obj S.X₁))
    (h₂ : cechAcyclicOnAffines X ((toAb X).obj S.X₂)) :
    cechAcyclicOnAffines X ((toAb X).obj S.X₃) :=
  cechAcyclicOnAffines_X₃ (S := S.map (toAb X)) (hS.map_of_exact (toAb X)) h₁ h₂

/-- Let `f : X ⟶ T` be affine. The pushforward along `f` of a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules, with `M₁` Čech-acyclic on affine opens, is right
exact: `M₂ ⟶ M₃` is surjective on the sections over the affine opens `f ⁻¹ᵁ V`, `V` affine. -/
private lemma epi_pushforward_map_g_of_cechAcyclicOnAffines {X T : Scheme.{u}}
    (f : X ⟶ T) [IsAffineHom f]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : cechAcyclicOnAffines X ((toAb X).obj S.X₁)) : Epi ((pushforward f).map S.g) := by
  refine epi_of_forall_exists_app_eq _ fun W y x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens hx
  obtain ⟨z, hz⟩ := surjective_app_of_cechAcyclicOnAffines (hS.map_of_exact (toAb X)) h₁
    (IsAffineOpen.preimage hV f) (S.X₃.presheaf.map (homOfLE (f.preimage_mono hVW)).op y)
  exact ⟨V, hVW, hxV, z, hz⟩

private theorem affine_rightAcyclic {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [IsAffineHom g] [HasInjectiveResolutions Y.Modules] (M : Y.Modules) [M.IsQuasicoherent] :
    (pushforward g).rightAcyclic M := by
  have : PreservesFiniteLimits (pushforward g) :=
    have := (pullbackPushforwardAdjunction g).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  exact Functor.rightAcyclic_of_epi_map_g (pushforward g)
    (fun N ↦ cechAcyclicOnAffines Y ((toAb Y).obj N))
    (fun I _ ↦ cechAcyclicOnAffines_toAb_of_injective I)
    (fun _ hS h₁ h₂ ↦ cechAcyclicOnAffines_toAb_X₃ hS h₁ h₂)
    (fun S hS h₁ ↦ epi_pushforward_map_g_of_cechAcyclicOnAffines g hS h₁)
    (cechAcyclicOnAffines_of_isQuasicoherent M)

private theorem affine_open_rightAcyclic {X T : Scheme.{u}} (f : X ⟶ T)
    [IsAffine T] [IsSeparated f] (W : X.Opens) (hW : IsAffineOpen W)
    (F : X.Modules) [F.IsQuasicoherent] :
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightAcyclic
      ((pushforward W.ι).obj (F.restrict W.ι)) := by
  have := RingedSpace.moduleGrothendieckAbelian X.toRingedSpace
  have : IsGrothendieckAbelian.{u} W.toScheme.Modules :=
    RingedSpace.moduleGrothendieckAbelian W.toScheme.toRingedSpace
  have : HasInjectiveResolutions W.toScheme.Modules := inferInstance
  have : IsAffine W.toScheme := hW
  have : IsAffineHom (W.ι ≫ f) := inferInstance
  have : IsAffineHom W.ι := IsAffineHom.of_comp W.ι f
  have hJ := affine_rightAcyclic W.ι (F.restrict W.ι)
  intro q
  obtain ⟨e⟩ := open_pushforward_rightDerived_comparison f W (F.restrict W.ι) hJ (q + 1)
  exact (affine_rightAcyclic (W.ι ≫ f) (F.restrict W.ι) q).of_iso e


/-- The finite section model is the termwise pushforward of an acyclic resolution.
This assertion concerns complexes and ordinary direct image, without a derived
localization or a total derived comparison.
Source: Stacks Project, Tags 01XB, 01XD, 01FK and 01FM.
(blueprint: lem-pc-finite-affine-cech-model-acyclic-resolution).

Proof: In degree p form the finite product of j_J,*(F restricted to U_J), where J
runs over the increasing (p+1)-tuples of the cover and U_J is their intersection.
For each deleted entry use the restriction morphism between these open direct
images, with sign (-1)^j. The two orders of deleting entries cancel, so the signed
sum squares to zero. The restriction maps from F augment this complex. On V_i,
insert i into a tuple, sort it with its sign, and put repeated-index contributions
to zero. The signed face calculation gives a contraction of the augmentation;
thus it is locally, and hence globally, a quasi-isomorphism. Equivalently this is
the ordered version of the usual sheaf Cech resolution, via Tags 01FK and 01FM.
Separatedness over the affine target makes each U_J affine. Its inclusion in X
is affine, as its inverse image on any affine chart is an intersection of affine
opens. Both j_J and f composed with j_J have vanishing positive direct images on
F restricted to U_J by affine quasi-coherent acyclicity (01XB). The open inclusion
has exact restriction as its left adjoint and therefore preserves injectives.
Pushing an injective resolution along j_J gives an injective resolution of its
ordinary direct image; composition of pushforwards then proves f_*-acyclicity of
that factor. Finite products of acyclic objects are acyclic. Finally identify
f_*j_J,*(F restricted to U_J) on the affine target with the associated module of
sections of F on U_J. Naturality of the tilde-Gamma identification intertwines
every restriction and therefore the signed differentials. The canonical chart
T to Spec Gamma(T,O) and GammaSpecIso give exactly the scalar restriction and
pullback in finiteAffineCechModel, so these identifications assemble into the
asserted chain isomorphism after extension by zero. For r=0 the covering condition
forces X empty, and the zero complex and unique augmentation give the claim.
When p+1 exceeds r the product is empty and zero; F=0 and empty affine intersections
are also covered by the same construction. Existential witnesses are consumed only
in proofs and never used here to define an arbitrary object. -/
theorem exists_finiteAffineCechModel_acyclic_resolution
    {X T : Scheme.{u}} (f : X ⟶ T) [IsAffine T] [IsSeparated f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent]
    {r : ℕ} (V : Fin r → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hcover : iSup V = ⊤) :
    ∃ (D : CochainComplex X.Modules ℕ)
      (ε : (CochainComplex.single₀ X.Modules).obj F ⟶ D),
      QuasiIso ε ∧
      (∀ p, (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightAcyclic (D.X p)) ∧
      Nonempty (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (D.extend ComplexShape.embeddingUpNat) ≅
          finiteAffineCechModel f F V) := by
  let a := T.toSpecΓ
  have : IsIso a := inferInstanceAs (IsIso T.toSpecΓ)
  let g := pullback.fst (f ≫ a) (𝟙 (Spec Γ(T, ⊤)))
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction g
  let : (tensorPullback g).Additive := adj.left_adjoint_additive
  obtain ⟨D, ε, ⟨q⟩, hε, _, hterms⟩ :=
    exists_affineAlternatingCech_augmented_construction
      (f ≫ a) (𝟙 (Spec Γ(T, ⊤))) V hcover hV F
  refine ⟨D, ε, hε, ?_, ?_⟩
  · intro p
    obtain ⟨n, W, hW, ⟨eW⟩⟩ := hterms p
    let G := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    apply G.rightAcyclic.prop_of_iso eW.symm
    have : G.rightAcyclic.IsClosedUnderFiniteProducts :=
      ObjectProperty.IsClosedUnderFiniteProducts.mk'
    apply G.rightAcyclic.prop_product
    intro j
    exact affine_open_rightAcyclic f (W j) (hW j) F
  · let K := D.extend ComplexShape.embeddingUpNat
    let e : pushforward (f ≫ a) ⋙ Modules.pullback a ≅ pushforward f :=
      Functor.isoWhiskerLeft (pushforward (f ≫ a)) (pullbackIsoPushforwardInv a) ≪≫
        pushforwardComp (f ≫ a) (inv a) ≪≫
        pushforwardCongr (by simp [a])
    exact ⟨((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).app K).symm ≪≫
      ((Modules.pullback a).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso q⟩

end AlgebraicGeometry.Scheme.Modules
