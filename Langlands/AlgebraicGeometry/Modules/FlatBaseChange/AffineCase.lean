import Langlands.AlgebraicGeometry.Modules.HigherDirectImageBaseChange
import Langlands.Cohomology.ExactBaseChange.ResolutionMap
import Langlands.AlgebraicGeometry.Modules.CechResolution.CechTermDirectImageProof
import Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeOfIsoProof
import Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeOf
import Langlands.AlgebraicGeometry.Modules.CechResolution.AffineSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.CechResolution.Exact
import Langlands.AlgebraicGeometry.Modules.PullbackQuasicoherent
import Langlands.AlgebraicGeometry.OrderedAffineCoverCompact
import Langlands.Cohomology.AdditiveAdjunction

/-!
# Flat base change of higher direct images over an affine base

For a ring map `φ : R ⟶ T`, a quasi-compact separated `f : X ⟶ Spec R`, a cartesian square
`p ≫ f = f' ≫ Spec.map φ` with exact pullbacks along `Spec.map φ` and `p`, and a quasi-coherent
`M`, every component `(higherDirectImageBaseChangeNatTrans (Spec.map φ) f f' p w n).app M` is an
isomorphism. The proof applies the published `resolutionCompatibility` to the sheafified Čech
resolutions of `M` and of `p^* M`, with the published `cechTermDirectImage` and
`pushforwardBaseChangeOfIso`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.FlatBaseChange

open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution
open Langlands.Cohomology.ExactBaseChange
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules.CechResolution

section Adjunct

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsAffineHom g] (𝒰 : X.OrderedAffineCover)
  (M : X.Modules)

/-- The `g^* ⊣ g_*` adjunct of `cechPullback`: a chain map
`g^* C(𝒰, M) ⟶ C(g⁻¹𝒰, g^* M)`. -/
def cechPullbackAdjunct :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechComplex 𝒰 M) ⟶
      cechComplex (inverseImageCover g 𝒰) ((Scheme.Modules.pullback g).obj M) :=
  ((Langlands.Cohomology.complexAdjunction (Scheme.Modules.pullbackPushforwardAdjunction g)
    (ComplexShape.up ℕ)).homEquiv _ _).symm (cechPullback g 𝒰)

lemma cechPullbackAdjunct_f (q : ℕ) :
    (cechPullbackAdjunct g 𝒰 M).f q =
      (Scheme.Modules.pullback g).map ((cechPullback g 𝒰).f q) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app _ := by
  simp [cechPullbackAdjunct, Adjunction.homEquiv_counit]

/-- The unit of `g` followed by `g_*` of a component of the adjunct is the component of
`cechPullback`. -/
lemma unit_comp_pushforward_cechPullbackAdjunct_f (q : ℕ) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app _ ≫
        (Scheme.Modules.pushforward g).map ((cechPullbackAdjunct g 𝒰 M).f q) =
      (cechPullback g 𝒰).f q := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).apply_symm_apply
    ((cechPullback (M := M) g 𝒰).f q)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at h
  rw [cechPullbackAdjunct_f]
  exact h

/-- The adjunct is compatible with the augmentations. -/
theorem mapResolutionAugmentation_cechPullbackAdjunct :
    mapResolutionAugmentation (Scheme.Modules.pullback g) (cechAug 𝒰 M) ≫
        cechPullbackAdjunct g 𝒰 M =
      cechAug (inverseImageCover g 𝒰) ((Scheme.Modules.pullback g).obj M) := by
  apply HomologicalComplex.from_single_hom_ext
  have h := congrArg (fun φ => HomologicalComplex.Hom.f φ 0) (cechAug_cechPullback (M := M) g 𝒰)
  simp only [HomologicalComplex.comp_f, mapResolutionAugmentation_f_zero] at h
  rw [HomologicalComplex.comp_f, mapResolutionAugmentation_f_zero, cechPullbackAdjunct_f]
  have key : ∀ {N : Y.Modules} (a : (Scheme.Modules.pullback g).obj M ⟶ N),
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforward g).map a) ≫
          (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app N = a := fun a => by
    simp
  erw [← Functor.map_comp_assoc, h]
  simp only [CochainComplex.single₀_map_f_zero]
  exact key _

end Adjunct

section Affine

variable {X X' : Scheme.{u}} {R T : CommRingCat.{u}} (φ : R ⟶ T) (f : X ⟶ Spec R)
  (f' : X' ⟶ Spec T) (p : X' ⟶ X) (w : p ≫ f = f' ≫ Spec.map φ)

/-- The components of the scalar Čech sections map of the pullback unit are the scalar
sections maps of the components of `cechPullback`. -/
lemma scalarCechSectionsMap_unit_f [IsAffineHom p] (𝒰 : X.OrderedAffineCover)
    (M : X.Modules) (q : ℕ) :
    (scalarCechSectionsMap φ f f' p w
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) 𝒰).f q =
      scalarSectionsBaseChangeMapOf φ f f' p w ((cechPullback (M := M) p 𝒰).f q) :=
  rfl

/-- **Affine flat base change.** For a quasi-compact separated `f : X ⟶ Spec R`, a
cartesian square `p ≫ f = f' ≫ Spec.map φ` whose pullbacks preserve finite limits, and a
quasi-coherent `M`, the base change transformation of higher direct images is an isomorphism
at `M` in every degree. -/
theorem isIso_higherDirectImageBaseChange_affine (h : IsPullback p f' f (Spec.map φ))
    [QuasiCompact f] [IsSeparated f]
    [PreservesFiniteLimits (Scheme.Modules.pullback (Spec.map φ))]
    [PreservesFiniteLimits (Scheme.Modules.pullback p)]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso ((higherDirectImageBaseChangeNatTrans (Spec.map φ) f f' p h.w n).app M) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsAffineHom p := MorphismProperty.of_isPullback h.flip inferInstance
  have hf' : IsSeparated f' := MorphismProperty.of_isPullback h inferInstance
  let 𝒰 := Scheme.OrderedAffineCover.ofCompactSpace X
  let 𝒰' := inverseImageCover p 𝒰
  let M' := (Scheme.Modules.pullback p).obj M
  let τ := pushforwardBaseChangeNatTrans (Spec.map φ) f f' p h.w
  let ψ := cechPullbackAdjunct p 𝒰 M
  have : QuasiIso (cechAug 𝒰 M) := quasiIso_cechAug 𝒰 M
  have : QuasiIso (cechAug 𝒰' M') := quasiIso_cechAug 𝒰' M'
  let Φ := resolutionBaseChangeMap τ ψ
  have hB₁ := cechTermDirectImage X R f inferInstance 𝒰 M inferInstance
  have hB₂ := cechTermDirectImage X' T f' hf' 𝒰' M' inferInstance
  have hΦ : ∀ q, IsIso (Φ.f q) := by
    intro q
    change IsIso (pushforwardBaseChange (Spec.map φ) f f' p h.w _ ≫
      (Scheme.Modules.pushforward f').map (ψ.f q))
    rw [pushforwardBaseChange_comp_pushforward_map, unit_comp_pushforward_cechPullbackAdjunct_f]
    refine pushforwardBaseChangeOfIso X X' R T φ f f' p h.w _ _ _ (hB₁ q).1 (hB₂ q).1 ?_
    have := isIso_scalarCechSectionsMap_of_isPullback_of_isSeparated p M φ f f' h.w 𝒰 h
    rw [← scalarCechSectionsMap_unit_f]
    infer_instance
  have : IsIso Φ := HomologicalComplex.Hom.isIso_of_components Φ
  exact (resolutionCompatibility.{u, u, u, u, u + 1, u + 1, u + 1, u + 1} _ _ _ _ _ _ _ _ τ M _ _
    (cechAug 𝒰 M) (cechAug 𝒰' M') ψ
    (mapResolutionAugmentation_cechPullbackAdjunct p 𝒰 M) Φ (fun _ => rfl)).2
    (fun q r => (hB₁ q).2 r) (fun q r => (hB₂ q).2 r) inferInstance n

end Affine

end Langlands.AlgebraicGeometry.Modules.FlatBaseChange
