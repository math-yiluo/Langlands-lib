import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleSupport
import Langlands.Sheaf.CompactExtensionUniverseLift

/-! # Compact sections across the actual ordinary universe lift -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v uL w

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation

/-- Native stalk support is equivalently detected by nonvanishing on every
ordinary open neighborhood. -/
theorem not_mem_nativeSupport_iff {Y : TopCat.{w}} {S : Type w} [CommRing S]
    (F : TopCat.Sheaf (ModuleCat.{w} S) Y)
    (s : F.obj.obj (op ⊤)) (y : Y) :
    y ∉ Langlands.Sheaf.CompactSupport.support F.obj s ↔
      ∃ U : Opens Y, y ∈ U ∧ F.obj.map (homOfLE le_top : U ⟶ ⊤).op s = 0 := by
  constructor
  · intro hy
    have hz : F.presheaf.Γgerm y s = 0 := not_not.mp hy
    obtain ⟨U, hyU, i, j, hU⟩ := F.presheaf.germ_eq y
      (U := ⊤) (V := ⊤) trivial trivial s 0
        (by simpa only [TopCat.Presheaf.Γgerm, map_zero] using hz)
    exact ⟨U, hyU, by
      simpa only [show i = (homOfLE le_top : U ⟶ ⊤) from Subsingleton.elim _ _,
        map_zero] using hU⟩
  · rintro ⟨U, hyU, hz⟩ hy
    apply hy
    change F.presheaf.Γgerm y s = 0
    rw [← F.presheaf.Γgerm_res_apply (U := U) y hyU s (i := homOfLE le_top),
      hz, map_zero]

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Actual ordinary module sheaves before and after canonical universe lift. -/
def underlyingTopologyLiftEquivalence :
    TopCat.Sheaf (ModuleCat.{max u (v + 1) uL} R) (localizedSpaceFunctor.obj X) ≌
      TopCat.Sheaf (ModuleCat.{max u (v + 1) uL} R)
        (TopCat.of (ULift.{max u (v + 1) uL} (localizedSpaceFunctor.obj X))) :=
  Langlands.Sheaf.HomeomorphTransport.equivalence
    (Homeomorph.ulift.{max u (v + 1) uL, v}
      (X := localizedSpaceFunctor.obj X)).symm (ModuleCat.{max u (v + 1) uL} R)

/-- The literal lifted global section has support equal to the preimage of the
original standard ordinary point support. -/
theorem support_underlyingTopologyLift
    (F : TopCat.Sheaf (ModuleCat.{max u (v + 1) uL} R) (localizedSpaceFunctor.obj X))
    (s : F.obj.obj (op ⊤)) :
    Langlands.Sheaf.CompactSupport.support
        (((underlyingTopologyLiftEquivalence.{u, v, uL} X R).functor.obj F).obj) s =
      ULift.down ⁻¹' Langlands.Sheaf.PointSupport.support
        (underlyingTopologyPoint.{u, v, uL} X) F.obj s := by
  let e : ULift.{max u (v + 1) uL} (localizedSpaceFunctor.obj X) ≃ₜ
      localizedSpaceFunctor.obj X := Homeomorph.ulift
  let a := Langlands.Sheaf.HomeomorphTransport.opensEquivalence e.symm
  let T := (underlyingTopologyLiftEquivalence.{u, v, uL} X R).functor.obj F
  ext y
  apply not_iff_not.mp
  change y ∉ Langlands.Sheaf.CompactSupport.support T.obj s ↔
    y.down ∉ Langlands.Sheaf.PointSupport.support
      (underlyingTopologyPoint.{u, v, uL} X) F.obj s
  rw [not_mem_nativeSupport_iff,
    not_mem_support_underlyingTopologyPoint_iff.{u, v, uL}]
  constructor
  · rintro ⟨U, hyU, hz⟩
    exact ⟨a.inverse.obj U, hyU, hz⟩
  · rintro ⟨U, hyU, hz⟩
    exact ⟨a.functor.obj U, hyU, hz⟩

/-- Compact support is preserved and reflected by actual universe transport. -/
theorem isCompact_support_underlyingTopologyLift_iff
    (F : TopCat.Sheaf (ModuleCat.{max u (v + 1) uL} R) (localizedSpaceFunctor.obj X))
    (s : F.obj.obj (op ⊤)) :
    IsCompact (Langlands.Sheaf.CompactSupport.support
      (((underlyingTopologyLiftEquivalence.{u, v, uL} X R).functor.obj F).obj) s) ↔
      Langlands.Sheaf.PointSupport.IsCompactlySupported
        (underlyingTopologyPoint.{u, v, uL} X) F.obj s := by
  have hc := Langlands.Sheaf.CompactSupport.isClosed_support
    (((underlyingTopologyLiftEquivalence.{u, v, uL} X R).functor.obj F).obj) s
  rw [support_underlyingTopologyLift.{u, v, uL}] at hc
  rw [support_underlyingTopologyLift.{u, v, uL}]
  constructor
  · intro hs
    exact ⟨_, (Homeomorph.ulift.{max u (v + 1) uL, v}
      (X := localizedSpaceFunctor.obj X)).isCompact_preimage.1 hs, subset_rfl⟩
  · rintro ⟨C, hC, hsC⟩
    exact ((Homeomorph.ulift.{max u (v + 1) uL, v}
      (X := localizedSpaceFunctor.obj X)).isCompact_preimage.2 hC).of_isClosed_subset
        hc (fun _ hx => hsC hx)

/-- The actual independent-universe compact sections identify with native
compact sections on the canonically lifted ordinary sheaf. -/
def underlyingTopologyLiftCompactIso :
    underlyingTopologyCompactSections.{u, v, uL} (X := X) (R := R) ≅
      (underlyingTopologyLiftEquivalence.{u, v, uL} X R).functor ⋙
        Langlands.Sheaf.CompactSupport.functor
          (X := TopCat.of (ULift.{max u (v + 1) uL} (localizedSpaceFunctor.obj X))) (R := R) :=
  NatIso.ofComponents (fun F =>
    (show (Langlands.Sheaf.PointSupport.compactSubmodule
        (underlyingTopologyPoint.{u, v, uL} X) R F.obj (⊤ : Opens (localizedSpaceFunctor.obj X))) ≃ₗ[R]
      Langlands.Sheaf.CompactSupport.submodule
        (((underlyingTopologyLiftEquivalence.{u, v, uL} X R).functor.obj F).obj) from
      { toFun := fun s => ⟨s.val,
          (isCompact_support_underlyingTopologyLift_iff.{u, v, uL} X R F s.val).2 s.property⟩
        invFun := fun s => ⟨s.val,
          (isCompact_support_underlyingTopologyLift_iff.{u, v, uL} X R F s.val).1 s.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }).toModuleIso) (by
    intro F G f
    ext s
    rfl)

end Langlands.Sheaf.Equivariant.Analytic
