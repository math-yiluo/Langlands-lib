import Langlands.AlgebraicGeometry.Modules.FlatSupportedSectionCoefficients
import Langlands.AlgebraicGeometry.Picard.SupportedPullbackPowerSections
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Reflection of ampleness under flat surjective affine base change -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.FlatAmpleReflection

/-- An ample pullback along an affine surjection supplies compactness and
quasi-separatedness of the original scheme. -/
lemma compactSpace_and_quasiSeparatedSpace {X Y : Scheme.{u}}
    (g : Y ⟶ X) [IsAffineHom g] [Surjective g] (L : LineBundle X)
    (hL : ((LineBundle.pullback g).obj L).IsAmple) :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  let : CompactSpace Y := hL.compactSpace
  let : QuasiSeparatedSpace Y := hL.quasiSeparatedSpace
  exact ⟨g.surjective.compactSpace g.continuous,
    FieldAmpleReflection.quasiSeparatedSpace_of_surjective g⟩

/-- The canonical scalar sections isomorphism when one specified line bundle
becomes ample along an affine surjection in a flat affine-base square. -/
def sectionsIsoOfAmplePullback {X Y : Scheme.{u}} {R A : CommRingCat.{u}}
    (φ : R ⟶ A) (f : X ⟶ Spec R) (f' : Y ⟶ Spec A) (g : Y ⟶ X)
    [IsAffineHom g] [Surjective g] (h : IsPullback g f' f (Spec.map φ))
    (hφ : φ.hom.Flat) (L : LineBundle X)
    (hL : ((LineBundle.pullback g).obj L).IsAmple) (M : LineBundle X) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeGlobalSections f).obj M.obj) ≅
      (relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj M.obj) := by
  have htop := compactSpace_and_quasiSeparatedSpace g L hL
  let : CompactSpace X := htop.1
  let : QuasiSeparatedSpace X := htop.2
  exact Modules.CechResolution.scalarSectionsBaseChangeIso_lineBundle_qcqs
    φ f f' g h.w M h hφ

/-- A section of an actual pulled-back positive tensor power can be chosen to
generate above a point and vanish on the base change of a closed complement. -/
lemma exists_vanishing_upstairs_section {X Y : Scheme.{u}} (g : Y ⟶ X)
    [Surjective g] (L : LineBundle X)
    (hL : ((LineBundle.pullback g).obj L).IsAmple)
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ y : Y, g y = x ∧ ∃ r : ℕ, 1 ≤ r ∧
      ∃ t : GlobalSections ((Scheme.Modules.pullback g).obj (tensorPow L.obj r)),
        y ∈ trivializationOpen
            ((Scheme.Modules.pullback g).obj (tensorPow L.obj r)) t ∧
          pullbackSection (pullback.snd (closedComplementι U) g)
            ((Scheme.Modules.pullback g).obj (tensorPow L.obj r)) t = 0 := by
  let i := closedComplementι U
  let i' := pullback.snd i g
  let : CompactSpace Y := hL.compactSpace
  let : CompactSpace (pullback i g : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace i'
  obtain ⟨y, hy⟩ := g.surjective x
  have hyU : y ∈ g ⁻¹ᵁ U := by
    change g y ∈ U
    rwa [hy]
  obtain ⟨n, hn, s, hys, hsU⟩ :=
    ampleSectionOpenBasis_apply Y ((LineBundle.pullback g).obj L) hL (g ⁻¹ᵁ U) y hyU
  have hs : i' ⁻¹ᵁ ((LineBundle.pullback g).obj L).sectionOpen s = ⊥ := by
    apply bot_unique
    intro z hz
    have hzi : i (pullback.fst i g z) ∈ (U : Set X)ᶜ := by
      rw [← range_closedComplementι U]
      exact ⟨_, rfl⟩
    have hcomm : i (pullback.fst i g z) = g (i' z) :=
      congrArg (fun k => k z) (pullback.condition (f := i) (g := g))
    exact (hzi (hcomm ▸ hsU hz)).elim
  obtain ⟨r, hr, t, ht, hz⟩ :=
    FieldAmpleReflection.exists_vanishing_pullback_powerSection g i' L hn s hs
  exact ⟨y, hy, r, hr, t, ht.symm ▸ hys, hz⟩

/-- Flat scalar extension reflects ampleness in a Cartesian affine-base square
whose scheme projection is affine and surjective. -/
theorem isAmple_of_flat_square {X Y : Scheme.{u}} {R A : CommRingCat.{u}}
    (φ : R ⟶ A) (f : X ⟶ Spec R) (f' : Y ⟶ Spec A) (g : Y ⟶ X)
    [IsAffineHom g] [Surjective g] (h : IsPullback g f' f (Spec.map φ))
    (hφ : φ.hom.Flat) (L : LineBundle X)
    (hL : ((LineBundle.pullback g).obj L).IsAmple) : L.IsAmple := by
  have htop := compactSpace_and_quasiSeparatedSpace g L hL
  let : CompactSpace X := htop.1
  let : QuasiSeparatedSpace X := htop.2
  refine ⟨htop.1, fun x => ?_⟩
  obtain ⟨U, hU, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨y, hy, r, hr, t, hyt, htz⟩ :=
    exists_vanishing_upstairs_section g L hL U x hx
  let M : LineBundle X :=
    ⟨tensorPow L.obj r, tensorPow_isLocallyFreeRankOne X L r⟩
  let i := closedComplementι U
  let i' := pullback.snd i g
  let gZ := pullback.fst i g
  let sq : gZ ≫ i = i' ≫ g := pullback.condition
  let : IsIso (scalarSectionsBaseChangeMap φ f f' g h.w M.obj) := by
    change IsIso (sectionsIsoOfAmplePullback φ f f' g h hφ L hL M).hom
    infer_instance
  let : CompactSpace (closedComplement U) := inferInstance
  let : QuasiSeparatedSpace (closedComplement U) :=
    quasiSeparatedSpace_of_quasiSeparated i
  let : IsAffineHom gZ :=
    MorphismProperty.pullback_fst i g (inferInstance : IsAffineHom g)
  have hZ : IsPullback gZ (i' ≫ f') (i ≫ f) (Spec.map φ) :=
    (IsPullback.of_hasPullback i g).paste_vert h
  let : IsIso (scalarSectionsBaseChangeMap φ (i ≫ f) (i' ≫ f') gZ
      (square_restrict_comm φ f f' g h.w i i' gZ sq)
      ((Scheme.Modules.pullback i).obj M.obj)) :=
    Modules.CechResolution.isIso_scalarSectionsBaseChangeMap_lineBundle_qcqs
      φ (i ≫ f) (i' ≫ f') gZ
      (square_restrict_comm φ f f' g h.w i i' gZ sq)
      ((LineBundle.pullback i).obj M) hZ hφ
  obtain ⟨s, hsz, hxs⟩ :=
    Modules.DerivedSections.FlatBaseChange.exists_vanishing_coefficient_generating
      φ hφ f f' g h.w i i' gZ sq M t htz y hyt
  have hle : L.sectionOpen s ≤ U :=
    trivializationOpen_le_of_closedComplement_vanishing U M s hsz
  refine ⟨r, hr, s, ?_, FieldAmpleReflection.isAffineOpen_sectionOpen_of_le L s U hU hle⟩
  change x ∈ trivializationOpen M.obj s
  rwa [hy] at hxs

end Langlands.AlgebraicGeometry.Picard.FlatAmpleReflection

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

/-- Ampleness of a specified line bundle descends along a flat surjective base
change between arbitrary affine schemes. -/
theorem isAmple_of_affine_flat_surjective_baseChange
    {S T X Y : Scheme.{u}} [IsAffine S] [IsAffine T]
    (b : T ⟶ S) [Flat b] [Surjective b]
    (f : X ⟶ S) (f' : Y ⟶ T) (g : Y ⟶ X)
    (h : IsPullback g f' f b) (L : LineBundle X)
    (hL : ((LineBundle.pullback g).obj L).IsAmple) : L.IsAmple := by
  let : IsAffineHom b := inferInstance
  let : IsAffineHom g := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip
    (inferInstance : IsAffineHom b)
  let : Surjective g := MorphismProperty.of_isPullback (P := @Surjective) h.flip
    (inferInstance : Surjective b)
  have hΓ : IsPullback g (f' ≫ T.isoSpec.hom) (f ≫ S.isoSpec.hom)
      (Spec.map b.appTop) := by
    apply h.of_iso (Iso.refl _) (Iso.refl _) T.isoSpec S.isoSpec
    · simp
    · simp
    · simp
    · exact (Scheme.isoSpec_hom_naturality b).symm
  exact FlatAmpleReflection.isAmple_of_flat_square b.appTop
    (f ≫ S.isoSpec.hom) (f' ≫ T.isoSpec.hom) g hΓ b.flat_appTop L hL

end Langlands.AlgebraicGeometry.Picard.LineBundle
