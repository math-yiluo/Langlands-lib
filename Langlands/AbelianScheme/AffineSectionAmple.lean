import Langlands.GroupScheme.TranslationLaws
import Langlands.AbelianScheme.SeparatingLineBundle.RationalPoints
import Langlands.AbelianScheme.FieldTheoremOfTheSquareProof
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof
import Langlands.AlgebraicGeometry.Modules.TensorSectionGenerationLocusProof
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms
import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleReflectionProof
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero

/-! # Ampleness from one affine section generation open on an abelian scheme over a field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.AffineSectionAmple

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.GroupScheme Langlands.GroupScheme.CommonAffine

variable {S : Scheme.{u}} (G : Grp (Over S))

instance (s : Over.mk (𝟙 S) ⟶ G.X) : IsIso (translation G s).left :=
  ((Over.forget _).mapIso (translationIso G s)).isIso_hom

/-- The section of `L ^ (n + n)` obtained from a section of `L ^ n` by the theorem of the
square: its generation open is the intersection of the two translated generation opens. -/
theorem exists_square_section (K : Type u) [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left) (n : ℕ)
    (s : L.powSections n) (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    ∃ σ : L.powSections (n + n), L.sectionOpen σ =
      (translation A.toGrp a).left ⁻¹ᵁ L.sectionOpen s ⊓
        (translation A.toGrp a⁻¹).left ⁻¹ᵁ L.sectionOpen s := by
  let G : Grp (Over (Spec (CommRingCat.of K))) := A.toGrp
  let M : LineBundle A.X.left := ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne _ L n⟩
  obtain ⟨e⟩ := fieldTheoremOfTheSquare K G A.smooth A.proper A.geometricallyConnected M a a⁻¹
  have h1 : (translation G (a * a⁻¹)).left = 𝟙 A.X.left := by
    rw [mul_inv_cancel, translation_one]
    rfl
  have e1 : Nonempty ((Scheme.Modules.pullback (translation G (a * a⁻¹)).left).obj M.obj ≅
      M.obj) := by
    rw [h1]
    exact ⟨(Scheme.Modules.pullbackId A.X.left).app M.obj⟩
  obtain ⟨e1⟩ := e1
  let Ma := (LineBundle.pullback (translation G a).left).obj M
  let Mb := (LineBundle.pullback (translation G a⁻¹).left).obj M
  let τ := tensorSection Ma.obj Mb.obj (pullbackSection (translation G a).left M.obj s)
    (pullbackSection (translation G a⁻¹).left M.obj s)
  have hτ : trivializationOpen (tensorObj Ma.obj Mb.obj) τ =
      (translation G a).left ⁻¹ᵁ L.sectionOpen s ⊓
        (translation G a⁻¹).left ⁻¹ᵁ L.sectionOpen s := by
    refine (tensorSectionGenerationLocus A.X.left Ma Mb _ _).trans ?_
    exact congrArg₂ (· ⊓ ·)
      (lineBundlePullbackSectionOpen _ _ (translation G a).left M s)
      (lineBundlePullbackSectionOpen _ _ (translation G a⁻¹).left M s)
  let f : tensorObj Ma.obj Mb.obj ≅ tensorPow L.obj (n + n) :=
    e.symm ≪≫ (tensorFunctor A.X.left).mapIso (e1.prod (Iso.refl _)) ≪≫
      tensorPowAddIso L.obj n n
  refine ⟨f.hom.app ⊤ τ, ?_⟩
  change trivializationOpen (tensorPow L.obj (n + n)) (f.hom.app ⊤ τ) = _
  rw [trivializationOpen_mapIso, hτ]

/-- Over an algebraically closed field, one section of a positive power with nonempty affine
generation open makes a line bundle on an abelian scheme ample. -/
theorem isAmple_of_isAlgClosed (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left) (n : ℕ)
    (hn : 1 ≤ n) (s : L.powSections n) (hne : (L.sectionOpen s : Set A.X.left).Nonempty)
    (haff : IsAffineOpen (L.sectionOpen s)) : L.IsAmple := by
  let G : Grp (Over (Spec (CommRingCat.of K))) := A.toGrp
  have : IrreducibleSpace A.X.left :=
    SeparatingLineBundle.irreducibleSpace_of_smooth_of_isProper G
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  have : A.X.left.IsSeparated := ⟨by rw [← terminal.comp_from A.X.hom]; infer_instance⟩
  let U := L.sectionOpen s
  let W : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) → A.X.left.Opens := fun a ↦
    (translation G a).left ⁻¹ᵁ U ⊓ (translation G a⁻¹).left ⁻¹ᵁ U
  have hclosed : ∀ z : A.X.left, IsClosed ({z} : Set A.X.left) → ∃ a, z ∈ W a := by
    intro z hz
    let c : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
    let z' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X :=
      Over.homMk (pointOfClosedPoint A.X.hom z hz) (pointOfClosedPoint_comp A.X.hom z hz)
    have hz' : z'.left c = z := pointOfClosedPoint_apply A.X.hom z hz c
    let V₁ : A.X.left.Opens := (translation G z').left ⁻¹ᵁ U
    let V₂ : A.X.left.Opens := (ι[G.X]).left ⁻¹ᵁ V₁
    have hV₁ : (V₁ : Set A.X.left).Nonempty := by
      obtain ⟨y, hy⟩ := hne
      obtain ⟨w, hw⟩ := (Scheme.homeoOfIso
        ((Over.forget _).mapIso (translationIso G z'))).surjective y
      refine ⟨w, ?_⟩
      change (translation G z').left w ∈ U
      change (translation G z').left w = y at hw
      rwa [hw]
    have hV₂ : (V₂ : Set A.X.left).Nonempty := by
      obtain ⟨y, hy⟩ := hV₁
      refine ⟨(ι[G.X]).left y, ?_⟩
      change (ι[G.X]).left ((ι[G.X]).left y) ∈ V₁
      have h := congr(($(GrpObj.inv_comp_inv G.X)).left y)
      rw [Over.comp_left, Over.id_left] at h
      change (ι[G.X]).left ((ι[G.X]).left y) = y at h
      rwa [h]
    obtain ⟨a, ha, haV⟩ := SeparatingLineBundle.exists_rationalPoint_mem_of_isOpen
      A.X.hom (fun b : Bool ↦ if b then (V₁ : Set A.X.left) else (V₂ : Set A.X.left))
      (fun b ↦ by cases b <;> exact TopologicalSpace.Opens.isOpen _)
      (fun b ↦ by cases b; exacts [hV₂, hV₁])
    let a' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X := Over.homMk a ha
    refine ⟨a', ?_, ?_⟩
    · change (translation G a').left z ∈ U
      rw [← hz', translation_apply_section G a' z']
      exact haV true
    · change (translation G a'⁻¹).left z ∈ U
      rw [← hz', translation_apply_section G a'⁻¹ z']
      have h2 := haV false
      exact h2
  have hcover : ∀ x : A.X.left, ∃ a, x ∈ W a := by
    by_contra hcon
    push Not at hcon
    let Z : Set A.X.left := (⋃ a, (W a : Set A.X.left))ᶜ
    have hZ : IsClosed Z := (isOpen_iUnion fun a ↦ (W a).isOpen).isClosed_compl
    obtain ⟨x, hx⟩ : Z.Nonempty := by
      obtain ⟨x, hx⟩ := hcon
      exact ⟨x, by simpa [Z] using hx⟩
    obtain ⟨z, hzZ, hzc⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ hZ.isLocallyClosed
    obtain ⟨a, ha⟩ := hclosed z hzc
    exact hzZ (Set.mem_iUnion.mpr ⟨a, ha⟩)
  refine ⟨inferInstance, fun x ↦ ?_⟩
  obtain ⟨a, ha⟩ := hcover x
  obtain ⟨σ, hσ⟩ := exists_square_section K A L n s a
  refine ⟨n + n, by omega, σ, ?_, ?_⟩
  · rw [hσ]
    exact ha
  · rw [hσ]
    exact (haff.preimage_of_isIso _).inf (haff.preimage_of_isIso _)

set_option backward.isDefEq.respectTransparency.types false in
/-- Over an arbitrary field, one section of a positive power with nonempty affine generation
open makes a line bundle on an abelian scheme ample. -/
theorem isAmple_of_isAffineOpen_sectionOpen (K : Type u) [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left) (n : ℕ)
    (hn : 1 ≤ n) (s : L.powSections n) (hne : (L.sectionOpen s : Set A.X.left).Nonempty)
    (haff : IsAffineOpen (L.sectionOpen s)) : L.IsAmple := by
  let K' := AlgebraicClosure K
  let b : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K K'))
  apply fieldBaseChangeAmpleReflection K K' b A.X.left A.X.hom L
  have : Surjective b := ⟨fun x ↦ ⟨IsLocalRing.closedPoint K', Subsingleton.elim _ _⟩⟩
  let A' := (AbelianScheme.baseChange b).obj A
  let p : A'.X.left ⟶ A.X.left := pullback.fst A.X.hom b
  have : IsAffineHom b := isAffineHom_of_isAffine b
  have : IsAffineHom p := MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom b)
  have : Surjective p := MorphismProperty.pullback_fst _ _ (inferInstance : Surjective b)
  let L' : LineBundle A'.X.left := (LineBundle.pullback p).obj L
  have hopen : L'.sectionOpen (L.pullbackPowSection p s) = p ⁻¹ᵁ L.sectionOpen s :=
    LineBundle.sectionOpen_pullbackPowSection p L s
  refine isAmple_of_isAlgClosed K' A' L' n hn (L.pullbackPowSection p s) ?_ ?_
  · rw [hopen]
    obtain ⟨y, hy⟩ := hne
    obtain ⟨w, hw⟩ := p.surjective y
    exact ⟨w, by change p w ∈ L.sectionOpen s; rwa [hw]⟩
  · rw [hopen]
    exact haff.preimage p

end Langlands.AbelianScheme.AffineSectionAmple
