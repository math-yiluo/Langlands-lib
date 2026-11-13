import Langlands.AlgebraicGeometry.Picard.DvrUniformizerDivision
import Langlands.AlgebraicGeometry.Modules.QuasiAffineLineBundleSectionBasis
import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof

/-! # Dividing line-bundle sections by a uniformizer over a DVR -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry

open Langlands.SchemeModule Langlands.SchemeModule.SectionClearing
open Langlands.SchemeModule.QuasiAffineSectionBasis
open Langlands.AlgebraicGeometry.ProjectiveBundle

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (A : Langlands.AbelianScheme (Spec (CommRingCat.of R)))

/-- `chartE` is injective. -/
theorem chartE_injective {X : Scheme.{u}} {M : X.Modules} {T : X.Opens}
    (e : M.restrict T.ι ≅ SheafOfModules.unit T.toScheme.ringCatSheaf) (W : X.Opens)
    (hW : W ≤ T) : Function.Injective (chartE e W hW) :=
  Function.LeftInverse.injective (chartF_chartE e W hW)

/-- `chartE` sends zero to zero. -/
theorem chartE_zero {X : Scheme.{u}} {M : X.Modules} {T : X.Opens}
    (e : M.restrict T.ι ≅ SheafOfModules.unit T.toScheme.ringCatSheaf) (W : X.Opens)
    (hW : W ≤ T) : chartE e W hW 0 = 0 := by
  have h := chartE_smul e W hW 0 0
  rwa [zero_smul, zero_mul] at h

/-- The basic open of the chart coordinate of a global section lies in its generation open. -/
theorem basicOpen_chartE_le {X : Scheme.{u}} (L : LineBundle X) {T : X.Opens}
    (e : L.obj.restrict T.ι ≅ SheafOfModules.unit T.toScheme.ringCatSheaf)
    (s : GlobalSections L.obj) :
    X.basicOpen (chartE e T le_rfl (sectionRes L.obj s T)) ≤ trivializationOpen L.obj s := by
  let h := chartE e T le_rfl (sectionRes L.obj s T)
  have hU : X.basicOpen h ≤ T := X.basicOpen_le h
  apply le_trivializationOpen_of_chart_unit L e hU s
  have hres := chartE_res e T (X.basicOpen h) le_rfl hU (sectionRes L.obj s T)
  rw [sectionRes_res] at hres
  rw [hres]
  exact X.toRingedSpace.isUnit_res_basicOpen h

/-- A global section of a line bundle that generates at no point of the special fibre is
divisible by the uniformizer. -/
theorem exists_eq_unifX_smul {π : R} (hπ : Irreducible π) (L : LineBundle A.X.left)
    (s : GlobalSections L.obj)
    (hs : ∀ x : A.X.left, A.X.hom x = IsLocalRing.closedPoint R →
      x ∉ trivializationOpen L.obj s) :
    ∃ s₁ : GlobalSections L.obj, s = unifX A π • s₁ := by
  choose T hxT he using L.property
  let e (x : A.X.left) : L.obj.restrict (T x).ι ≅
      Langlands.Scheme.Modules.structureSheaf (T x).toScheme := (he x).some
  have hloc : ∀ x : A.X.left, ∃ b : Γ(A.X.left, T x),
      chartE (e x) (T x) le_rfl (sectionRes L.obj s (T x)) = unifRes A π (T x) * b :=
    fun x ↦ by
      apply exists_eq_unifRes_mul A hπ
      intro y _ hys hyb
      exact hs y hys (basicOpen_chartE_le L (e x) s hyb)
  choose b hb using hloc
  let σ : ∀ x : A.X.left, Γ(L.obj, T x) := fun x ↦ chartF (e x) (T x) le_rfl (b x)
  have hσ : ∀ x, unifRes A π (T x) • σ x = sectionRes L.obj s (T x) := fun x ↦ by
    apply chartE_injective (e x) (T x) le_rfl
    rw [chartE_smul, chartE_chartF, hb x]
  have key : ∀ x y : A.X.left,
      L.obj.presheaf.map (homOfLE (inf_le_left : T x ⊓ T y ≤ T x)).op (σ x) =
        L.obj.presheaf.map (homOfLE (inf_le_right : T x ⊓ T y ≤ T y)).op (σ y) := by
    intro x y
    have hW : T x ⊓ T y ≤ T x := inf_le_left
    let d := L.obj.presheaf.map (homOfLE (inf_le_left : T x ⊓ T y ≤ T x)).op (σ x) -
      L.obj.presheaf.map (homOfLE (inf_le_right : T x ⊓ T y ≤ T y)).op (σ y)
    have hd : unifRes A π (T x ⊓ T y) • d = 0 := by
      have t1 : unifRes A π (T x ⊓ T y) •
          L.obj.presheaf.map (homOfLE (inf_le_left : T x ⊓ T y ≤ T x)).op (σ x) =
          sectionRes L.obj s (T x ⊓ T y) := by
        rw [← res_unifRes A π (inf_le_left : T x ⊓ T y ≤ T x), ← Scheme.Modules.map_smul,
          hσ x, sectionRes_res]
      have t2 : unifRes A π (T x ⊓ T y) •
          L.obj.presheaf.map (homOfLE (inf_le_right : T x ⊓ T y ≤ T y)).op (σ y) =
          sectionRes L.obj s (T x ⊓ T y) := by
        rw [← res_unifRes A π (inf_le_right : T x ⊓ T y ≤ T y), ← Scheme.Modules.map_smul,
          hσ y, sectionRes_res]
      change unifRes A π (T x ⊓ T y) • (_ - _) = 0
      rw [smul_sub, t1, t2, sub_self]
    have h1 : unifRes A π (T x ⊓ T y) * chartE (e x) (T x ⊓ T y) hW d = 0 := by
      rw [← chartE_smul, hd, chartE_zero]
    have h2 : chartE (e x) (T x ⊓ T y) hW d = 0 := eq_zero_of_unifRes_mul_eq_zero A hπ _ h1
    have h3 : d = 0 := chartE_injective (e x) _ hW (h2.trans (chartE_zero _ _ _).symm)
    exact sub_eq_zero.mp h3
  let F : TopCat.Sheaf Ab A.X.left := ⟨L.obj.presheaf, L.obj.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.1 T σ := key
  have hcover : (⊤ : A.X.left.Opens) ≤ iSup T := fun y _ ↦ Opens.mem_iSup.mpr ⟨y, hxT y⟩
  obtain ⟨s₁, hs₁, -⟩ := F.existsUnique_gluing' T ⊤ (fun x ↦ homOfLE le_top) hcover σ hcompat
  let g : GlobalSections L.obj := s₁
  have hg : ∀ x, sectionRes L.obj g (T x) = σ x := hs₁
  refine ⟨g, ?_⟩
  have hl : ∀ x, sectionRes L.obj s (T x) = sectionRes L.obj (unifX A π • g) (T x) := by
    intro x
    have hsm : sectionRes L.obj (unifX A π • g) (T x) =
        unifRes A π (T x) • sectionRes L.obj g (T x) :=
      Scheme.Modules.map_smul L.obj (homOfLE (le_top : T x ≤ ⊤)) (unifX A π) g
    rw [hsm, hg x, hσ x]
  exact F.eq_of_locally_eq' T ⊤ (fun x ↦ homOfLE le_top) hcover s (unifX A π • g) hl

/-- Every point specializes to a point of the special fibre. -/
theorem exists_specializes_closedPoint (y : A.X.left) :
    ∃ x : A.X.left, y ⤳ x ∧ A.X.hom x = IsLocalRing.closedPoint R := by
  have hZ : IsClosed (A.X.hom '' closure {y}) :=
    A.X.hom.isClosedMap _ isClosed_closure
  have hmem : IsLocalRing.closedPoint R ∈ A.X.hom '' closure {y} :=
    (IsLocalRing.specializes_closedPoint (A.X.hom y)).mem_closed hZ
      (Set.mem_image_of_mem _ (subset_closure rfl))
  obtain ⟨x, hx, hfx⟩ := hmem
  exact ⟨x, specializes_iff_mem_closure.mpr hx, hfx⟩

/-- Krull intersection for line-bundle sections: a section with nonempty generation open is
not divisible by every power of the uniformizer. -/
theorem not_forall_unifX_pow_smul {π : R} (hπ : Irreducible π) (L : LineBundle A.X.left)
    (s : GlobalSections L.obj) (hne : (trivializationOpen L.obj s : Set A.X.left).Nonempty) :
    ¬ ∀ j : ℕ, ∃ sj : GlobalSections L.obj, s = unifX A π ^ j • sj := by
  intro hdiv
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, hyx, hxs⟩ := exists_specializes_closedPoint A y
  obtain ⟨T, hxT, ⟨e₀⟩⟩ := L.property x
  let e : L.obj.restrict T.ι ≅ Langlands.Scheme.Modules.structureSheaf T.toScheme := e₀
  have hyT : y ∈ T := hyx.mem_open T.isOpen hxT
  let h := chartE e T le_rfl (sectionRes L.obj s T)
  have hdiv' : ∀ j : ℕ, ∃ hj : Γ(A.X.left, T), h = unifRes A π T ^ j * hj := by
    intro j
    obtain ⟨sj, hsj⟩ := hdiv j
    refine ⟨chartE e T le_rfl (sectionRes L.obj sj T), ?_⟩
    have hsm : sectionRes L.obj (unifX A π ^ j • sj) T =
        unifRes A π T ^ j • sectionRes L.obj sj T := by
      rw [sectionRes, Scheme.Modules.map_smul, map_pow]
    change chartE e T le_rfl (sectionRes L.obj s T) = _
    rw [hsj, hsm, chartE_smul]
  have h0 : h = 0 := eq_zero_of_forall_unifRes_pow_dvd A hπ h hxT hxs hdiv'
  have hres0 : sectionRes L.obj s T = 0 :=
    chartE_injective e T le_rfl (h0.trans (chartE_zero e T le_rfl).symm)
  have hpb : pullbackSection T.ι L.obj s = 0 := by
    rw [← openSection_restriction L.obj T s]
    change openSection L.obj T (sectionRes L.obj s T) = 0
    rw [hres0, map_zero]
  have hopen := lineBundlePullbackSectionOpen A.X.left T.toScheme T.ι L s
  rw [hpb] at hopen
  have hbot := trivializationOpen_zero ((LineBundle.pullback T.ι).obj L)
  have hmem : (⟨y, hyT⟩ : T.toScheme) ∈ T.ι ⁻¹ᵁ trivializationOpen L.obj s := hy
  rw [← hopen] at hmem
  change (⟨y, hyT⟩ : T.toScheme) ∈
    trivializationOpen ((LineBundle.pullback T.ι).obj L).obj 0 at hmem
  rw [hbot] at hmem
  exact hmem

end Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry
