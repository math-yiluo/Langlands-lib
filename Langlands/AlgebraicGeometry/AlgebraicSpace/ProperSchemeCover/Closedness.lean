import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.Construction
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Closedness of the cover over the chart

For the weak Chow data `D`, the fibre product `Q = U ×_X W` of the cover `φ : h_U → X` and the
chart `π : h_W → X` maps to `Z ×_S W` by a closed immersion. Its image is the union of the loci
where the `i`-th projection `Z ⟶ Y` agrees with the immersion `W ⟶ Y`. Hence the projection
`Q ⟶ W` is proper.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover

namespace ChowData

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (D : ChowData X)

/-- The fibre product `U ×_X W` of the cover and the chart. -/
abbrev Q : Over S := spacePullback D.φ D.π

/-- The projection `U ×_X W ⟶ U`. -/
abbrev q₁ : D.Q ⟶ D.U := spacePullbackFst D.φ D.π

/-- The projection `U ×_X W ⟶ W`. -/
abbrev q₂ : D.Q ⟶ D.W := spacePullbackSnd D.φ D.π

/-- The map `U ×_X W ⟶ Z ×_S W`. -/
def m : D.Q ⟶ D.Z ⊗ D.W := lift (D.q₁ ≫ openOverι D.Z D.X') D.q₂

theorem m_eq : D.m = lift D.q₁ D.q₂ ≫ (openOverι D.Z D.X' ▷ D.W) := by
  rw [lift_whiskerRight, m]

theorem q₂_eq : D.q₂ = D.m ≫ snd D.Z D.W := by
  rw [m, lift_snd]

instance : Etale D.q₁.left := etale_spacePullbackFst D.φ D.π D.etale

instance : IsPreimmersion D.m.left := by
  rw [m_eq, Over.comp_left]
  have := isClosedImmersion_spacePullbackLift D.φ D.π D.separated
  have : _root_.AlgebraicGeometry.IsOpenImmersion (openOverι D.Z D.X' ▷ D.W).left := by
    rw [Over.whiskerRight_left]; infer_instance
  infer_instance

/-- The locus of `Z ×_S W` where the `i`-th projection `Z ⟶ Y` agrees with the immersion
`W ⟶ Y`. -/
def Γ (i : Fin (D.n + 1)) : Set (D.Z ⊗ D.W).left :=
  {x | EqAt (fst D.Z D.W ≫ D.ζ ≫ D.p i).left (snd D.Z D.W ≫ D.ι ≫ D.o).left x}

theorem isClosed_Γ (i : Fin (D.n + 1)) : IsClosed (D.Γ i) :=
  isClosed_setOf_eqAt _ _

theorem Γ_subset_range (i : Fin (D.n + 1)) : D.Γ i ⊆ Set.range D.m.left := by
  intro x hx
  let T : Over S := Over.mk ((D.Z ⊗ D.W).left.fromSpecResidueField x ≫ (D.Z ⊗ D.W).hom)
  let h : T ⟶ D.Z ⊗ D.W := Over.homMk ((D.Z ⊗ D.W).left.fromSpecResidueField x)
  have hh : h ≫ fst D.Z D.W ≫ D.ζ ≫ D.p i = h ≫ snd D.Z D.W ≫ D.ι ≫ D.o :=
    Over.OverMorphism.ext hx
  obtain ⟨g, hg⟩ := exists_lift_openImmersion (openOverι D.Z (D.opens i)) (h ≫ fst D.Z D.W) (by
    rintro _ ⟨y, rfl⟩
    change _ ∈ Set.range (D.opens i).ι
    rw [Scheme.Opens.range_ι]
    change (D.ζ ≫ D.p i).left ((h ≫ fst D.Z D.W).left y) ∈ D.o.left.opensRange
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc, hh]
    exact ⟨_, rfl⟩)
  have hgw : g ≫ D.fac i = h ≫ snd D.Z D.W := by
    apply D.comp_fac_eq
    rw [reassoc_of% hg, hh, Category.assoc]
  let u : T ⟶ D.U := g ≫ openOverHomOfLE D.Z (le_iSup D.opens i)
  have hu : (schemeYoneda S).map u ≫ D.φ = (schemeYoneda S).map (h ≫ snd D.Z D.W) ≫ D.π := by
    rw [Functor.map_comp_assoc, D.φ_spec, ← Functor.map_comp_assoc, hgw]
  have hl : spacePullbackLift u _ hu ≫ D.m = h := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [m, Category.assoc, lift_fst, spacePullbackLift_fst_assoc, Category.assoc,
        openOverHomOfLE_ι, hg]
    · rw [m, Category.assoc, lift_snd, spacePullbackLift_snd]
  refine ⟨(spacePullbackLift u _ hu).left
    (show T.left from IsLocalRing.closedPoint ((D.Z ⊗ D.W).left.residueField x)), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hl]
  exact Scheme.fromSpecResidueField_apply _ _

/-- The image of the complete locus is dense in `U`. -/
theorem dense_εU_image : Dense (D.εU.left '' (D.gbar.left ⁻¹' D.G)) := by
  have h1 : ∀ z, D.εbar.left z = D.X'.ι (D.εU.left z) := fun z => by
    rw [← D.εU_ι, Over.comp_left, Scheme.Hom.comp_apply]
    rfl
  have h2 : D.εbar.left '' (D.gbar.left ⁻¹' D.G) =
      D.X'.ι '' (D.εU.left '' (D.gbar.left ⁻¹' D.G)) := by
    rw [Set.image_image]
    exact Set.image_congr (fun z _ => h1 z)
  have h3 : Dense (D.X'.ι '' (D.εU.left '' (D.gbar.left ⁻¹' D.G))) :=
    D.dense_A.mono (h2 ▸ D.A_subset)
  rw [← Set.preimage_image_eq (D.εU.left '' (D.gbar.left ⁻¹' D.G))
    D.X'.ι.isOpenEmbedding.injective]
  exact h3.preimage D.X'.ι.isOpenEmbedding.isOpenMap

theorem preimage_subset_Γ {y : D.Q.left}
    (hy : y ∈ D.q₁.left ⁻¹' (D.εU.left '' (D.gbar.left ⁻¹' D.G))) :
    D.m.left y ∈ ⋃ i, D.Γ i := by
  obtain ⟨g, hg, hgy⟩ := hy
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := D.q₁.left) (g := D.εU.left) y g hgy.symm
  let R : Over S := Over.mk (pullback.fst D.q₁.left D.εU.left ≫ D.Q.hom)
  let r₁ : R ⟶ D.Q := Over.homMk (pullback.fst _ _)
  let r₂ : R ⟶ D.Gbar := Over.homMk (pullback.snd _ _) (by
    change pullback.snd D.q₁.left D.εU.left ≫ D.Gbar.hom =
      pullback.fst D.q₁.left D.εU.left ≫ D.Q.hom
    rw [← Over.w D.εU, ← Over.w D.q₁, pullback.condition_assoc])
  have hr : r₁ ≫ D.q₁ = r₂ ≫ D.εU := Over.OverMorphism.ext pullback.condition
  have hw : (schemeYoneda S).map (r₁ ≫ D.q₂) ≫ D.π =
      (schemeYoneda S).map ((r₂ ≫ D.gbar) ≫ D.P.pr 0) ≫ D.π := by
    rw [Functor.map_comp_assoc, ← spacePullback_w D.φ D.π, ← Functor.map_comp_assoc, hr,
      Functor.map_comp_assoc, D.εU_φ, ← Functor.map_comp_assoc, Category.assoc]
  have hz : (r₂ ≫ D.gbar).left z ∈ D.G := by
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    change D.gbar.left (pullback.snd D.q₁.left D.εU.left z) ∈ D.G
    rw [hz₂]
    exact hg
  obtain ⟨i, hi⟩ := exists_eqAt_of_mem_completeLocus (r₂ ≫ D.gbar) (r₁ ≫ D.q₂) hw z hz
  have e1 : (r₁ ≫ D.m) ≫ fst D.Z D.W ≫ D.ζ ≫ D.p i =
      ((r₂ ≫ D.gbar) ≫ D.P.pr i) ≫ D.ι ≫ D.o := by
    simp only [Category.assoc, m, lift_fst_assoc]
    rw [reassoc_of% hr, D.εU_ι_assoc, D.εbar_ζ_assoc, D.ε_p]
  have e2 : (r₁ ≫ D.m) ≫ snd D.Z D.W ≫ D.ι ≫ D.o = (r₁ ≫ D.q₂) ≫ D.ι ≫ D.o := by
    simp only [Category.assoc, m, lift_snd_assoc]
  have key : EqAt ((r₁ ≫ D.m) ≫ fst D.Z D.W ≫ D.ζ ≫ D.p i).left
      ((r₁ ≫ D.m) ≫ snd D.Z D.W ≫ D.ι ≫ D.o).left z := by
    rw [e1, e2]
    exact hi.symm.comp_right (D.ι ≫ D.o).left
  have key' := (eqAt_comp_iff (r₁ ≫ D.m).left (fst D.Z D.W ≫ D.ζ ≫ D.p i).left
    (snd D.Z D.W ≫ D.ι ≫ D.o).left z).mp key
  have hp : (r₁ ≫ D.m).left z = D.m.left y := by
    rw [Over.comp_left, Scheme.Hom.comp_apply, ← hz₁]
    rfl
  rw [hp] at key'
  exact Set.mem_iUnion.mpr ⟨i, key'⟩

theorem range_m : Set.range D.m.left = ⋃ i, D.Γ i := by
  apply subset_antisymm
  · have hcl : IsClosed (D.m.left ⁻¹' ⋃ i, D.Γ i) :=
      (isClosed_iUnion_of_finite D.isClosed_Γ).preimage D.m.left.continuous
    have hdense : Dense (D.q₁.left ⁻¹' (D.εU.left '' (D.gbar.left ⁻¹' D.G))) :=
      D.dense_εU_image.preimage D.q₁.left.isOpenMap
    have h := closure_minimal (fun y hy => D.preimage_subset_Γ hy) hcl
    rw [hdense.closure_eq] at h
    rintro _ ⟨y, rfl⟩
    exact h (Set.mem_univ y)
  · exact Set.iUnion_subset D.Γ_subset_range

instance : _root_.AlgebraicGeometry.IsClosedImmersion D.m.left :=
  .of_isPreimmersion _ (by rw [range_m]; exact isClosed_iUnion_of_finite D.isClosed_Γ)

/-- **Closedness.** The projection `U ×_X W ⟶ W` is proper. -/
instance isProper_q₂ : _root_.AlgebraicGeometry.IsProper D.q₂.left := by
  rw [q₂_eq, Over.comp_left, Over.snd_left]
  infer_instance

end ChowData

end Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover
