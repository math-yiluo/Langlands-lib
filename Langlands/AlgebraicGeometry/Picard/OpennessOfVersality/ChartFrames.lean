import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.NilpotentFrame
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Sufficiency
import Langlands.AlgebraicGeometry.Modules.BiCech.Kunneth

/-! # Framed covers and lifted transition functions over a square-zero thickening -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open RelativeAffineSections InfinitesimalAffineOpenNilpotence NilpotentUnitReduction
open Langlands.Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

section Thickening

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (q : A →ₐ[R] B) (hq : Function.Surjective q)

include hq in
/-- The relative-space map of a surjective algebra map is a closed immersion. -/
lemma isClosedImmersion_relMap : IsClosedImmersion (relMap f q) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_relMap f q).flip
    (IsClosedImmersion.spec_of_surjective _ hq)

include hq in
/-- An open neighbourhood of a point of the relative space of `B` contains the preimage of an
open neighbourhood of its image. -/
lemma exists_open_preimage_le (T : (relSpace f B).Opens) (y : relSpace f B) (hy : y ∈ T) :
    ∃ T' : (relSpace f A).Opens, (relMap f q).base y ∈ T' ∧ relMap f q ⁻¹ᵁ T' ≤ T := by
  have := isClosedImmersion_relMap f q hq
  have hemb := (relMap f q).isClosedEmbedding
  have hZ : IsClosed ((relMap f q).base '' (T : Set (relSpace f B))ᶜ) :=
    hemb.isClosedMap _ T.isOpen.isClosed_compl
  refine ⟨⟨_, hZ.isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨z, hz, hzy⟩
    exact hz (hemb.injective hzy ▸ hy)
  · intro z hz
    by_contra hzT
    exact hz ⟨z, hzT, rfl⟩

variable (hn : IsNilpotent (RingHom.ker q.toRingHom))

include hq hn

/-- The relative-space map of a surjection with nilpotent kernel is surjective. -/
lemma surjective_relMap_of_isNilpotent : Function.Surjective (relMap f q).base :=
  surjective_relMap f q hq fun x hx => by
    obtain ⟨n, hn⟩ := hn
    refine ⟨n, ?_⟩
    have : x ^ n ∈ RingHom.ker q.toRingHom ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at this
    exact (Ideal.mem_bot.mp this)

/-- A quasi-compact relative space has a finite ordered affine cover whose preimages in the
relative space of a nilpotent quotient carry frames of a given line bundle. -/
theorem exists_frameCover_relMap [CompactSpace (relSpace f A)] (L : LineBundle (relSpace f B)) :
    ∃ K : (relSpace f A).OrderedAffineCover, ∀ i, ∃ e : Γ(L.obj, relMap f q ⁻¹ᵁ K.U i),
      Scheme.Modules.IsFrameOn e (relMap f q ⁻¹ᵁ K.U i) := by
  classical
  let Bs : Set (relSpace f A).Opens := {U | IsAffineOpen U ∧
    ∃ e : Γ(L.obj, relMap f q ⁻¹ᵁ U), Scheme.Modules.IsFrameOn e (relMap f q ⁻¹ᵁ U)}
  have hB : TopologicalSpace.Opens.IsBasis Bs := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro W x hx
    obtain ⟨y, rfl⟩ := surjective_relMap_of_isNilpotent f q hq hn x
    obtain ⟨T, hyT, e, he⟩ :=
      Langlands.AlgebraicGeometry.Modules.BiCech.exists_isFrameOn_of_isLocallyFreeRankOne
        L.property y
    obtain ⟨T', hyT', hT'⟩ := exists_open_preimage_le f q hq T y hyT
    obtain ⟨U, hU, hxU, hUWT⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (relSpace f A).isBasis_affineOpens)
        (show (relMap f q).base y ∈ W ⊓ T' from ⟨hx, hyT'⟩)
    have hle : relMap f q ⁻¹ᵁ U ≤ T :=
      ((relMap f q).preimage_mono (hUWT.trans inf_le_right)).trans hT'
    exact ⟨U, ⟨hU, L.obj.presheaf.map (homOfLE hle).op e, (he.map _).mono hle⟩, hxU,
      hUWT.trans inf_le_left⟩
  obtain ⟨Us, hUs, hfinite, hcover⟩ :=
    hB.exists_finite_of_isCompact (U := ⊤) (show IsCompact (⊤ : (relSpace f A).Opens).carrier from
      isCompact_univ)
  let : Fintype Us := hfinite.fintype
  let : LinearOrder Us :=
    LinearOrder.lift' (Fintype.equivFin Us) (Fintype.equivFin Us).injective
  exact ⟨{
    ι := Us
    U := Subtype.val
    isAffineOpen := fun i => (hUs i.property).1
    iSup_eq_top := by
      simpa only [sSup_eq_iSup'] using hcover.symm }, fun i => (hUs i.property).2⟩

/-- Units of the sections of the relative space of a nilpotent quotient over the preimage of
an affine open lift. -/
lemma exists_units_lift (V : (relSpace f A).Opens) (hV : IsAffineOpen V)
    (u : (Γ(relSpace f B, relMap f q ⁻¹ᵁ V))ˣ) :
    ∃ v : (Γ(relSpace f A, V))ˣ,
      Units.map ((relMap f q).appLE V (relMap f q ⁻¹ᵁ V) le_rfl).hom.toMonoidHom v = u := by
  obtain ⟨happ, hnilapp⟩ := nilpotentSurjective_of_isPushout _ _ _ _
    (isPushout_sections f q V hV) hq hn
  exact unitsMap_surjective _ happ hnilapp u

end Thickening

section Chart

variable {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  {A₀ : Type u} [CommRing A₀] [Algebra R A₀] [Algebra P A₀] [IsScalarTower R P A₀]

/-- Pairwise intersections of an ordered affine cover of a separated relative space are
affine. -/
lemma isAffineOpen_cover_inf [IsSeparated f] (i j : K.ι) : IsAffineOpen (K.U i ⊓ K.U j) := by
  have := isSeparated_relProj f P
  exact (isAffineHom_diagonal_iff (f := relProj f P)).mp inferInstance ⊤ (isAffineOpen_top _)
    _ (by simp) _ (by simp) (K.isAffineOpen i) (K.isAffineOpen j)

/-- The coboundary defect of a family of units whose pushed family is a cocycle vanishes after
base change to `A₀`. -/
lemma secMap_defect_eq_zero (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (hc : CocycleGluing.IsCocycle
      (pushUnits f K (relMap f (IsScalarTower.toAlgHom R P A₀)) (testCover f K A₀).U
        (fun _ _ => le_rfl) g)) (s : K.Idx 2) :
    (secMap (A := A₀) f K s).hom (defect f K g s) = 0 := by
  have h1 := pr_pairUnitsAlong_val f K (IsScalarTower.toAlgHom R P A₀) (fun _ => rfl) g s 0 1
  have h1' := pr_pairUnitsAlong_val f K (IsScalarTower.toAlgHom R P A₀) (fun _ => rfl) g s 1 2
  have h2 := pr_pairUnitsAlong_inv f K (IsScalarTower.toAlgHom R P A₀) (fun _ => rfl) g s 0 2
  have hcoc := pr_cocycle (testCover f K A₀) _ hc s
  have hinv := pr_val_mul_pr_inv (testCover f K A₀)
    (pushUnits f K (relMap f (IsScalarTower.toAlgHom R P A₀)) (testCover f K A₀).U
      (fun _ _ => le_rfl) g) s 0 2
  rw [secMapAlong_toAlgHom] at h1 h1' h2
  unfold defect
  rw [map_sub, map_mul, map_mul, map_one, ← h1, ← h1', ← h2]
  exact sub_eq_zero.mpr ((congrArg (· * _) hcoc).trans hinv)

/-- Chart data over a square-zero thickening: a finite ordered affine cover `K` of the
relative space of `P`, frames of a line bundle `L₀` on the pieces of the pulled-back cover of
the relative space of `A₀`, and units `g` on the pairwise intersections of `K` lifting the
transition functions, whose coboundary is trivial modulo the kernel of `P → A₀`. -/
theorem exists_chartFrames [IsSeparated f] [CompactSpace (relSpace f P)]
    (hπ : Function.Surjective (algebraMap P A₀))
    (hn : IsNilpotent (RingHom.ker (algebraMap P A₀))) (L₀ : LineBundle (relSpace f A₀)) :
    ∃ (K : (relSpace f P).OrderedAffineCover) (e : ∀ i, Γ(L₀.obj, (testCover f K A₀).U i))
      (_ : ∀ i, Scheme.Modules.IsFrameOn (e i) ((testCover f K A₀).U i))
      (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ),
      CocycleGluing.IsTransition e (pushUnits f K (relMap f (IsScalarTower.toAlgHom R P A₀))
        (testCover f K A₀).U (fun _ _ => le_rfl) g) ∧
      ∀ s : K.Idx 2, defect f K g s ∈
        (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom := by
  have hq : Function.Surjective (IsScalarTower.toAlgHom R P A₀) := hπ
  have hn' : IsNilpotent (RingHom.ker (IsScalarTower.toAlgHom R P A₀).toRingHom) := hn
  obtain ⟨K, hK⟩ := exists_frameCover_relMap f (IsScalarTower.toAlgHom R P A₀) hq hn' L₀
  choose e he using hK
  choose g hg using fun i j => exists_units_lift f (IsScalarTower.toAlgHom R P A₀) hq hn'
    (K.U i ⊓ K.U j) (isAffineOpen_cover_inf f K i j)
    (CocycleGluing.frameCocycle (T := (testCover f K A₀).U) e he i j)
  have hpush : pushUnits f K (relMap f (IsScalarTower.toAlgHom R P A₀)) (testCover f K A₀).U
      (fun _ _ => le_rfl) g = CocycleGluing.frameCocycle (T := (testCover f K A₀).U) e he := by
    funext i j
    exact hg i j
  have htr : CocycleGluing.IsTransition e (pushUnits f K (relMap f (IsScalarTower.toAlgHom R P A₀))
      (testCover f K A₀).U (fun _ _ => le_rfl) g) := by
    rw [hpush]
    exact CocycleGluing.isTransition_frameCocycle (he := he)
  refine ⟨K, e, he, g, htr, fun s => ?_⟩
  have := isSeparated_relProj f P
  change defect f K g s ∈
    (RingHom.ker (IsScalarTower.toAlgHom R P A₀).toRingHom).map (structureHom f P (K.inter s)).hom
  rw [← ker_appLE_eq_map f _ hq _ (isAffineOpen_inter f K s), RingHom.mem_ker]
  have hz := secMap_defect_eq_zero f K g (CocycleGluing.isCocycle_of_isTransition he htr) s
  have heq : (relMap f (IsScalarTower.toAlgHom R P A₀)).appLE (K.inter s)
      (relMap f (IsScalarTower.toAlgHom R P A₀) ⁻¹ᵁ K.inter s) le_rfl =
      secMap (A := A₀) f K s ≫ (relSpace f A₀).presheaf.map
        (homOfLE (testCover_inter f K A₀ s).ge).op := by
    rw [secMap, Scheme.Hom.appLE_map]
  rw [heq, CommRingCat.comp_apply, hz, map_zero]

end Chart

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality
