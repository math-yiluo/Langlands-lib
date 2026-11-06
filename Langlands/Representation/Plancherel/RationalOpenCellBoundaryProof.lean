import Langlands.Representation.Plancherel.RationalOpenCellBoundaryStatement

/-! # The algebraic boundary of the actual rational dynamic open cell -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open HarishChandraSchwartz

/-- A rational point lands in the range of an open immersion exactly when it
factors through that immersion. -/
theorem rationalPoint_mem_range_iff (F : Type u) [Field F]
    {X Y : Over (Spec (CommRingCat.of F))} (f : X ⟶ Y) [IsOpenImmersion f.left]
    (p : RationalPoint F Y) :
    p.left (IsLocalRing.closedPoint F) ∈ Set.range f.left ↔
      ∃ q : RationalPoint F X, q ≫ f = p := by
  constructor
  · intro hp
    have h : Set.range p.left ⊆ Set.range f.left := by
      rintro _ ⟨t, rfl⟩
      have ht : t = IsLocalRing.closedPoint F :=
        @Subsingleton.elim (PrimeSpectrum F) inferInstance _ _
      simpa only [ht] using hp
    let l := IsOpenImmersion.lift f.left p.left h
    have hl : l ≫ f.left = p.left := IsOpenImmersion.lift_fac _ _ _
    let q : RationalPoint F X := Over.homMk l (by
      have h1 := Over.w f
      have h2 := Over.w p
      rw [← h1, ← Category.assoc, hl, h2])
    refine ⟨q, ?_⟩
    apply Over.OverMorphism.ext
    exact hl
  · rintro ⟨q, rfl⟩
    exact ⟨q.left (IsLocalRing.closedPoint F), rfl⟩

/-- The inverse of opposite multiplication has exactly the actual open-cell
image on rational points. -/
theorem range_inverse_opposite_multiplication (F : Type u) [Field F]
    {G U P : GroupScheme (Spec (CommRingCat.of F))}
    (iU : U ⟶ G) (iP : P ⟶ G)
    (V Q : SubgroupFunctor G) (hU : V.IsRepresentedBy iU) (hP : Q.IsRepresentedBy iP) :
    Set.range (fun w : RationalPoint F (U.X ⊗ P.X) =>
      w ≫ ((fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)) ≫ ι[G.X]) =
      Set.range (openCellMap
        (P := Q.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
        (V := V.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))) := by
  ext p
  constructor
  · rintro ⟨w, rfl⟩
    have hu : w ≫ fst U.X P.X ≫ iU.hom.hom ∈
        V.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) := by
      rw [← hU.2]
      exact SubgroupFunctor.mem_range.mpr ⟨w ≫ fst U.X P.X, Category.assoc _ _ _⟩
    have hp : w ≫ snd U.X P.X ≫ iP.hom.hom ∈
        Q.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) := by
      rw [← hP.2]
      exact SubgroupFunctor.mem_range.mpr ⟨w ≫ snd U.X P.X, Category.assoc _ _ _⟩
    refine ⟨(⟨(w ≫ snd U.X P.X ≫ iP.hom.hom)⁻¹, inv_mem hp⟩,
      ⟨w ≫ fst U.X P.X ≫ iU.hom.hom, hu⟩), ?_⟩
    change _ = (w ≫ ((fst U.X P.X ≫ iU.hom.hom) *
      (snd U.X P.X ≫ iP.hom.hom)))⁻¹
    simp only [openCellMap, MonObj.comp_mul, mul_inv_rev]
  · rintro ⟨⟨p, v⟩, rfl⟩
    have hp := (Q.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))).inv_mem p.property
    have hv := v.property
    have hp' : (p : RationalPoint F G.X)⁻¹ ∈ (SubgroupFunctor.range iP).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F)))) := by
      simpa only [hP.2] using hp
    have hv' : (v : RationalPoint F G.X) ∈ (SubgroupFunctor.range iU).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F)))) := by
      simpa only [hU.2] using hv
    obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp hp'
    obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp hv'
    refine ⟨lift b a, ?_⟩
    change ((lift b a) ≫ ((fst U.X P.X ≫ iU.hom.hom) *
      (snd U.X P.X ≫ iP.hom.hom)))⁻¹ = _
    simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, ha, hb,
      mul_inv_rev, inv_inv, openCellMap]

/-- The complete geometric boundary proposition, over arbitrary fields. -/
theorem rationalDynamicOpenCellBoundary : RationalDynamicOpenCellBoundaryStatement.{u} := by
  intro F _ G _ _
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro χ
  let χ' := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ
  let U := Dynamic.Affine.unipotentScheme χ'
  let P := Dynamic.Affine.parabolicScheme χ
  let iU := Dynamic.Affine.unipotentHom χ'
  let iP := Dynamic.Affine.parabolicHom χ
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom χ'
  have hP := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  let m : U.X ⊗ P.X ⟶ G.X :=
    (fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)
  have hm : IsOpenImmersion m.left := oppositeCellStatement F G χ U P iU iP hU hP
  have : IsIso (ι[G.X]).left :=
    inferInstanceAs (IsIso ((Over.forget _).map ι[G.X]))
  let f : U.X ⊗ P.X ⟶ G.X := m ≫ ι[G.X]
  have : IsOpenImmersion f.left := by
    change IsOpenImmersion (m.left ≫ (ι[G.X]).left)
    infer_instance
  have hr : (fun p : RationalPoint F G.X => p.left (IsLocalRing.closedPoint F)) ⁻¹'
      Set.range f.left = Set.range (openCellMap
        (P := (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
        (V := (Dynamic.unipotent χ').carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))) := by
    rw [← range_inverse_opposite_multiplication F iU iP _ _ hU hP]
    ext p
    exact rationalPoint_mem_range_iff F f p
  refine ⟨(Set.range f.left)ᶜ, f.left.isOpenEmbedding.isOpen_range.isClosed_compl, ?_, ?_⟩
  · intro h
    have h1 : (1 : RationalPoint F G.X) ∈ Set.range (openCellMap
        (P := (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
        (V := (Dynamic.unipotent χ').carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))) :=
      ⟨(1, 1), by simp [openCellMap]⟩
    rw [← hr] at h1
    have hn : (1 : RationalPoint F G.X).left (IsLocalRing.closedPoint F) ∈
        (Set.range f.left)ᶜ := by rw [h]; exact Set.mem_univ _
    exact hn h1
  · rw [Set.preimage_compl, hr]

end Langlands.Plancherel
