import Langlands.GroupScheme.SimplyConnected.CoverPreimageCentralProduct

/-! # Rational characters of the preimage of a subgroup in a central cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoverPreimage

section General

variable {S : Scheme.{u}}

/-- The second inclusion of a product followed by the second projection is the identity. -/
theorem prodInr_snd (A B : GroupScheme S) : prodInr A B ≫ snd A B = 𝟙 B := by
  apply hom_ext_points
  intro T y
  rw [Grp.comp_hom_hom, ← Category.assoc, prodInr, comp_homOfPoints, Grp.snd_hom_hom,
    Grp.id_hom_hom, Category.comp_id]
  exact congrArg Prod.snd ((productPointsEquiv A B T).apply_symm_apply (1, y))

variable {G D C M : GroupScheme S}

/-- The comparison map from the preimage `C ×_G M` to the derived part `D ×_G M`. -/
def toDerivedPart (π : C ⟶ D) (d : D ⟶ G) (j : M ⟶ G) :
    subgroupIntersection (π ≫ d) j ⟶ subgroupIntersection d j :=
  pullback.lift (subgroupIntersectionFst (π ≫ d) j ≫ π) (subgroupIntersectionSnd (π ≫ d) j)
    (by rw [Category.assoc]; exact subgroupIntersection_condition (π ≫ d) j)

@[reassoc]
theorem toDerivedPart_fst (π : C ⟶ D) (d : D ⟶ G) (j : M ⟶ G) :
    toDerivedPart π d j ≫ subgroupIntersectionFst d j = subgroupIntersectionFst (π ≫ d) j ≫ π :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem toDerivedPart_snd (π : C ⟶ D) (d : D ⟶ G) (j : M ⟶ G) :
    toDerivedPart π d j ≫ subgroupIntersectionSnd d j = subgroupIntersectionSnd (π ≫ d) j :=
  pullback.lift_snd _ _ _

/-- The comparison map is the base change of `π` along the derived part. -/
theorem toDerivedPart_isPullback (π : C ⟶ D) (d : D ⟶ G) (j : M ⟶ G) :
    IsPullback (subgroupIntersectionFst (π ≫ d) j).hom.hom.left
      (toDerivedPart π d j).hom.hom.left π.hom.hom.left
      (subgroupIntersectionFst d j).hom.hom.left := by
  have hs := (subgroupIntersection_isPullback_scheme (π ≫ d) j).flip
  have ht := (subgroupIntersection_isPullback_scheme d j).flip
  have he : (toDerivedPart π d j).hom.hom.left ≫ (subgroupIntersectionSnd d j).hom.hom.left =
      (subgroupIntersectionSnd (π ≫ d) j).hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) (toDerivedPart_snd π d j)
  have hp : (toDerivedPart π d j).hom.hom.left ≫ (subgroupIntersectionFst d j).hom.hom.left =
      (subgroupIntersectionFst (π ≫ d) j).hom.hom.left ≫ π.hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) (toDerivedPart_fst π d j)
  rw [← he] at hs
  exact (IsPullback.of_right hs hp ht).flip

/-- The comparison map is a central fppf cover when `π` is. -/
theorem isCentralFppfCover_toDerivedPart {π : C ⟶ D} (hπ : IsCentralFppfCover π) (d : D ⟶ G)
    {j : M ⟶ G} [Mono j.hom.hom] :
    IsCentralFppfCover (toDerivedPart π d j) := by
  have : Mono (subgroupIntersectionFst (π ≫ d) j).hom.hom :=
    (subgroupIntersection_isPullback (π ≫ d) j).mono_fst_of_mono
  exact hπ.of_isPullback (subgroupIntersectionFst (π ≫ d) j) (toDerivedPart π d j)
    (subgroupIntersectionFst d j) (toDerivedPart_fst π d j).symm (toDerivedPart_isPullback π d j)

end General

section Field

variable {k : Type u} [Field k]

/-- A central isogeny over a field is a central fppf cover. -/
theorem isCentralFppfCover_of_isCentralIsogeny {G H : GroupScheme (Spec (CommRingCat.of k))}
    {π : G ⟶ H} (hπ : IsCentralIsogeny π) : IsCentralFppfCover π := by
  have := hπ.isFinite
  obtain ⟨N, hN, hNk⟩ := hπ.exists_pow_eq_one_kernel
  refine ⟨inferInstance, hπ.flat, hπ.surjective, hπ.locallyOfFinitePresentation,
    fun T x hx => hπ.mem_center_of_comp_eq_one hx, N, hN, fun T x hx => ?_⟩
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp ((mem_range_kernelι_iff π x).mpr hx)
  rw [← hy, ← MonObj.pow_comp, hNk T y, MonObj.one_comp]

end Field

section Characters

variable {S : Scheme.{u}} {G D C M : GroupScheme S} {Z : CommGroupScheme S}

/-- Every rational character of the preimage `C ×_G M` has a positive multiple restricted from
a rational character of `M`. -/
theorem exists_nsmul_eq_characterRestrict {π : C ⟶ D} (hπ : IsCentralFppfCover π)
    (d : D ⟶ G) [Mono d.hom.hom] {i : Z.toGrp ⟶ G} (hic : IsCentral i)
    (hm : IsCentralFppfCover (centralProduct i d hic)) (j : M ⟶ G) [Mono j.hom.hom]
    (iM : Z.toGrp ⟶ M) (hiM : iM ≫ j = i)
    (χ' : rationalCharacters (subgroupIntersection (π ≫ d) j)) :
    ∃ n : ℕ, 0 < n ∧ ∃ χ : rationalCharacters M,
      n • χ' = characterRestrict (subgroupIntersectionSnd (π ≫ d) j) χ := by
  let e := toDerivedPart π d j
  have he := isCentralFppfCover_toDerivedPart hπ d (j := j)
  have := he.quasiCompact
  have := he.flat
  have := he.surjective
  obtain ⟨N, hN, hNx⟩ := he.exponent
  obtain ⟨ψ, hψ⟩ := exists_characterRestrict_eq_nsmul_of_fpqc e N hNx χ'
  let hicM := isCentral_of_comp_mono hic j iM hiM
  let ρ := restrictedProduct d j iM hicM
  have hρ := isCentralFppfCover_restrictedProduct i d hic hm j iM hiM
  have := hρ.quasiCompact
  have := hρ.flat
  have := hρ.surjective
  obtain ⟨N₂, hN₂, hN₂x⟩ := hρ.exponent
  obtain ⟨χ, hχ⟩ := exists_characterRestrict_eq_nsmul_of_fpqc ρ N₂ hN₂x
    (characterRestrict (snd Z.toGrp (subgroupIntersection d j)) ψ)
  refine ⟨N₂ * N, Nat.mul_pos hN₂ hN, χ, ?_⟩
  have hmd : prodInr Z.toGrp (subgroupIntersection d j) ≫ ρ = subgroupIntersectionSnd d j :=
    prodInr_prodHom _ _ _
  rw [← toDerivedPart_snd π d j, characterRestrict_comp, AddMonoidHom.comp_apply, ← hmd,
    characterRestrict_comp, AddMonoidHom.comp_apply, hχ, map_nsmul, ← AddMonoidHom.comp_apply,
    ← characterRestrict_comp, prodInr_snd, characterRestrict_id, AddMonoidHom.id_apply,
    map_nsmul, hψ, smul_smul]

end Characters

end Langlands.GroupScheme.CoverPreimage
