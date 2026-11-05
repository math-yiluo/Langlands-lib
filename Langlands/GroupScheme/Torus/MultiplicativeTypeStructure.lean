import Langlands.GroupScheme.Torus.DiagonalizablePowerDecomposition
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.SchematicImage
import Langlands.GroupScheme.SchematicImageComparison
import Langlands.GroupScheme.Descent.AffineFppfQuotient
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent

/-! # Torus and finite quotient of a multiplicative-type group -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A closed actual torus with an actual finite schematic fppf quotient. -/
def HasTorusFiniteQuotient (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (T : GroupScheme (Spec (CommRingCat.of k))) (j : T ⟶ G),
    IsTorus T ∧ IsClosedSubgroup j ∧
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
      IsFinite Q.X.hom ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q

/-- A multiplicative-type group has an actual closed torus with full finite fppf quotient. -/
theorem IsMultiplicativeType.exists_torus_finiteQuotient
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsMultiplicativeType G) :
    HasTorusFiniteQuotient G := by
  classical
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsCommMonObj G.X := hG.isCommMonObj
  obtain ⟨K, hK, aK, Λ, hΛ, hfg, ⟨e⟩⟩ := hG
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k K
  have : Surjective b := hsurj
  have : Flat b := hflat
  have : QuasiCompact b := hqc
  let F := GroupScheme.baseChange b
  obtain ⟨n, T, j, p, hT, hj, hp, hfac, Q, q, hQ, hq⟩ :=
    Diagonalizable.exists_power_torus_finiteQuotient K Λ
  let f := powerHom G n
  have : QuasiCompact f.hom.hom.left := by
    have : QuasiCompact (f.hom.hom.left ≫ G.X.hom) := by
      rw [Over.w]
      infer_instance
    exact QuasiCompact.of_comp f.hom.hom.left G.X.hom
  have : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : IsIso e.hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso e.hom
  have : IsIso e.inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso e.inv
  have : IsSchemeTheoreticallyDominant p.hom.hom.left := hp
  have : IsSchemeTheoreticallyDominant (e.hom ≫ p).hom.hom.left := by
    change IsSchemeTheoreticallyDominant (e.hom.hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  have : IsSchemeTheoreticallyDominant
      (F.map (SchematicImage.projection f)).hom.hom.left :=
    isSchemeTheoreticallyDominant_baseChange b (SchematicImage.projection f)
  have hi : IsClosedSubgroup (F.map (SchematicImage.inclusion f)) :=
    IsClosedSubgroup.baseChange b (inferInstanceAs
      (IsClosedImmersion (SchematicImage.inclusion f).hom.hom.left))
  have hj' : IsClosedSubgroup (j ≫ e.inv) := by
    have : IsClosedImmersion j.hom.hom.left := hj
    change IsClosedImmersion (j.hom.hom.left ≫ e.inv.hom.hom.left)
    infer_instance
  have hfac' :
      F.map (SchematicImage.projection f) ≫ F.map (SchematicImage.inclusion f) =
        (e.hom ≫ p) ≫ (j ≫ e.inv) := by
    rw [← F.map_comp, SchematicImage.projection_inclusion]
    change F.map (powerHom G n) = _
    rw [baseChange_powerHom]
    rw [Category.assoc, ← Category.assoc p, hfac, ← Category.assoc,
      ← powerHom_naturality, Category.assoc, e.hom_inv_id, Category.comp_id]
  let c := SchematicImage.isoOfDominantFactorizations
    (F.map (SchematicImage.projection f)) (e.hom ≫ p)
    (F.map (SchematicImage.inclusion f)) (j ≫ e.inv) hi hj' hfac'
  have hI : IsTorus (SchematicImage.image f) :=
    ⟨K, hK, aK, IsSplitTorus.of_iso c hT⟩
  have hrange :
      SubgroupFunctor.range (F.map (SchematicImage.inclusion f)) =
        SubgroupFunctor.range (j ≫ e.inv) :=
    SchematicImage.range_eq_of_dominantFactorizations
      (F.map (SchematicImage.projection f)) (e.hom ≫ p)
      (F.map (SchematicImage.inclusion f)) (j ≫ e.inv) hi hj' hfac'
  have : IsFinite Q.X.hom := hQ
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have hq' : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (F.map (SchematicImage.inclusion f))) (e.hom ≫ q) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change Flat (e.hom.hom.hom.left ≫ q.hom.hom.left)
      infer_instance
    · change Surjective (e.hom.hom.hom.left ≫ q.hom.hom.left)
      infer_instance
    · change LocallyOfFinitePresentation (e.hom.hom.hom.left ≫ q.hom.hom.left)
      infer_instance
    · rw [hrange]
      apply SubgroupFunctor.ext
      intro U
      apply Subgroup.ext
      intro x
      rw [mem_range_kernelι_iff]
      constructor
      · intro hx
        have hx' : x ≫ e.hom.hom.hom ∈ (SubgroupFunctor.range j).carrier U := by
          rw [← hq.2.2.2, mem_range_kernelι_iff]
          simpa only [Grp.comp_hom_hom, Category.assoc] using hx
        obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp hx'
        refine SubgroupFunctor.mem_range.mpr ⟨t, ?_⟩
        apply (cancel_mono e.hom.hom.hom).mp
        have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
          ((Grp.forget _).mapIso e).inv_hom_id
        rw [Grp.comp_hom_hom, Category.assoc, Category.assoc, he, Category.comp_id]
        exact ht
      · intro hx
        obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
        have ht : (t ≫ j.hom.hom) ≫ q.hom.hom = 1 := by
          rw [← mem_range_kernelι_iff, hq.2.2.2]
          exact SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩
        have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ := by
          exact ((Grp.forget _).mapIso e).inv_hom_id
        simpa only [Grp.comp_hom_hom, Category.assoc, ← Category.assoc e.inv.hom.hom,
          he, Category.id_comp] using ht
  have : Mono (SchematicImage.inclusion f).hom.hom := Over.mono_of_mono_left _
  have : QuasiCompact (e.hom ≫ q).hom.hom.left := by
    have : QuasiCompact ((e.hom ≫ q).hom.hom.left ≫ Q.X.hom) := by
      rw [Over.w]
      infer_instance
    exact QuasiCompact.of_comp (e.hom ≫ q).hom.hom.left Q.X.hom
  obtain ⟨R, r, hRaff, hr, d, hd⟩ :=
    Descent.exists_affine_fppfQuotient b (SchematicImage.inclusion f) Q (e.hom ≫ q) hq'
  have : IsIso d.hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso d.hom
  have hbcfin : IsFinite (F.obj R).X.hom := by
    rw [← Over.w d.hom.hom.hom]
    infer_instance
  have hRfin : IsFinite R.X.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (f := R.X.hom) (g := b) ⟨⟨hsurj, hflat⟩, hqc⟩ hbcfin
  exact ⟨SchematicImage.image f, SchematicImage.inclusion f, hI,
    inferInstanceAs (IsClosedImmersion (SchematicImage.inclusion f).hom.hom.left),
    R, r, hRfin, hr⟩

end Langlands.GroupScheme
