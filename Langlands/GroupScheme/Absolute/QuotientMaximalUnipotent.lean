import Langlands.GroupScheme.Absolute.MaximalUnipotentBorel
import Langlands.GroupScheme.Absolute.QuotientUnipotentPartImage
import Langlands.GroupScheme.Absolute.QuotientNormalizer
import Langlands.GroupScheme.Rational.TorusCentralizerImage

/-! # Maximal unipotent subgroup images and their realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- Preservation of maximal smooth connected unipotent subgroups in supplied
smooth closed image presentations. -/
def PreservesMaximalUnipotentSubgroups (q : G ⟶ Q) : Prop :=
  ∀ (U J : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G) (j : J ⟶ Q) (f : U ⟶ J),
    IsClosedSubgroup j → Smooth J.X.hom → Surjective f.hom.hom.left →
      i ≫ q = f ≫ j → IsMaximalUnipotentSubgroup i → IsMaximalUnipotentSubgroup j

namespace QuotientMaximalUnipotent

variable [IsAlgClosed k]
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]

/-- Borel image preservation implies maximal-unipotent image preservation. -/
theorem preservesMaximalUnipotentSubgroups_of_borel_images (q : G ⟶ Q)
    (himages : ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
      IsBorelSubgroup b → ∃ (C : GroupScheme (Spec (CommRingCat.of k)))
        (c : C ⟶ Q) (p : B ⟶ C), IsBorelSubgroup c ∧
          Surjective p.hom.hom.left ∧ b ≫ q = p ≫ c) :
    PreservesMaximalUnipotentSubgroups q := by
  intro U J i j f hj hJsm hf hcomm hi
  obtain ⟨B, b, u, hb, hu, hui⟩ := hi.isBorelUnipotentSubgroup
  have : Smooth B.X.hom := hb.smooth
  have : ConnectedSpace B.X.left := hb.connectedSpace
  have : IsAffineHom B.X.hom := hb.isClosedSubgroup.isAffineHom
  obtain ⟨C, c, p, hc, hp, hbc⟩ := himages B b hb
  have : Smooth C.X.hom := hc.smooth
  have : ConnectedSpace C.X.left := hc.connectedSpace
  have : IsAffineHom C.X.hom := hc.isClosedSubgroup.isAffineHom
  have : Smooth J.X.hom := hJsm
  have : IsReduced J.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ J.X.hom
  have : Surjective f.hom.hom.left := hf
  have : IsSchemeTheoreticallyDominant f.hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have hr : SubgroupFunctor.range j ≤ SubgroupFunctor.range c := by
    apply (SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant
      f j c hc.isClosedSubgroup).mp
    rw [← hcomm, ← hui, Category.assoc, hbc, ← Category.assoc]
    exact SubgroupFunctor.range_le_of_factor (u ≫ p) rfl
  have hcrep : (SubgroupFunctor.range c).IsRepresentedBy c := by
    have : IsClosedImmersion c.hom.hom.left := hc.isClosedSubgroup
    exact ⟨Over.mono_of_mono_left _, rfl⟩
  let v : J ⟶ C := hcrep.factorHom j hr
  have hvc : v ≫ c = j := hcrep.factorHom_comp j hr
  have hcommC : u ≫ p = f ≫ v := by
    have : IsClosedImmersion c.hom.hom.left := hc.isClosedSubgroup
    have : Mono c.hom.hom := Over.mono_of_mono_left _
    have : Mono c := (Grp.forget _).mono_of_mono_map (inferInstance : Mono c.hom.hom)
    apply (cancel_mono c).mp
    rw [Category.assoc, ← hbc, ← Category.assoc, hui, Category.assoc, hvc, hcomm]
  have hpart : IsUnipotentPart v :=
    QuotientUnipotentPartImage.preservesUnipotentParts
      hb.isSolvableGroupScheme hc.isSolvableGroupScheme p hp U J u v f hu
      (IsClosedSubgroup.of_comp hc.isClosedSubgroup (by rwa [hvc]))
      hJsm hf hcommC
  have hmax := hpart.isMaximalUnipotentSubgroup hc
  rwa [hvc] at hmax

omit [ConnectedSpace G.X.left] in
/-- Maximal-unipotent images and rational conjugacy realize every prescribed
maximal smooth connected unipotent subgroup downstairs. -/
theorem exists_maximalUnipotent_image_of_images (q : G ⟶ Q)
    (hq : Surjective q.hom.hom.left) (himages : PreservesMaximalUnipotentSubgroups q)
    {J : GroupScheme (Spec (CommRingCat.of k))} (j : J ⟶ Q)
    (hj : IsMaximalUnipotentSubgroup j) :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G) (f : U ⟶ J),
      IsMaximalUnipotentSubgroup i ∧ Surjective f.hom.hom.left ∧ i ≫ q = f ≫ j := by
  obtain ⟨U, i, hi⟩ := MaximalUnipotentExistence.exists_maximal G
  have : Smooth U.X.hom := hi.smooth
  have : ConnectedSpace U.X.left := hi.connectedSpace
  have : IsAffineHom U.X.hom := hi.isClosedSubgroup.isAffineHom
  obtain ⟨C, c, p, hc, hpc, _, hp, _, _, hCsm, _, _⟩ :=
    HomImage.exists_image (i ≫ q)
  have hcmax : IsMaximalUnipotentSubgroup c :=
    himages U C i c p hc hCsm hp hpc.symm hi
  obtain ⟨x, e, he⟩ := hcmax.exists_conjugatingIso hj
  have : Surjective q.hom.hom.left := hq
  have : LocallyOfFiniteType (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : LocallyOfFiniteType q.hom.hom.left :=
    locallyOfFiniteType_of_comp _ Q.X.hom
  obtain ⟨g, hg⟩ := exists_rationalPointLift q x
  refine ⟨U, i ≫ (G.innerIso g).hom, p ≫ e.hom, hi.comp_iso (G.innerIso g), ?_, ?_⟩
  · have : Surjective p.hom.hom.left := hp
    have : IsIso e.hom.hom.hom.left :=
      (Over.forget _).map_isIso ((Grp.forget _).map e.hom)
    change Surjective (p.hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  · rw [Category.assoc, innerIso_hom_comp, hg, ← Category.assoc, ← hpc,
      Category.assoc, he, ← Category.assoc]

end QuotientMaximalUnipotent

end Langlands.GroupScheme
