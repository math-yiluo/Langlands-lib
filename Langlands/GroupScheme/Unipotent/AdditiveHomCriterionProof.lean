import Langlands.GroupScheme.Unipotent.AdditiveHomCriterionStatement
import Langlands.GroupScheme.Unipotent.AdditiveCharacter
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.AffineHomImageProof
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.SplitSeriesUnipotent
import Langlands.GroupScheme.SubgroupRangeTransport
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Unipotence detected by additive characters of closed subgroups -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem definingIdeal_lt_of_nonzero
    {k : Type u} [Field k] {G H Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] [IsSeparated Q.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (f : H ⟶ Q) (hf : f ≠ 0) :
    i.hom.hom.left.ker.ideal ⟨⊤, isAffineOpen_top G.X.left⟩ <
      (kernelι f ≫ i).hom.hom.left.ker.ideal ⟨⊤, isAffineOpen_top G.X.left⟩ := by
  have hcomp : (kernelι f ≫ i).hom.hom.left =
      (kernelι f).hom.hom.left ≫ i.hom.hom.left := rfl
  have hle := Scheme.Hom.le_ker_comp (kernelι f).hom.hom.left i.hom.hom.left
  rw [← hcomp] at hle
  refine lt_of_le_of_ne (hle _) fun heq => hf ?_
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion (kernelι f ≫ i).hom.hom.left :=
    IsClosedSubgroup.comp (kernelι_isClosedImmersion f) hi
  have hker : (kernelι f ≫ i).hom.hom.left.ker = i.hom.hom.left.ker :=
    Scheme.IdealSheafData.ext_of_isAffine heq.symm
  have : IsIso ((Over.forget _).map (kernelι f).hom.hom) := by
    change IsIso (kernelι f).hom.hom.left
    exact IsClosedImmersion.isIso_of_ker_eq _ _ _ hcomp.symm hker
  have : IsIso (kernelι f).hom.hom :=
    isIso_of_reflects_iso _ (Over.forget _)
  apply Grp.hom_ext
  apply (cancel_epi (kernelι f).hom.hom).mp
  rw [(kernel_isPullback f).w]
  exact (MonObj.comp_one _).symm

private theorem isUnipotent_of_additive_kernel
    {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (f : H ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    (hK : IsUnipotent (kernel f)) : IsUnipotent H := by
  let A := VectorGroup.groupScheme (CommRingCat.of k) 1
  have hA : RelativeRoot.IsVectorGroupOfDimension A 1 :=
    ⟨VectorGroup.coordinates (CommRingCat.of k) 1, VectorGroup.isNaturalVectorCoordinates⟩
  have : IsAffineHom A.X.hom := hA.isAffineHom
  have : Smooth A.X.hom := hA.smooth
  obtain ⟨I, q, j, _, hIa, hj, _, hq⟩ := affineHomImage k H A f
  have : IsAffineHom I.X.hom := hIa
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : QuasiCompact (q.hom.hom.left ≫ I.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ I.X.hom
  have : IsAffineHom (kernel q).X.hom :=
    IsClosedSubgroup.isAffineHom (kernelι_isClosedImmersion q)
  have hrep : (SubgroupFunctor.range (kernelι f)).IsRepresentedBy (kernelι f) :=
    ⟨inferInstance, rfl⟩
  let e : kernel f ≅ kernel q := hrep.isoOfIsRepresentedBy ⟨inferInstance, hq.2.2.2⟩
  exact isUnipotent_of_kernel_of_quotient q (IsUnipotent.of_iso e.symm hK)
    (unipotentClosedSubgroup k A I j hj (VectorGroup.isUnipotent k 1))

/-- An affine algebraic group over a field is unipotent exactly when every
nontrivial closed subgroup admits a nontrivial homomorphism to the additive group. -/
theorem unipotentAdditiveHomCriterion : UnipotentAdditiveHomCriterionStatement.{u} := by
  intro k _ G _ _
  constructor
  · intro hG H i hi hn
    have : Mono i.hom.hom := IsClosedSubgroup.mono_overHom hi
    have : IsAffineHom H.X.hom := hi.isAffineHom
    have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
    have hH : IsUnipotent H := unipotentClosedSubgroup k G H i hi hG
    have hnt : SubgroupFunctor.range (𝟙 H) ≠ ⊥ := by
      intro hb
      apply hn
      simpa only [Category.id_comp] using
        (SubgroupFunctor.range_comp_eq_bot_iff (𝟙 H) i).mpr hb
    obtain ⟨f, hf⟩ := Unipotent.exists_additive_character hH hnt
    exact ⟨⟨f, 0, hf⟩⟩
  · intro h
    classical
    let A := VectorGroup.groupScheme (CommRingCat.of k) 1
    have : IsAffineHom A.X.hom := RelativeRoot.IsVectorGroupOfDimension.isAffineHom
      ⟨VectorGroup.coordinates (CommRingCat.of k) 1, VectorGroup.isNaturalVectorCoordinates⟩
    have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
    let U : G.X.left.affineOpens := ⟨⊤, isAffineOpen_top G.X.left⟩
    have : IsNoetherianRing Γ(G.X.left, ⊤) := IsLocallyNoetherian.component_noetherian U
    have hInd : ∀ J : Ideal Γ(G.X.left, ⊤),
        ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
          IsClosedSubgroup i → i.hom.hom.left.ker.ideal U = J → IsUnipotent H := by
      intro J
      apply wellFounded_gt.induction J
      intro J ih H i hi hJ
      have : IsClosedImmersion i.hom.hom.left := hi
      have : Mono i.hom.hom := IsClosedSubgroup.mono_overHom hi
      have : IsAffineHom H.X.hom := hi.isAffineHom
      have : LocallyOfFiniteType H.X.hom := by
        rw [← Over.w i.hom.hom]
        infer_instance
      by_cases hbot : SubgroupFunctor.range i = ⊥
      · have htriv : RelativeRoot.HasSplitSeries 0 H :=
          (SubgroupFunctor.range_comp_eq_bot_iff (𝟙 H) i).mp (by
            simpa only [Category.id_comp] using hbot)
        exact htriv.isUnipotent
      · have : Nontrivial (H ⟶ A) := h H i hi hbot
        obtain ⟨f, hf⟩ := exists_ne (0 : H ⟶ A)
        have hstrict : J < (kernelι f ≫ i).hom.hom.left.ker.ideal U := by
          rw [← hJ]
          exact definingIdeal_lt_of_nonzero i hi f hf
        have hclosed : IsClosedSubgroup (kernelι f ≫ i) :=
          IsClosedSubgroup.comp (kernelι_isClosedImmersion f) hi
        have hK := ih _ hstrict (kernel f) (kernelι f ≫ i) hclosed rfl
        exact isUnipotent_of_additive_kernel f hK
    exact hInd _ G (𝟙 G) (IsClosedSubgroup.of_iso (Iso.refl G)) rfl

end Langlands.GroupScheme
