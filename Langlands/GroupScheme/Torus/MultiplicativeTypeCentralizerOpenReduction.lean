import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralizerOpenStatement
import Langlands.GroupScheme.SubgroupFunctor.CentralizerBaseChange
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.BaseChangeReflection

/-! # Reduction of multiplicative-type centralizer openness to the split case -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- The split input for centralizer openness, including torsion character
groups and arbitrary ambient group schemes. -/
def DiagonalizableCentralizerOpenProperty : Prop :=
  ∀ (k : Type u) [Field k] (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (G N C : GroupScheme (Spec (CommRingCat.of k)))
    (i : (Diagonalizable.groupScheme (CommRingCat.of k) M).toGrp ⟶ G),
    Mono i.hom.hom.left →
      ∀ (n : N ⟶ G) (c : C ⟶ N),
        (torusNormalizer i).IsRepresentedBy n →
        ((torusCentralizer i).comap n).IsRepresentedBy c →
        IsOpenImmersion c.hom.hom.left

/-- Openness of a group-scheme homomorphism descends along an fpqc change
of the base scheme. -/
theorem isOpenImmersion_groupHom_of_fpqcBaseChange {S S' : Scheme.{u}}
    (b : S' ⟶ S) [Surjective b] [Flat b] [QuasiCompact b]
    {H G : GroupScheme S} (f : H ⟶ G)
    (hf : IsOpenImmersion ((GroupScheme.baseChange b).map f).hom.hom.left) :
    IsOpenImmersion f.hom.hom.left := by
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (baseChange_map_isPullback b f)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hf

/-- In particular, openness descends along every field extension, without
algebraicity, finiteness or separability assumptions. -/
theorem isOpenImmersion_groupHom_of_fieldBaseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {H G : GroupScheme (Spec (CommRingCat.of k))} (f : H ⟶ G)
    (hf : IsOpenImmersion ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f).hom.hom.left) :
    IsOpenImmersion f.hom.hom.left := by
  obtain ⟨h₁, h₂, h₃⟩ := fieldExtension_fpqc k K
  let : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) := h₁
  let : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := h₂
  let : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k K))) := h₃
  exact isOpenImmersion_groupHom_of_fpqcBaseChange _ f hf

/-- The split diagonalizable input implies the unchanged field-level
multiplicative-type centralizer openness statement. -/
theorem multiplicativeTypeCentralizerOpen_of_diagonalizable
    (hdiag : DiagonalizableCentralizerOpenProperty.{u}) :
    MultiplicativeTypeCentralizerOpenStatement.{u} := by
  intro k _ G H i _ _ hH hi N C n c f hn hc hfc
  obtain ⟨K, _, _, M, _, _, ⟨e⟩⟩ := hH
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  let D := Diagonalizable.groupScheme (CommRingCat.of K) M
  let t : D.toGrp ⟶ B.obj G := e.inv ≫ B.map i
  let : IsClosedImmersion i.hom.hom.left := hi
  have : Mono (B.map i).hom.hom.left := by
    have : Mono i.hom.hom := Over.mono_of_mono_left _
    have : Mono (B.map i).hom.hom :=
      inferInstanceAs (Mono ((Over.pullback b).map i.hom.hom))
    exact Over.mono_left_of_mono _
  have : Mono t.hom.hom.left := by
    change Mono (e.inv.hom.hom.left ≫ (B.map i).hom.hom.left)
    infer_instance
  have ht : SubgroupFunctor.range t = (SubgroupFunctor.range i).baseChange b := by
    change SubgroupFunctor.range (e.symm.hom ≫ B.map i) = _
    rw [SubgroupFunctor.range_iso_comp e.symm, SubgroupFunctor.range_baseChangeHom]
  have hnbase : (torusNormalizer t).IsRepresentedBy (B.map n) := by
    change (SubgroupFunctor.range t).normalizer.IsRepresentedBy _
    rw [ht, ← SubgroupFunctor.normalizer_baseChange]
    exact hn.baseChange b
  have hcrep := hn.comap_of_comp hc f hfc
  have hcbase : ((torusCentralizer t).comap (B.map n)).IsRepresentedBy (B.map f) := by
    rw [torusCentralizer_eq_centralizer_range, ht,
      ← SubgroupFunctor.centralizer_baseChange, ← SubgroupFunctor.comap_baseChange]
    exact hcrep.baseChange b
  apply isOpenImmersion_groupHom_of_fieldBaseChange k K f
  exact hdiag K M (B.obj G) (B.obj N) (B.obj C) t inferInstance
    (B.map n) (B.map f) hnbase hcbase

end Langlands.GroupScheme
