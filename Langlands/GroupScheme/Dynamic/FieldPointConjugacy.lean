import Langlands.GroupScheme.Dynamic.PointedEtaleConjugacy
import Langlands.GroupScheme.Dynamic.ResidueCocharacterTransporter
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Etale conjugacy from presentations agreeing at a field point -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Dynamic

variable {S T : Scheme.{u}} {G P Q : GroupScheme S}

/-- Compose etale conjugacy data with an etale change of the original base. -/
def EtaleSubgroupConjugacyData.comp
    (p : T ⟶ S) [Etale p] (i : P ⟶ G) (j : Q ⟶ G) (t : T)
    (d : EtaleSubgroupConjugacyData ((baseChange p).map i)
      ((baseChange p).map j) t) :
    EtaleSubgroupConjugacyData i j (p t) := by
  let r := d.projection ≫ p
  let e := Descent.pullbackComparison p d.projection r rfl G
  let g := d.conjugator ≫ e.hom.hom.hom
  let : Etale d.projection := d.etale
  refine ⟨d.neighbourhood, r, inferInstance, d.point, ?_, g, ?_⟩
  · change p (d.projection d.point) = p t
    rw [d.point_over]
  · have h := (SubgroupFunctor.range_comp_iso_eq_iff _ _ e).mpr d.conjugates
    rw [Category.assoc, innerIso_hom_comp, ← Category.assoc,
      Descent.pullbackComparison_naturality,
      Descent.pullbackComparison_naturality,
      Category.assoc, SubgroupFunctor.range_iso_comp,
      SubgroupFunctor.range_iso_comp] at h
    exact h

/-- Global presentations agreeing at a supplied field point give etale
conjugacy over an arbitrary base. -/
def etaleConjugacyOfFieldPointPresentations
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : P ⟶ G) (j : Q ⟶ G)
    (χ ψ : (Gm S).toGrp ⟶ G)
    (hi : SubgroupFunctor.range i = parabolic χ)
    (hj : SubgroupFunctor.range j = parabolic ψ)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (heq : baseChangeCocharacter b χ = baseChangeCocharacter b ψ) :
    EtaleSubgroupConjugacyData i j (b (IsLocalRing.closedPoint k)) := by
  classical
  let s := b (IsLocalRing.closedPoint k)
  let H := Scheme.exists_Spec_apply_eq s
  let R := Classical.choose H
  let Hq := Classical.choose_spec H
  let q := Classical.choose Hq
  let Hx := Classical.choose_spec Hq
  let : IsOpenImmersion q := Classical.choose Hx
  let x := Classical.choose (Classical.choose_spec Hx)
  have hx : q x = s := Classical.choose_spec (Classical.choose_spec Hx)
  have hr : Set.range b ⊆ Set.range q := by
    rintro _ ⟨z, rfl⟩
    refine ⟨x, ?_⟩
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint k)] using hx
  let bq := IsOpenImmersion.lift q b hr
  have hbq : bq ≫ q = b := IsOpenImmersion.lift_fac _ _ _
  let χq := baseChangeCocharacter q χ
  let ψq := baseChangeCocharacter q ψ
  have heqq : baseChangeCocharacter bq χq = baseChangeCocharacter bq ψq := by
    apply (cancel_mono (Descent.pullbackComparison q bq b hbq G).hom).mp
    exact (baseChangeCocharacter_tower q bq b hbq χ).trans
      (heq.trans (baseChangeCocharacter_tower q bq b hbq ψ).symm)
  have hiq : SubgroupFunctor.range ((baseChange q).map i) = parabolic χq := by
    rw [SubgroupFunctor.range_baseChangeHom, hi, parabolic_baseChange]
  have hjq : SubgroupFunctor.range ((baseChange q).map j) = parabolic ψq := by
    rw [SubgroupFunctor.range_baseChangeHom, hj, parabolic_baseChange]
  let : Smooth ((baseChange q).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom q)
    infer_instance
  let : IsAffineHom ((baseChange q).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom q)
    exact MorphismProperty.pullback_snd _ _ inferInstance
  let : IsAffine ((baseChange q).obj G).X.left := by
    exact isAffine_of_isAffineHom ((baseChange q).obj G).X.hom
  let d₀ := residueCocharacterTransporter χq ψq bq heqq
  let d := etaleConjugacyOfPresentations (G := (baseChange q).obj G)
    inferInstance ((baseChange q).map i) ((baseChange q).map j)
    χq ψq hiq hjq d₀.point d₀.transporter d₀.transports
  have hq : q d₀.point = s := by
    change (bq ≫ q) (IsLocalRing.closedPoint k) = s
    rw [hbq]
  have hq' : q d₀.point = b (IsLocalRing.closedPoint k) := hq
  exact hq' ▸ EtaleSubgroupConjugacyData.comp q i j d₀.point d

end Langlands.GroupScheme.Dynamic
