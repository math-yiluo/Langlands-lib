import Langlands.GroupScheme.Rational.RootSubgroupStability
import Langlands.GroupScheme.Rational.VectorLineActionRigidity

/-! # Actions fixing a torus preserve its intrinsic root subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section OverBase

variable {B : Scheme.{u}} {S : CommGroupScheme B} {H K : GroupScheme B}
    (b : AutomorphicAction K H) (s : S.toGrp ⟶ H)
    (hfix : ∀ (T : Over B) (k : T ⟶ K.X) (t : T ⟶ S.X),
      b.act k (t ≫ s.hom.hom) = t ≫ s.hom.hom)
    (α : characterLattice S)

include hfix

/-- An automorphic action fixing the torus map commutes with its conjugation. -/
theorem orbit_act_of_fixes_torus {T : Over B} (k : T ⟶ K.X) (g : T ⟶ H.X) :
    orbit s (b.act k g) = b.act (fst T S.X ≫ k) (orbit s g) := by
  simp only [orbit, AutomorphicAction.conjugation_act, b.naturality,
    b.act_mul_right, b.act_inv, hfix]

/-- Acting on an affine-line orbit extension preserves the same character. -/
theorem IsOrbitExtension.act_of_fixes_torus {T : Over B}
    {g : T ⟶ H.X} {e : T ⊗ AffineLine.scheme B ⟶ H.X}
    (he : IsOrbitExtension s α g e) (k : T ⟶ K.X) :
    IsOrbitExtension s α (b.act k g)
      (b.act (fst T (AffineLine.scheme B) ≫ k) e) := by
  rw [IsOrbitExtension, b.naturality, whiskerLeft_fst_assoc, he,
    orbit_act_of_fixes_torus b s hfix]

/-- The original action preserves each intrinsic root functor on all tests. -/
theorem subgroup_isStable_of_fixes_torus : b.IsStable (subgroup s α) := by
  intro T k g hg
  obtain ⟨e, he, he0⟩ := hg
  refine ⟨b.act (fst T (AffineLine.scheme B) ≫ k) e,
    he.act_of_fixes_torus b s hfix α k, ?_⟩
  rw [AutomorphicAction.evalZero_act, he0, b.act_one]

variable {V : GroupScheme B} (j : V ⟶ H) (hj : (subgroup s α).IsRepresentedBy j)

/-- The induced actual action on any supplied representative of an intrinsic root. -/
def rootActionOfFixesTorus : AutomorphicAction K V :=
  b.onRepresentedSubgroup j hj (subgroup_isStable_of_fixes_torus b s hfix α)

theorem rootActionOfFixesTorus_act_comp {T : Over B}
    (k : T ⟶ K.X) (v : T ⟶ V.X) :
    (rootActionOfFixesTorus b s hfix α j hj).act k v ≫ j.hom.hom =
      b.act k (v ≫ j.hom.hom) :=
  b.onRepresentedSubgroup_act_comp j hj
    (subgroup_isStable_of_fixes_torus b s hfix α) k v

end OverBase

section NormalizedConjugation

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G H K : GroupScheme B}
    (h : H ⟶ G) (a : K ⟶ G)
    (hn : (SubgroupFunctor.range h).IsNormalizedBy (SubgroupFunctor.range a))
    [Mono h.hom.hom] (s : S.toGrp ⟶ H)
    (hc : SubgroupFunctor.range a ≤
      (AutomorphicAction.conjugation (s ≫ h)).fixedSubgroup)

include hc

/-- Conjugation on a normalized subgroup fixes any torus centralized in the ambient group. -/
theorem normalizedConjugation_fixes_torus {T : Over B}
    (q : T ⟶ K.X) (t : T ⟶ S.X) :
    (AutomorphicAction.ofNormalizedConjugation h a hn).act q
      (t ≫ s.hom.hom) = t ≫ s.hom.hom := by
  apply (cancel_mono h.hom.hom).1
  change (lift q (t ≫ s.hom.hom) ≫
    SubgroupFunctor.normalizedConjugation h a hn) ≫ h.hom.hom =
      (t ≫ s.hom.hom) ≫ h.hom.hom
  rw [SubgroupFunctor.lift_comp_normalizedConjugation_comp]
  have e := hc T (SubgroupFunctor.mem_range.mpr ⟨q, rfl⟩)
    T (𝟙 T) t
  simp only [AutomorphicAction.conjugation_act, Category.id_comp,
    Grp.comp_hom_hom, ← Category.assoc] at e
  rw [← (mul_inv_eq_iff_eq_mul.mp e), mul_inv_cancel_right]

variable (α : characterLattice S) {V : GroupScheme B}
    (j : V ⟶ H) (hj : (subgroup s α).IsRepresentedBy j)

/-- The actual root action induced by an ambient subgroup centralizing the torus. -/
def rootActionOfTorusCentralizer : AutomorphicAction K V :=
  rootActionOfFixesTorus (AutomorphicAction.ofNormalizedConjugation h a hn) s
    (fun _ q t => normalizedConjugation_fixes_torus h a hn s hc q t) α j hj

/-- Its representing inclusion into the ambient group intertwines actual conjugation. -/
theorem rootActionOfTorusCentralizer_act_comp {T : Over B}
    (q : T ⟶ K.X) (v : T ⟶ V.X) :
    (rootActionOfTorusCentralizer h a hn s hc α j hj).act q v ≫
        (j ≫ h).hom.hom =
      (q ≫ a.hom.hom) * (v ≫ (j ≫ h).hom.hom) * (q ≫ a.hom.hom)⁻¹ := by
  rw [Grp.comp_hom_hom, ← Category.assoc]
  change ((rootActionOfFixesTorus _ s _ α j hj).act q v ≫ j.hom.hom) ≫
    h.hom.hom = _
  rw [rootActionOfFixesTorus_act_comp]
  exact SubgroupFunctor.lift_comp_normalizedConjugation_comp h a hn q
    (v ≫ j.hom.hom)

end NormalizedConjugation

section Field

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H K V : GroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction K H) (s : S.toGrp ⟶ H)
    (hfix : ∀ (T : Over (Spec (CommRingCat.of k)))
      (q : T ⟶ K.X) (t : T ⟶ S.X), b.act q (t ≫ s.hom.hom) = t ≫ s.hom.hom)
    (α : characterLattice S) (j : V ⟶ H)
    (hj : (subgroup s α).IsRepresentedBy j)
    (hK : IsVectorGroupOfDimension K 1) (hV : IsVectorGroupOfDimension V 1)

include hfix hj hK hV

/-- A vector line fixing the torus acts trivially on a represented vector root line. -/
theorem act_root_eq_of_vectorLines {T : Over (Spec (CommRingCat.of k))}
    (q : T ⟶ K.X) (v : T ⟶ V.X) :
    b.act q (v ≫ j.hom.hom) = v ≫ j.hom.hom := by
  have he := AutomorphicAction.eq_trivial_of_vectorLines
    (rootActionOfFixesTorus b s hfix α j hj) hK hV
  rw [← rootActionOfFixesTorus_act_comp b s hfix α j hj, he,
    AutomorphicAction.trivial_act]

/-- The entire intrinsic root functor is fixed on every refinement. -/
theorem subgroup_le_fixedSubgroup_of_vectorLines :
    subgroup s α ≤ b.fixedSubgroup := by
  intro T g hg W c q
  have hg' : c ≫ g ∈ (subgroup s α).carrier W :=
    (subgroup s α).comp_mem c hg
  rw [← hj.2] at hg'
  obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hg'
  rw [← hv]
  exact act_root_eq_of_vectorLines b s hfix α j hj hK hV q v

end Field

section AmbientField

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H K V : GroupScheme (Spec (CommRingCat.of k))}
    (h : H ⟶ G) (a : K ⟶ G)
    (hn : (SubgroupFunctor.range h).IsNormalizedBy (SubgroupFunctor.range a))
    [Mono h.hom.hom] (s : S.toGrp ⟶ H)
    (hc : SubgroupFunctor.range a ≤
      (AutomorphicAction.conjugation (s ≫ h)).fixedSubgroup)
    (α : characterLattice S) (j : V ⟶ H)
    (hj : (subgroup s α).IsRepresentedBy j)
    (hK : IsVectorGroupOfDimension K 1) (hV : IsVectorGroupOfDimension V 1)

include hn hc hj hK hV

/-- An ambient vector line centralizing the torus centralizes each represented vector root line. -/
theorem range_root_comp_le_centralizer_of_vectorLines :
    SubgroupFunctor.range (j ≫ h) ≤
      (AutomorphicAction.conjugation a).fixedSubgroup := by
  have he := AutomorphicAction.eq_trivial_of_vectorLines
    (rootActionOfTorusCentralizer h a hn s hc α j hj) hK hV
  intro T x hx W c q
  obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have e := rootActionOfTorusCentralizer_act_comp h a hn s hc α j hj q (c ≫ v)
  rw [he, AutomorphicAction.trivial_act] at e
  simpa only [AutomorphicAction.conjugation_act, Category.assoc] using e.symm

end AmbientField

end Langlands.GroupScheme.RelativeRoot
