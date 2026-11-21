import Langlands.GroupScheme.Unipotent.DiagonalizableSmoothUnipotentCocycle
import Langlands.GroupScheme.Rational.QuotientHomCocycle
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Trigonalizable.SectionConjugacySmoothStatement
import Langlands.GroupScheme.Trigonalizable.ExtensionSplitAlgClosed

/-! # Conjugacy of sections of trigonalizable groups with smooth unipotent part -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace TrigonalizableSectionConjugacySmooth

variable {k : Type u} [Field k]

local notation "T₀" => Over.mk (𝟙 (Spec (CommRingCat.of k)))

section Conjugation

variable {G U Q : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ G) (q : G ⟶ Q)
    (hn : SubgroupFunctor.range i = SubgroupFunctor.range (kernelι q))

include hn in
/-- The subgroup is killed by the quotient map. -/
theorem comp_eq_one : i.hom.hom ≫ q.hom.hom = 1 := by
  have h : i.hom.hom ∈ (SubgroupFunctor.range (kernelι q)).carrier U.X := by
    rw [← hn]
    exact SubgroupFunctor.mem_range.2 ⟨𝟙 _, Category.id_comp _⟩
  exact (mem_range_kernelι_iff q _).1 h

include hn in
/-- Conjugation by a rational point of the kernel does not change the quotient map. -/
theorem innerIso_hom_comp (u : T₀ ⟶ U.X) : (G.innerIso (u ≫ i.hom.hom)).hom ≫ q = q := by
  apply GroupScheme.hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp]
  have hc : G.constantPoint (u ≫ i.hom.hom) T ≫ q.hom.hom = 1 := by
    simp only [GroupScheme.constantPoint, Category.assoc, comp_eq_one i q hn, MonObj.comp_one]
  rw [hc]
  group

include hn in
/-- Over an algebraically closed field, two homomorphisms from a diagonalizable group with
finitely generated character group to `G` that have the same composite with `q` are conjugate
by a rational point of the smooth unipotent kernel `U`. -/
theorem exists_conj_of_comp_eq [IsAlgClosed k]
    [Mono i.hom.hom] [Smooth U.X.hom] [IsAffineHom U.X.hom] (hU : IsUnipotent U)
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (i₀ i₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G)
    (h : i₀ ≫ q = i₁ ≫ q) :
    ∃ u : T₀ ⟶ U.X, i₀ ≫ (G.innerIso (u ≫ i.hom.hom)).hom = i₁ := by
  obtain ⟨v, hv⟩ := diagonalizableSmoothUnipotentCocycle.exists_coboundary k Λ U hU
    (QuotientHomCocycle.action i q hn i₀) (QuotientHomCocycle.cocycle i q hn i₀ i₁ h)
  exact ⟨v, (QuotientHomCocycle.cocycle_eq_coboundary_iff i q hn i₀ i₁ h v).1 hv⟩

include hn in
/-- A homomorphism `j` from a group isomorphic to a diagonalizable group is conjugate, by a
rational point of `U`, to its composite with `q` and a section `s` of `q`. -/
theorem exists_eq_comp_inner [IsAlgClosed k]
    [Mono i.hom.hom] [Smooth U.X.hom] [IsAffineHom U.X.hom] (hU : IsUnipotent U)
    {S : GroupScheme (Spec (CommRingCat.of k))} (j : S ⟶ G)
    (hS : ∃ (Λ' : Type u) (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ'),
      Nonempty (S ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp))
    (s : Q ⟶ G) (hs : s ≫ q = 𝟙 Q) :
    ∃ u : T₀ ⟶ U.X, j = j ≫ q ≫ s ≫ (G.innerIso (u ≫ i.hom.hom)).hom := by
  obtain ⟨Λ', _, _, ⟨e⟩⟩ := hS
  have h : (e.inv ≫ j ≫ q ≫ s) ≫ q = (e.inv ≫ j) ≫ q := by
    simp only [Category.assoc, hs, Category.comp_id]
  obtain ⟨u, hu⟩ := exists_conj_of_comp_eq i q hn hU Λ' _ _ h
  refine ⟨u, ?_⟩
  calc
    j = e.hom ≫ e.inv ≫ j := by rw [e.hom_inv_id_assoc]
    _ = e.hom ≫ (e.inv ≫ j ≫ q ≫ s) ≫ (G.innerIso (u ≫ i.hom.hom)).hom := by rw [hu]
    _ = j ≫ q ≫ s ≫ (G.innerIso (u ≫ i.hom.hom)).hom := by
      simp only [Category.assoc, e.hom_inv_id_assoc]

include hn in
/-- If the range of a section `s` of `q` lies in the range of a homomorphism `j'` from a group
isomorphic to a diagonalizable group, the reverse inclusion also holds. -/
theorem range_le_range_section [IsAlgClosed k]
    [Mono i.hom.hom] [Smooth U.X.hom] [IsAffineHom U.X.hom] (hU : IsUnipotent U)
    {S' : GroupScheme (Spec (CommRingCat.of k))} (j' : S' ⟶ G)
    (hS' : ∃ (Λ' : Type u) (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ'),
      Nonempty (S' ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp))
    (s : Q ⟶ G) (hs : s ≫ q = 𝟙 Q)
    (hle : SubgroupFunctor.range s ≤ SubgroupFunctor.range j') :
    SubgroupFunctor.range j' ≤ SubgroupFunctor.range s := by
  obtain ⟨u, hu⟩ := exists_eq_comp_inner i q hn hU j' hS' s hs
  have hsq : s.hom.hom ≫ q.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, hs]
    rfl
  -- every point of the range of `j'` is the conjugate of its image under `q ≫ s`
  have key : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range j').carrier T →
        x = G.constantPoint (u ≫ i.hom.hom) T * (x ≫ q.hom.hom ≫ s.hom.hom) *
          (G.constantPoint (u ≫ i.hom.hom) T)⁻¹ := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    have e := congrArg (fun f : S' ⟶ G => y ≫ f.hom.hom) hu
    simp only [Grp.comp_hom_hom] at e
    conv_lhs => rw [e]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, comp_innerIso_hom]
    simp only [Category.assoc]
  rw [SubgroupFunctor.le_def]
  intro T x hx
  have hsx : x ≫ q.hom.hom ≫ s.hom.hom ∈ (SubgroupFunctor.range j').carrier T :=
    hle T (SubgroupFunctor.mem_range.2 ⟨x ≫ q.hom.hom, Category.assoc _ _ _⟩)
  have h1 := key T _ hsx
  rw [Category.assoc, Category.assoc, ← Category.assoc s.hom.hom, hsq, Category.id_comp] at h1
  have h2 := key T x hx
  rw [← h1] at h2
  exact SubgroupFunctor.mem_range.2 ⟨x ≫ q.hom.hom, by rw [Category.assoc]; exact h2.symm⟩

end Conjugation
end TrigonalizableSectionConjugacySmooth

open TrigonalizableSectionConjugacySmooth in
/-- **Milne 16.27 with smooth unipotent part (SGA 3 XVII 5.1.1 ii) b) for part (a)).**
Sections are conjugate by a rational point of the kernel, and the maximal closed
diagonalizable subgroups are exactly the ranges of sections. -/
theorem trigonalizableSectionConjugacySmooth : TrigonalizableSectionConjugacySmoothStatement.{u} := by
  intro k _ _ G _ _ U i Λ _ _ q hi _ hU hnorm hq
  have : Mono i.hom.hom := hi.mono_overHom
  have : IsAffineHom U.X.hom := by
    have : IsClosedImmersion i.hom.hom.left := hi
    rw [← Over.w i.hom.hom]
    infer_instance
  have hn : SubgroupFunctor.range i = SubgroupFunctor.range (kernelι q) := hq.2.2.2.symm
  -- a homomorphic section of a homomorphism out of an affine group is a closed subgroup
  have hclosed : ∀ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G,
      s ≫ q = 𝟙 _ → IsClosedSubgroup s := by
    intro s hs
    change IsClosedImmersion s.hom.hom.left
    have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    have he : s.hom.hom.left ≫ q.hom.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, ← Grp.comp_hom_hom, hs, Grp.id_hom_hom, Over.id_left]
    have : IsClosedImmersion (s.hom.hom.left ≫ q.hom.hom.left) := by
      rw [he]
      infer_instance
    exact IsClosedImmersion.of_comp _ q.hom.hom.left
  refine ⟨fun s₁ s₂ h₁ h₂ => ?_, fun S j hj hS => ⟨fun hmax => ?_, ?_⟩⟩
  · -- (a) sections are conjugate
    obtain ⟨u, hu⟩ := exists_conj_of_comp_eq i q hn hU Λ s₁ s₂ (h₁.trans h₂.symm)
    exact ⟨u, hu.symm⟩
  · -- (b), maximal implies the range of a section
    obtain ⟨s₀, hs₀⟩ := TrigonalizableExtensionSplit.exists_section_of_isAlgClosed i q hi hU hnorm hq
    obtain ⟨u, hu⟩ := exists_eq_comp_inner i q hn hU j hS s₀ hs₀
    have hs : (s₀ ≫ (G.innerIso (u ≫ i.hom.hom)).hom) ≫ q = 𝟙 _ := by
      rw [Category.assoc, TrigonalizableSectionConjugacySmooth.innerIso_hom_comp i q hn, hs₀]
    refine ⟨_, hs, hmax _ _ (hclosed _ hs) ⟨Λ, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩ ?_⟩
    rw [SubgroupFunctor.le_def]
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    refine SubgroupFunctor.mem_range.2 ⟨y ≫ j.hom.hom ≫ q.hom.hom, ?_⟩
    have e := congrArg (fun f : S ⟶ G => y ≫ f.hom.hom) hu
    simp only [Grp.comp_hom_hom] at e
    rw [e]
    simp only [Grp.comp_hom_hom, Category.assoc]
  · -- (b), the range of a section is maximal
    rintro ⟨s, hs, hrange⟩ S' j' _ hS' hle
    rw [hrange] at hle ⊢
    exact le_antisymm hle (range_le_range_section i q hn hU j' hS' s hs hle)

end Langlands.GroupScheme
