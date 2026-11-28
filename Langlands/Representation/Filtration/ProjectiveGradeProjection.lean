import Langlands.Representation.Filtration.ActualGradedExtraction
import Langlands.Representation.Filtration.HomVanishingFiltration
import Langlands.Representation.CuspidalSupport.InducedProgeneratorEndBasis

/-! # A split projection onto one grade of a projectively filtered object -/

noncomputable section

open CategoryTheory

namespace Langlands.ObjectRepFiltration

universe uR uG uV

variable {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]
  {B A : SmoothRep.{uR, uG, uV} R G} {n : ℕ}

/-- A grade isomorphic to `A` in a finite filtration by projective grades gives a split
projection to `A`. If all other grades have zero Hom to `X`, every map to `X` factors
uniquely through this projection. -/
theorem exists_splitProjection_of_projectiveGrades
    (s : ObjectRepFiltration B.obj n) (j : Fin n) (e : s.smoothGradedObject j ≅ A)
    (hproj : ∀ i, Projective (s.smoothGradedObject i)) :
    ∃ (p : B ⟶ A) (a : A ⟶ B), a ≫ p = 𝟙 A ∧
      ∀ X : SmoothRep.{uR, uG, uV} R G,
        (∀ i ≠ j, ∀ h : s.smoothGradedObject i ⟶ X, h = 0) →
        Function.Bijective (fun h : A ⟶ X => p ≫ h) := by
  let pt := Discrete.mk PUnit.unit
  have hs (i : Fin n) : ∃ t : s.gradedRepresentation i ⟶ (s.step i.succ).representation pt,
      t ≫ s.gradedProjection i = 𝟙 _ := by
    let := hproj i
    exact SmoothRep.exists_section_of_projective
      (SmoothRep.subrepresentation B (s.subrepresentation i.succ)).isSmooth
      (s.gradedProjection i) (s.gradedProjection_surjective i)
      (s.smoothGradedObject i) (Iso.refl _)
  choose t ht using hs
  let aR (i : Fin n) : s.gradedRepresentation i ⟶ B.obj :=
    t i ≫ (s.step i.succ).inclusion.app pt
  have hdetect {X : Rep.{uV} R G} (f : B.obj ⟶ X) (hf : ∀ i, aR i ≫ f = 0) : f = 0 := by
    have hstep (k : Fin (n + 1)) : f ∈ s.homVanishing pt X k := by
      induction k using Fin.induction with
      | zero => simp [s.homVanishing_zero]
      | succ i ih =>
        apply (s.gradedDescent_eq_zero_iff pt X i f ih).mp
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        change s.gradedRepresentation i at x
        let d : s.gradedRepresentation i ⟶ X := s.gradedDescent pt X i f ih
        have hx := congrArg (fun f => f.hom x) (ht i)
        change (s.gradedProjection i).hom ((t i).hom x) = x at hx
        have hd := s.gradedDescent_projection pt X i f ih ((t i).hom x)
        change d.hom ((s.gradedProjection i).hom ((t i).hom x)) = (aR i ≫ f).hom x at hd
        exact (congrArg d.hom hx).symm.trans (hd.trans (congrArg (fun f => f.hom x) (hf i)))
    have h := hstep (Fin.last n)
    rw [s.homVanishing_last, AddSubgroup.mem_bot] at h
    exact h
  let eR : s.gradedRepresentation j ≅ A.obj := SmoothRep.toRep.mapIso e
  obtain ⟨pR, hp⟩ := s.exists_extension_of_sections pt A.obj
    (fun i => ⟨t i, ht i⟩) j.succ (s.gradedProjection j ≫ eR.hom)
  change B.obj ⟶ A.obj at pR
  have hpa : aR j ≫ pR = eR.hom := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun f => f.hom x) (ht j)
    change (s.gradedProjection j).hom ((t j).hom x) = x at hx
    change pR.hom ((t j).hom x).val = eR.hom.hom x
    rw [hp]
    change eR.hom.hom ((s.gradedProjection j).hom ((t j).hom x)) = eR.hom.hom x
    rw [hx]
  let p : B ⟶ A := SmoothRep.toRep.preimage pR
  let a : A ⟶ B := SmoothRep.toRep.preimage (eR.inv ≫ aR j)
  have hsplit : a ≫ p = 𝟙 A := by
    apply SmoothRep.toRep.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, p, a]
    change (eR.inv ≫ aR j) ≫ pR = 𝟙 A.obj
    rw [Category.assoc, hpa, eR.inv_hom_id]
  refine ⟨p, a, hsplit, fun X hzero => ⟨?_, ?_⟩⟩
  · intro f g hfg
    simpa only [← Category.assoc, hsplit, Category.id_comp] using congrArg (fun f => a ≫ f) hfg
  · intro f
    refine ⟨a ≫ f, ?_⟩
    apply SmoothRep.toRep.map_injective
    apply sub_eq_zero.mp
    apply hdetect
    intro i
    simp only [Preadditive.comp_sub, Functor.map_comp]
    by_cases hi : i = j
    · subst i
      simp only [a, p, Functor.map_preimage, ← Category.assoc, hpa]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, sub_self]
    · have hvan (g : B.obj ⟶ X.obj) : aR i ≫ g = 0 := by
        let h : s.smoothGradedObject i ⟶ X := SmoothRep.toRep.preimage (aR i ≫ g)
        change (aR i ≫ g : SmoothRep.toRep.obj (s.smoothGradedObject i) ⟶
          SmoothRep.toRep.obj X) = 0
        simpa only [h, Functor.map_preimage, Functor.map_zero] using
          congrArg (SmoothRep.toRep.map) (hzero i hi h)
      simp only [hvan, sub_self]

end Langlands.ObjectRepFiltration
