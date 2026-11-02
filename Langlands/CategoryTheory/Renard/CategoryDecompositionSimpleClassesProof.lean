import Langlands.CategoryTheory.Renard.CategoryDecompositionSimpleClassesStatements

/-!
# Renard A.IX: internal simplicity and the partition of simple classes

This proof uses the actual cofans supplied by `IsCategoryDecomposition`.
The generality beyond the source's Grothendieck/AB6 setting is derived.
-/

universe w v u

open CategoryTheory Limits

namespace Langlands.Renard
namespace CategoryDecompositionSimpleClassesProof

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type w} {P : I → ObjectProperty C}

/-- Every leg of an actual coproduct cofan is a split monomorphism. -/
theorem cofan_leg_mono {Y : I → C} {T : C} {ι : ∀ i, Y i ⟶ T}
    (hc : IsColimit (Cofan.mk T ι)) (i : I) : Mono (ι i) := by
  classical
  let r : T ⟶ Y i := Cofan.IsColimit.desc hc
    (fun j => if h : j = i then eqToHom (congrArg Y h) else 0)
  have hr : ι i ≫ r = 𝟙 (Y i) := by
    change (Cofan.mk T ι).inj i ≫ Cofan.IsColimit.desc hc _ = _
    rw [Cofan.IsColimit.fac]
    simp
  have : IsSplitMono (ι i) := IsSplitMono.mk' ⟨r, hr⟩
  infer_instance

/-- Decomposing ambient test objects shows that internal monos remain mono. -/
theorem mono_hom (hP : IsCategoryDecomposition P) (i : I)
    {X Z : (P i).FullSubcategory} (f : X ⟶ Z) [Mono f] : Mono f.hom := by
  constructor
  intro T g h heq
  obtain ⟨Y, ι, hY, ⟨hc⟩⟩ := hP.1 T
  apply Cofan.IsColimit.hom_ext hc g h
  intro j
  by_cases hji : j = i
  · subst j
    have hcomp :
        (ObjectProperty.homMk (ι i ≫ g) : (⟨Y i, hY i⟩ : (P i).FullSubcategory) ⟶ X) ≫ f =
        ObjectProperty.homMk (ι i ≫ h) ≫ f := by
      apply ObjectProperty.hom_ext
      change (ι i ≫ g) ≫ f.hom = (ι i ≫ h) ≫ f.hom
      simpa only [Category.assoc] using congrArg (fun k => ι i ≫ k) heq
    exact congrArg (fun k => k.hom) ((cancel_mono f).mp hcomp)
  · exact (hP.2 j i hji (Y j) X.obj (hY j) X.property (ι j ≫ g)).trans
      (hP.2 j i hji (Y j) X.obj (hY j) X.property (ι j ≫ h)).symm

/-- Simplicity in a component agrees with simplicity in the ambient category. -/
theorem simple_iff (hP : IsCategoryDecomposition P) (i : I)
    (X : (P i).FullSubcategory) : Simple X ↔ Simple X.obj := by
  constructor
  · intro hX
    have := hX
    have hid : 𝟙 X.obj ≠ 0 := by
      intro hz
      apply id_nonzero X
      apply ObjectProperty.hom_ext
      exact hz
    constructor
    intro T f hf
    constructor
    · intro hiso hz
      apply hid
      have := hiso
      rw [← IsIso.inv_hom_id f]
      simp only [hz, comp_zero]
    · intro hnonzero
      obtain ⟨Y, ι, hY, ⟨hc⟩⟩ := hP.1 T
      have hleg : ι i ≫ f ≠ 0 := by
        intro hz
        apply hnonzero
        apply Cofan.IsColimit.hom_ext hc f 0
        intro j
        by_cases hji : j = i
        · subst j
          simpa only [cofan_mk_inj, comp_zero] using hz
        · simpa only [cofan_mk_inj, comp_zero] using
            hP.2 j i hji (Y j) X.obj (hY j) X.property (ι j ≫ f)
      have : Mono (ι i) := cofan_leg_mono hc i
      let g : (⟨Y i, hY i⟩ : (P i).FullSubcategory) ⟶ X :=
        ObjectProperty.homMk (ι i ≫ f)
      have : Mono g := (P i).ι.mono_of_mono_map (by
        change Mono (ι i ≫ f)
        infer_instance)
      have hg : g ≠ 0 := by
        intro hz
        apply hleg
        exact congrArg (fun k => k.hom) hz
      have : IsIso g := isIso_of_mono_of_nonzero hg
      have : IsIso (ι i ≫ f) := by
        change IsIso g.hom
        infer_instance
      have : Epi f := epi_of_epi (ι i) f
      exact isIso_of_mono_of_epi f
  · intro hX
    have := hX
    constructor
    intro Y f hf
    have : Mono f.hom := mono_hom hP i f
    rw [← ObjectProperty.isIso_hom_iff, Simple.mono_isIso_iff_nonzero]
    constructor
    · intro h hz
      exact h (congrArg (fun k => k.hom) hz)
    · intro h hz
      apply h
      exact (P i).hom_ext hz

/-- The exact published internal/ambient simplicity constituent. -/
theorem simplicity (C : Type u) [Category.{v} C] [Abelian C] :
    CategoryDecompositionSimplicityStatement.{w} C := by
  intro I P hP i X
  exact simple_iff hP i X

/-- The exact published partition of ambient simple classes by component index. -/
theorem partition (C : Type u) [Category.{v} C] [Abelian C] :
    CategoryDecompositionSimplePartitionStatement.{w} C := by
  classical
  intro I P hP q
  constructor
  · rintro ⟨T, hT, hq⟩
    have := hT
    obtain ⟨Y, ι, hY, ⟨hc⟩⟩ := hP.1 T
    have hleg : ∃ i, ι i ≠ 0 := by
      by_contra hn
      push Not at hn
      apply id_nonzero T
      apply Cofan.IsColimit.hom_ext hc (𝟙 T) 0
      intro i
      simp only [cofan_mk_inj, hn i, zero_comp]
    obtain ⟨i, hi⟩ := hleg
    have : Mono (ι i) := cofan_leg_mono hc i
    have : IsIso (ι i) := isIso_of_mono_of_nonzero hi
    have hsimple : Simple (Y i) := Simple.of_iso (asIso (ι i))
    have hclass : objectClass (Y i) = q :=
      (objectClass_eq_iff.mpr ⟨asIso (ι i)⟩).trans hq
    refine ⟨i, ⟨⟨Y i, hY i⟩, (simple_iff hP i _).mpr hsimple, hclass⟩, ?_⟩
    rintro j ⟨X, hX, hXq⟩
    by_contra hji
    have : Simple X.obj := (simple_iff hP j X).mp hX
    obtain ⟨e⟩ := objectClass_eq_iff.mp (hXq.trans hclass.symm)
    have hz : e.hom = 0 := hP.2 j i hji X.obj (Y i) X.property (hY i) e.hom
    apply id_nonzero X.obj
    simpa only [hz, zero_comp] using e.hom_inv_id.symm
  · rintro ⟨i, ⟨X, hX, hq⟩, _⟩
    exact ⟨X.obj, (simple_iff hP i X).mp hX, hq⟩

/-- Renard A.IX, first assertion: the complete unchanged aggregate target. -/
theorem simpleClasses (C : Type u) [Category.{v} C] [Abelian C] :
    CategoryDecompositionSimpleClassesStatement.{w} C :=
  ⟨simplicity C, partition C⟩

end CategoryDecompositionSimpleClassesProof
end Langlands.Renard
