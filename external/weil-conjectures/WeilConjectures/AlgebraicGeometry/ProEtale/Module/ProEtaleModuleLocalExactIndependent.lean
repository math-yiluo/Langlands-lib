/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Descent of local module exactness in independent universes

## References

* Stacks Project, Pro-etale Cohomology, Tag 09AH
* Modules on Sites, Tag 03DA
* Stacks Project, Pro-etale Cohomology, the final local exactness argument
* Modules on Sites, Tag 03DA, local lifting and the underlying abelian sheaf
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem module_epi_of_local_surjective {X : Scheme.{t}}
    [HasSheafify (ProEt.topology X) AddCommGrpCat.{max u (t + 1)}]
    [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)}]
    (R : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)})
    {F G : SheafOfModules.{max u (t + 1)} R} (a : F ⟶ G)
    (h : ∀ T : X.ProEt, ∃ (I : Type (t + 1)) (V : I → X.ProEt)
      (f : ∀ j, V j ⟶ T), Presieve.ofArrows V f ∈ ProEt.precoverage X T ∧
        ∀ j, Function.Surjective (a.val.app (op (V j)))) : Epi a := by
  let E := SheafOfModules.toSheaf R
  have hl : Sheaf.IsLocallySurjective (E.map a) := by
    constructor
    intro T s
    obtain ⟨I, V, f, hf, hs⟩ := h T
    apply (ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hf)
    rw [Sieve.generate_le_iff]
    rintro W g ⟨j⟩
    exact hs j (G.val.map (f j).op s)
  have : Epi (E.map a) := Sheaf.epi_of_isLocallySurjective (E.map a)
  constructor
  intro P s t hst
  apply E.map_injective
  apply (cancel_epi (E.map a)).mp
  simpa only [← E.map_comp] using congrArg E.map hst

private theorem module_epi_of_local_kernel_lifts {X : Scheme.{t}}
    [HasSheafify (ProEt.topology X) AddCommGrpCat.{max u (t + 1)}]
    [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)}]
    (R : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)})
    {F G H K : SheafOfModules.{max u (t + 1)} R}
    (a : F ⟶ G) (b : G ⟶ H) (ι : K ⟶ G) [Mono ι] (k : F ⟶ K)
    (hι : ι ≫ b = 0) (hk : k ≫ ι = a)
    (h : ∀ T : X.ProEt, ∃ (I : Type (t + 1)) (V : I → X.ProEt)
      (f : ∀ j, V j ⟶ T), Presieve.ofArrows V f ∈ ProEt.precoverage X T ∧
        ∀ j, Function.Exact (a.val.app (op (V j))) (b.val.app (op (V j)))) :
    Epi k := by
  apply module_epi_of_local_surjective R k
  intro T
  obtain ⟨I, V, f, hf, hj⟩ := h T
  refine ⟨I, V, f, hf, ?_⟩
  intro j s
  let E := SheafOfModules.evaluation R (op (V j))
  have hinj : Function.Injective (E.map ι) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hs : b.val.app _ (ι.val.app _ s) = 0 := by
    exact congrArg (fun z : K ⟶ H ↦ z.val.app _ s) hι
  obtain ⟨t, ht⟩ := (hj j _).mp hs
  refine ⟨t, ?_⟩
  apply hinj
  exact (congrArg (fun z : F ⟶ G ↦ z.val.app _ t) hk).trans ht

/-- Sectionwise short exactness on a pro-etale covering implies categorical
short exactness, with module universe independent of the scheme universe. -/
theorem proEtale_module_shortExact_of_local_sections_independent {X : Scheme.{t}}
    [HasSheafify (ProEt.topology X) AddCommGrpCat.{max u (t + 1)}]
    [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)}]
    (R : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)})
    {F G H : SheafOfModules.{max u (t + 1)} R} (a : F ⟶ G) (b : G ⟶ H)
    (h : ∀ T : X.ProEt, ∃ (I : Type (t + 1)) (V : I → X.ProEt)
      (f : ∀ j, V j ⟶ T), Presieve.ofArrows V f ∈ ProEt.precoverage X T ∧
        ∀ j, Function.Injective (a.val.app (op (V j))) ∧
          Function.Surjective (b.val.app (op (V j))) ∧
          Function.Exact (a.val.app (op (V j))) (b.val.app (op (V j)))) :
    Mono a ∧ Epi b ∧ (ComposableArrows.mk₂ a b).Exact := by
  have hinj (T : X.ProEt) : Function.Injective (a.val.app (op T)) := by
    intro s t hst
    obtain ⟨I, V, f, hf, hj⟩ := h T
    let K := (sheafCompose (ProEt.topology X)
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).obj
        ((SheafOfModules.toSheaf R).obj F)
    have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp K.property
    apply (hsh _ (Precoverage.generate_mem_toGrothendieck hf)).isSeparatedFor.ext
    rintro W g ⟨W', p, q, ⟨j⟩, rfl⟩
    change F.val.map (p ≫ f j).op s = F.val.map (p ≫ f j).op t
    rw [op_comp]
    simp only [PresheafOfModules.map_comp_apply]
    congr 1
    apply (hj j).1
    have hn (x : F.val.obj (op T)) :
        a.val.app (op (V j)) (F.val.map (f j).op x) =
          G.val.map (f j).op (a.val.app (op T) x) :=
      PresheafOfModules.naturality_apply a.val (f j).op x
    rw [hn, hn, hst]
  have ha : Mono a := by
    constructor
    intro P s t hst
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply hinj T.unop
    exact congrArg (fun k : P ⟶ G ↦ k.val.app T x) hst
  have hb : Epi b := module_epi_of_local_surjective R b (by
    intro T
    obtain ⟨I, V, f, hf, hj⟩ := h T
    exact ⟨I, V, f, hf, fun j ↦ (hj j).2.1⟩)
  have hz : a ≫ b = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨I, V, f, hf, hj⟩ := h T.unop
    let K := (sheafCompose (ProEt.topology X)
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).obj
        ((SheafOfModules.toSheaf R).obj H)
    have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp K.property
    apply (hsh _ (Precoverage.generate_mem_toGrothendieck hf)).isSeparatedFor.ext
    rintro W g ⟨W', p, q, ⟨j⟩, rfl⟩
    have hzj := ((hj j).2.2 (a.val.app (op (V j))
      (F.val.map (f j).op x))).mpr ⟨_, rfl⟩
    change H.val.map (p ≫ f j).op
      (b.val.app T (a.val.app T x)) = H.val.map (p ≫ f j).op 0
    rw [op_comp]
    simp only [PresheafOfModules.map_comp_apply]
    have hn : H.val.map (f j).op (b.val.app T (a.val.app T x)) = 0 := by
      rw [← PresheafOfModules.naturality_apply b.val (f j).op,
        ← PresheafOfModules.naturality_apply a.val (f j).op]
      exact hzj
    rw [hn]
    simp only [map_zero]
  let S := ShortComplex.mk a b hz
  have he : S.Exact := by
    apply S.exact_iff_epi_kernel_lift.mpr
    apply module_epi_of_local_kernel_lifts R a b (kernel.ι b) (kernel.lift b a hz)
      (kernel.condition b) (kernel.lift_ι b a hz)
    intro T
    obtain ⟨I, V, f, hf, hj⟩ := h T
    exact ⟨I, V, f, hf, fun j ↦ (hj j).2.2⟩
  exact ⟨ha, hb, S.exact_iff_exact_toComposableArrows.mp he⟩

end AlgebraicGeometry.Scheme
