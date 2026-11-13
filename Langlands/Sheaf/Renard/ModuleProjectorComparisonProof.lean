import Langlands.Sheaf.Renard.ModuleProjectorComparisonStatement

/-!
# Proof: the original-module comparison is an isomorphism

Renard (9 July 2026), II.2.5, end of the proof of the Theorem, printed p.40 / PDF p.46:
`M_c(X) = ⋃_U χ_U · M = M`. The comparison `m ↦ (χ_U · m)_U` is bijective:

* injective, because a compact open `K` with `χ_K · (m - n) = m - n` exists by
  nondegeneracy, and the component at `K` of the image of `m - n` is `χ_K · (m - n)`;
* surjective, because a compactly supported section `t` has its support in a compact open
  `K`; its component `t_K` is sent to a section agreeing with `t` on `K` (compatibility of
  the projector family) and vanishing off `K`, like `t`.

A bijective morphism of nondegenerate modules is an isomorphism, its inverse being again
test-linear.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.ModuleProjectorComparison

open CategoryTheory TopologicalSpace Opposite
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Renard.ProjectorBasisSheaf Langlands.Sheaf.Renard.ProjectorVectorSheaf
open Langlands.Sheaf.Renard.CompactSectionTestModule

universe u v

/-- A morphism of nondegenerate modules whose underlying map is bijective is an
isomorphism: the inverse map is again additive and test-linear. -/
theorem isIso_homMk_of_bijective {A : Type u} [NonUnitalRing A]
    {M N : NondegenerateModuleCat.{u, v} A} (f : NonUnitalModuleHom A M.obj N.obj)
    (hf : Function.Bijective f) : IsIso (ObjectProperty.homMk f : M ⟶ N) := by
  let e : M.obj ≃+ N.obj := AddEquiv.ofBijective f.toAddMonoidHom hf
  have he : ∀ n : N.obj, f (e.symm n) = n := fun n => e.apply_symm_apply n
  let g : NonUnitalModuleHom A N.obj M.obj :=
    { toAddMonoidHom := e.symm.toAddMonoidHom
      map_smul' := fun a n => by
        apply hf.1
        change f (e.symm (a • n)) = f (a • e.symm n)
        rw [NonUnitalModuleHom.map_smul, he, he] }
  refine ⟨⟨ObjectProperty.homMk g, ?_, ?_⟩⟩
  · apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    exact e.symm_apply_apply m
  · apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro n
    exact he n

variable {X : Type} [TopologicalSpace X] (hX : Langlands.Topology.IsLocallyProfinite X)

section Original

variable {M : Type} [AddCommGroup M] [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)

/-- Injectivity of `m ↦ (χ_U · m)_U`: some compact open `K` fixes `m - n`, and the
component at `K` of its image is `χ_K · (m - n)`. -/
theorem compactOriginal_injective :
    letI := originalModule hM
    Function.Injective (compactOriginal hX hM) := by
  let _ := originalModule hM
  intro m n h
  obtain ⟨K, hK⟩ := exists_compactOpen_action_eq hX hM (m - n)
  have hc : action hX M K m = action hX M K n :=
    congrArg (fun t => ((t.val.val ⟨K, le_top⟩).val : M)) h
  rw [← sub_eq_zero, ← hK, map_sub, hc, sub_self]

/-- Surjectivity of `m ↦ (χ_U · m)_U`: a compactly supported section `t` has its support in
a compact open `K`, and it is the image of its component `t_K`. -/
theorem compactOriginal_surjective :
    letI := originalModule hM
    Function.Surjective (compactOriginal hX hM) := by
  let _ := originalModule hM
  intro t
  obtain ⟨V, hVo, hVc, htV⟩ := exists_compactOpen_superset hX.2 t.2
  let K : CompactOpen hX := ⟨⟨V, hVo⟩, hVc⟩
  let tK : Value hX M K := t.val.val ⟨K, le_top⟩
  refine ⟨tK.val, ?_⟩
  apply Subtype.ext
  change originalSection.{0, 0} hX hM ⊤ tK.val = t.val
  apply VectorSheafScalars.ext_germ (sheaf.{0, 0} hX hM)
  intro x _
  change (presheaf.{0, 0} hX hM).Γgerm x _ = (presheaf.{0, 0} hX hM).Γgerm x _
  by_cases hx : x ∈ V
  · have hres (s : (presheaf.{0, 0} hX hM).obj (op ⊤)) :
        (presheaf.{0, 0} hX hM).Γgerm x s = (presheaf.{0, 0} hX hM).germ K.obj x hx
          ((presheaf.{0, 0} hX hM).map (homOfLE (le_top : K.obj ≤ ⊤)).op s) :=
      (TopCat.Presheaf.Γgerm_res_apply _ x hx s).symm
    rw [hres, hres]
    congr 1
    apply section_ext hX hM
    intro U
    exact congrArg Subtype.val
      (section_compatible hX hM t.val ⟨K, le_top⟩ ⟨U.val, le_top⟩ U.property)
  · have h1 : (presheaf.{0, 0} hX hM).Γgerm x t.val = 0 := by
      by_contra h
      exact hx (htV h)
    have h2 : (presheaf.{0, 0} hX hM).Γgerm x (originalSection.{0, 0} hX hM ⊤ tK.val) = 0 := by
      by_contra h
      exact hx (support_originalSection_subset hX hM K tK.val (value_fixed hX M tK) h)
    rw [h1, h2]

end Original

/-- The comparison `m ↦ (χ_U · m)_U` is bijective. -/
theorem moduleComparisonHom_bijective
    (M : NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier X)) :
    Function.Bijective (moduleComparisonHom hX M) :=
  ⟨compactOriginal_injective hX M.property, compactOriginal_surjective hX M.property⟩

/-- Renard II.2.5, end of the proof of the Theorem: for every nondegenerate test module `M`
on a t.d. space, the comparison `M ⟶ Γc(P M)`, `m ↦ (χ_U · m)_U`, is an isomorphism. -/
theorem moduleComparisonIsIso : ModuleComparisonIsIso := by
  intro X _ hX M
  exact isIso_homMk_of_bijective
    (N := (ProjectorVectorSheaf.functor.{0, 0} hX ⋙ compactSectionFunctor hX).obj M)
    (moduleComparisonHom hX M) (moduleComparisonHom_bijective hX M)

end Langlands.Sheaf.Renard.ModuleProjectorComparison
