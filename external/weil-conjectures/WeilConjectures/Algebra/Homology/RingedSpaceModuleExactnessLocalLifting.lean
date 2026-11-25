/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Local lifting for epimorphisms and exact complexes of module sheaves

Source: Stacks Project, Modules, Section 01AF and Lemma 01AG; Sheaves, Definition
007U and Lemma 0H7H (blueprint: lem-weil-pbc-ringed-space-module-exactness-local-lifting).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

private theorem kernel_sections (X : RingedSpace.{u})
    (F G : SheafOfModules.{u} (moduleRings X)) (φ : F ⟶ G) (W : Opens X) :
    Set.range (ConcreteCategory.hom ((kernel.ι φ).val.app (op W))) =
      {g | φ.val.app (op W) g = 0} := by
  let E := SheafOfModules.evaluation (moduleRings X) (op W)
  have he := (ShortComplex.kernelSequence_exact φ).map_of_mono_of_preservesKernel E
    inferInstance inferInstance
  apply Set.ext
  intro g
  constructor
  · rintro ⟨k, rfl⟩
    exact ((ShortComplex.kernelSequence φ).map E).moduleCat_zero_apply k
  · intro hg
    exact (((ShortComplex.kernelSequence φ).map E).moduleCat_exact_iff.mp he) g hg

private theorem local_lifts_iff_epi (X : RingedSpace.{u})
    (F G : SheafOfModules.{u} (moduleRings X)) (φ : F ⟶ G) :
    (∀ (W : Opens X) (t : G.val.obj (op W)),
      ∃ (I : Type u) (V : I → Opens X) (hV : ∀ i, V i ≤ W)
        (g : ∀ i, F.val.obj (op (V i))),
        (⨆ i, V i) = W ∧ ∀ i, φ.val.app (op (V i)) (g i) =
          G.val.map (homOfLE (hV i)).op t) ↔ Epi φ := by
  let T := SheafOfModules.toSheaf.{u} (moduleRings X)
  have he : Epi (T.map φ) ↔ Epi φ := T.epi_map_iff_epi φ
  rw [← he, ← TopCat.Sheaf.isLocallySurjective_iff_epi]
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  constructor
  · intro h W t x hx
    obtain ⟨I, V, hV, g, hcover, hg⟩ := h W t
    have hx' : x ∈ ⨆ i, V i := by rw [hcover]; exact hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
    exact ⟨V i, hV i, ⟨g i, hg i⟩, hi⟩
  · intro h W t
    classical
    choose V hV hlift hx using fun x : W ↦ h W t x.val x.property
    choose g hg using hlift
    refine ⟨W, V, hV, g, ?_, hg⟩
    apply le_antisymm (iSup_le hV)
    intro x hxW
    exact Opens.mem_iSup.mpr ⟨⟨x, hxW⟩, hx ⟨x, hxW⟩⟩

/--
Source: Stacks Project, Modules, Section 01AF and Lemma 01AG; Sheaves, Definition
007U and Lemma 0H7H (blueprint: lem-weil-pbc-ringed-space-module-exactness-local-lifting).

The category of modules on a ringed space is abelian (Mathlib's
`SheafOfModules.instAbelian`) and its kernels are computed sectionwise.
Epimorphisms are exactly the maps admitting local lifts of sections, and exactness
at the middle term of a complex is exactly local lifting of sections annihilated by
the second map.

Proof:
1. Evaluation preserves kernels. Map the exact kernel sequence to the category of
   modules on each open and apply `ShortComplex.moduleCat_exact_iff`.
2. `Preadditive.epi_iff_isZero_cokernel` gives the zero-cokernel characterization.
3. Forgetting to abelian sheaves preserves colimits and hence epimorphisms, by
   `SheafOfModules.preservesFiniteColimits_toSheaf` (Stacks, Modules on Sites, 03DB
   and 03CO). It reflects epimorphisms because it is faithful. Apply Mathlib's
   `TopCat.Sheaf.isLocallySurjective_iff_epi`. Its pointwise neighborhood condition
   is equivalent to the stated covering condition: a cover gives a neighborhood of
   each point, and chosen neighborhoods indexed by the points of W cover W.
4. Factor χ as F → kernel φ → G. `ShortComplex.exact_iff_epi_kernel_lift` identifies
   exactness with the first map being epi; apply step 3 to this map.
5. Step 1 lifts each section killed by φ to a kernel section. Naturality of the kernel
   inclusion translates restrictions, and its sectionwise injectivity translates
   the local lifting equations in both directions.
-/
theorem module_exactness_local_lifting (X : RingedSpace.{u}) :
    (∀ (F G : SheafOfModules.{u} (moduleRings X)) (φ : F ⟶ G) (W : Opens X),
        Set.range (ConcreteCategory.hom ((kernel.ι φ).val.app (op W))) =
          {g | φ.val.app (op W) g = 0}) ∧
      (∀ (F G : SheafOfModules.{u} (moduleRings X)) (φ : F ⟶ G),
        (Epi φ ↔ IsZero (cokernel φ)) ∧
        ((∀ (W : Opens X) (t : G.val.obj (op W)),
          (∃ (I : Type u) (V : I → Opens X) (hV : ∀ i, V i ≤ W)
              (g : ∀ i, F.val.obj (op (V i))),
              (⨆ i, V i) = W ∧
                ∀ i, φ.val.app (op (V i)) (g i) =
                  G.val.map (homOfLE (hV i)).op t)) ↔ Epi φ)) ∧
      (∀ (F G H : SheafOfModules.{u} (moduleRings X))
          (χ : F ⟶ G) (φ : G ⟶ H) (h : χ ≫ φ = 0),
        (ShortComplex.mk χ φ h).Exact ↔
          ∀ (W : Opens X) (g : G.val.obj (op W)),
            φ.val.app (op W) g = 0 →
              ∃ (I : Type u) (V : I → Opens X) (hV : ∀ i, V i ≤ W)
                (f : ∀ i, F.val.obj (op (V i))),
                (⨆ i, V i) = W ∧
                  ∀ i, χ.val.app (op (V i)) (f i) =
                    G.val.map (homOfLE (hV i)).op g) := by
  refine ⟨kernel_sections X, ?_, ?_⟩
  · intro F G φ
    exact ⟨Preadditive.epi_iff_isZero_cokernel φ, local_lifts_iff_epi X F G φ⟩
  · intro F G H χ φ h
    let K := kernel φ
    let k : K ⟶ G := kernel.ι φ
    let l : F ⟶ K := kernel.lift φ χ h
    have fac : l ≫ k = χ := kernel.lift_ι φ χ h
    have fac_apply (W : Opens X) (f : F.val.obj (op W)) :
        k.val.app (op W) (l.val.app (op W) f) = χ.val.app (op W) f := by
      exact congrArg (fun m : F ⟶ G ↦ m.val.app (op W) f) fac
    have natural (W V : Opens X) (i : V ≤ W) (s : K.val.obj (op W)) :
        k.val.app (op V) (K.val.map (homOfLE i).op s) =
          G.val.map (homOfLE i).op (k.val.app (op W) s) := by
      exact congrArg (fun m ↦ m s) (k.val.naturality (homOfLE i).op)
    rw [(ShortComplex.mk χ φ h).exact_iff_epi_kernel_lift]
    change Epi l ↔ _
    rw [← local_lifts_iff_epi X F K l]
    constructor
    · intro hl W g hg
      obtain ⟨s, hs⟩ := (show g ∈ Set.range (ConcreteCategory.hom (k.val.app (op W)))
        from (kernel_sections X G H φ W).symm ▸ hg)
      obtain ⟨I, V, hV, f, hcover, hf⟩ := hl W s
      refine ⟨I, V, hV, f, hcover, ?_⟩
      intro i
      rw [← fac_apply, hf i, natural, hs]
    · intro hl W s
      have hs : φ.val.app (op W) (k.val.app (op W) s) = 0 := by
        have hm : k.val.app (op W) s ∈
            Set.range (ConcreteCategory.hom (k.val.app (op W))) := Set.mem_range_self s
        rw [kernel_sections X G H φ W] at hm
        exact hm
      obtain ⟨I, V, hV, f, hcover, hf⟩ := hl W (k.val.app (op W) s) hs
      refine ⟨I, V, hV, f, hcover, ?_⟩
      intro i
      let E := SheafOfModules.evaluation (moduleRings X) (op (V i))
      have hinj : Function.Injective (E.map k) :=
        (ModuleCat.mono_iff_injective (E.map k)).mp inferInstance
      apply hinj
      change k.val.app (op (V i)) (l.val.app (op (V i)) (f i)) =
        k.val.app (op (V i)) (K.val.map (homOfLE (hV i)).op s)
      rw [fac_apply, natural, hf i]

end AlgebraicGeometry.RingedSpace
