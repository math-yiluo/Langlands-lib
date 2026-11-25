/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.Algebra.Homology.AffinePerfectChainMapDescent
import WeilConjectures.Algebra.Homology.AffinePerfectHomotopyDescent

/-! # Affine full faithfulness for perfect complexes over a filtered colimit

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.29.2, Tag 09RE,
affine case (blueprint: lem-pc-affine-perfect-hom-colimit).

The equivalences `ident` identify a presentation `H` with the stage derived Hom sets.
The equations `htransition` and `hcanonical` specify scalar extension on every chain-map
representative, so neither the diagram nor its comparison map is arbitrary.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The canonical affine derived Hom comparison is bijective.
Source: Stacks Project, Derived Categories of Schemes, Tag 09RE, affine proof.
Proof: Scalar extension preserves projective terms and bounded-above support.
Mathlib's K-projective localization bijection represents every derived map by a
chain map, and detects equality by a homotopy. Chain maps descend by
`affine_perfect_chainMap_descent`; homotopies descend by
`affine_perfect_homotopy_descent`. For surjectivity, descend a chain representative
and use `hcanonical`. For injectivity, represent two colimit elements at one common
stage, lift both derived maps to chain maps, descend the resulting homotopy, and
use `htransition` and the filtered-colimit equality criterion. No derived-internal-Hom
or one-point sheaf comparison is needed.
(blueprint: lem-pc-affine-perfect-hom-colimit) -/
theorem affine_perfect_hom_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    [∀ i : I, HasDerivedCategory.{w} (ModuleCat.{u} (F.obj i))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (colimit F : CommRingCat.{u}))]
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hE : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (E₀.X n) ∧
        Module.Projective (F.obj i₀) (E₀.X n))
    (hK : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (K₀.X n) ∧
        Module.Projective (F.obj i₀) (K₀.X n))
    (H : Set.Ici i₀ ⥤ Type w) [HasColimit H]
    (ident : ∀ i : Set.Ici i₀, H.obj i ≃
      (DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj E₀) ⟶
       DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj K₀)))
    (htransition : ∀ (i j : Set.Ici i₀) (hij : i ≤ j)
      (f : (Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj E₀ ⟶
        (Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj K₀),
      ident j (H.map (homOfLE hij) ((ident i).symm (DerivedCategory.Q.map f))) =
        DerivedCategory.Q.map (scalarExtensionHom
          (F.map (homOfLE i.property)).hom (F.map (homOfLE hij)).hom
          (F.map (homOfLE j.property)).hom
          (congrArg CommRingCat.Hom.hom (F.map_comp
            (homOfLE i.property) (homOfLE hij))) E₀ K₀ f))
    (c : Cocone H)
    (e : c.pt ≃
      (DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (colimit.ι F i₀).hom) (.up ℤ)).obj E₀) ⟶
       DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (colimit.ι F i₀).hom) (.up ℤ)).obj K₀)))
    (hcanonical : ∀ (i : Set.Ici i₀)
      (f : (Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj E₀ ⟶
        (Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj K₀),
      e (c.ι.app i ((ident i).symm (DerivedCategory.Q.map f))) =
        DerivedCategory.Q.map (scalarExtensionHom
          (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom
          (colimit.ι F i₀).hom
          (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm)
          E₀ K₀ f)) :
    Function.Bijective (e ∘ colimit.desc H c) := by
  obtain ⟨b, hb⟩ : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (E₀.X n) := by
    obtain ⟨a, b, hab⟩ := hE.1
    exact ⟨b, fun n hn ↦ hab n (Or.inr hn)⟩
  have (n : ℤ) : Module.Projective (F.obj i₀) (E₀.X n) := (hE.2 n).2
  have hle {S : CommRingCat.{u}} (r : F.obj i₀ ⟶ S) :
      IsStrictlyLE (((ModuleCat.extendScalars r.hom).mapHomologicalComplex (.up ℤ)).obj E₀) b :=
    (isStrictlyLE_iff _ _).2 (fun n hn ↦ (ModuleCat.extendScalars r.hom).map_isZero (hb n hn))
  have hproj {S : CommRingCat.{u}} (r : F.obj i₀ ⟶ S) (n : ℤ) :
      Projective ((((ModuleCat.extendScalars r.hom).mapHomologicalComplex (.up ℤ)).obj E₀).X n) :=
    (ModuleCat.extendRestrictScalarsAdj r.hom).map_projective _ inferInstance
  have : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have : IsDirected (Set.Ici i₀) (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  constructor
  · intro x y hxy
    obtain ⟨i, xi, yi, rfl, rfl⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ (colimit.isColimit H) x y
    have := hle (F.map (homOfLE i.property))
    have := hproj (F.map (homOfLE i.property))
    obtain ⟨f, hf⟩ := DerivedCategory.Q_map_surjective_of_projective _ _ b (ident i xi)
    obtain ⟨g, hg⟩ := DerivedCategory.Q_map_surjective_of_projective _ _ b (ident i yi)
    have hxi := congrArg (ident i).symm hf
    have hyi := congrArg (ident i).symm hg
    simp only [Equiv.symm_apply_apply] at hxi hyi
    rw [← hxi, ← hyi] at hxy ⊢
    change e (colimit.desc H c (colimit.ι H i _)) =
      e (colimit.desc H c (colimit.ι H i _)) at hxy
    simp only [← CategoryTheory.types_comp_apply, colimit.ι_desc] at hxy
    have hxy := (hcanonical i f).symm.trans (hxy.trans (hcanonical i g))
    obtain ⟨j, hij, ⟨hj⟩⟩ := affine_perfect_homotopy_descent F i₀ E₀ K₀ hE hK i f g
      ((DerivedCategory.Q_map_eq_Q_map_iff_of_projective b _ _).1 hxy)
    have := hle (F.map (homOfLE j.property))
    have := hproj (F.map (homOfLE j.property))
    have heq := (DerivedCategory.Q_map_eq_Q_map_iff_of_projective b _ _).2 ⟨hj⟩
    have hH : H.map (homOfLE hij) ((ident i).symm (DerivedCategory.Q.map f)) =
        H.map (homOfLE hij) ((ident i).symm (DerivedCategory.Q.map g)) := by
      apply (ident j).injective
      exact (htransition i j hij f).trans (heq.trans (htransition i j hij g).symm)
    exact (Types.FilteredColimit.colimit_eq_iff H).2
      ⟨j, homOfLE hij, homOfLE hij, hH⟩
  · intro z
    have := hle (colimit.ι F i₀)
    have := hproj (colimit.ι F i₀)
    obtain ⟨f, hf⟩ := DerivedCategory.Q_map_surjective_of_projective _ _ b z
    obtain ⟨i, g, hg⟩ := affine_perfect_chainMap_descent F i₀ E₀ K₀ hE hK f
    refine ⟨colimit.ι H i ((ident i).symm (DerivedCategory.Q.map g)), ?_⟩
    change e (colimit.desc H c (colimit.ι H i _)) = z
    simp only [← CategoryTheory.types_comp_apply, colimit.ι_desc]
    exact (hcanonical i g).trans ((congrArg DerivedCategory.Q.map hg).trans hf)

end CochainComplex
