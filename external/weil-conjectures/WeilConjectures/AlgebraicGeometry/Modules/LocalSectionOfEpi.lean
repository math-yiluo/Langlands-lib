/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Local sections of epimorphisms onto finite locally free modules

## References

* [Stacks: Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Extract a finite free trivialization from the local generators data. -/
private theorem finite_free_neighborhood {X : Scheme.{u}} (Q : X.Modules)
    [Q.IsFiniteLocallyFree] (x : X) :
    ∃ (U : X.Opens) (I : Type u) (_ : Fintype I), x ∈ U ∧
      Nonempty (Q.over U ≅ SheafOfModules.free I) := by
  obtain ⟨q, hq, hf⟩ := SheafOfModules.IsFiniteLocallyFree.exists_localGeneratorsData
    (M := Q)
  obtain ⟨V, g, ⟨i, ⟨k⟩⟩, hxV⟩ := q.coversTop ⊤ x trivial
  have := hf.isFiniteType i
  have := hq.isIso i
  let U := q.X i
  let I := (q.generators i).I
  let : Fintype I := Fintype.ofFinite I
  have hxU : x ∈ U := k.le hxV
  let e : Q.over U ≅ SheafOfModules.free I := (asIso (q.generators i).π).symm
  exact ⟨U, I, inferInstance, hxU, ⟨e⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Lift finitely many sections on a common neighbourhood, including the empty family. -/
private theorem finite_local_lifts {X : Scheme.{u}} {B C : X.Modules}
    (g : B ⟶ C) [Epi g] (I : Type u) [Finite I] (U : X.Opens)
    (c : I → C.val.obj (Opposite.op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      ∃ b : I → B.val.obj (Opposite.op V), ∀ i,
        g.val.app (Opposite.op V) (b i) = C.val.map (homOfLE hV).op (c i) := by
  classical
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : Epi (T.map g) := inferInstance
  have hl := (TopCat.Presheaf.isLocallySurjective_iff
    ((PresheafOfModules.toPresheaf _).map g.val)).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi (T.map g)).mpr inferInstance)
  choose V hV hb hxV using fun i : I ↦ hl U (c i) x hx
  choose b hb using hb
  let W : X.Opens := U ⊓ ⨅ i, V i
  have hWU : W ≤ U := inf_le_left
  have hWV (i : I) : W ≤ V i := inf_le_right.trans (iInf_le _ i)
  refine ⟨W, hWU, ?_, fun i ↦ B.val.map (homOfLE (hWV i)).op (b i), ?_⟩
  · exact ⟨hx, by
      change x ∈ ((⨅ i, V i : X.Opens) : Set X)
      rw [TopologicalSpace.Opens.coe_iInf]
      exact Set.mem_iInter.mpr hxV⟩
  · intro i
    change g.val.app (Opposite.op W) (B.val.map (homOfLE (hWV i)).op (b i)) = _
    rw [PresheafOfModules.naturality_apply]
    change C.val.map (homOfLE (hWV i)).op (g.val.app (Opposite.op (V i)) (b i)) = _
    have hb' : g.val.app (Opposite.op (V i)) (b i) =
        C.val.map (homOfLE (hV i)).op (c i) := hb i
    rw [hb', ← PresheafOfModules.map_comp_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- An epimorphism `f : P ⟶ Q` onto a finite locally free module has a section on a
neighbourhood of every point. -/
theorem exists_local_section_of_epi
    {X : Scheme.{u}} {P Q : X.Modules} (f : P ⟶ Q) [Epi f] [Q.IsFiniteLocallyFree] :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ s : (restrictFunctor U.ι).obj Q ⟶ (restrictFunctor U.ι).obj P,
        s ≫ (restrictFunctor U.ι).map f = 𝟙 _ := by
  classical
  intro x
  obtain ⟨U, I, hI, hxU, ⟨e⟩⟩ := finite_free_neighborhood Q x
  let := hI
  let c (i : I) : Q.val.obj (Opposite.op U) :=
    (e.inv.val.app (Opposite.op (Over.mk (𝟙 U))))
      ((SheafOfModules.ιFree i).val.app (Opposite.op (Over.mk (𝟙 U))) (1 : Γ(X, U)))
  obtain ⟨W, hWU, hxW, b, hb⟩ := finite_local_lifts f I U c x hxU
  let F := SheafOfModules.overMap X.ringCatSheaf (homOfLE hWU)
  have : F.Additive := ⟨by
    intro M N g h
    ext V z
    rfl⟩
  let E := (SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE hWU)).app Q
  let t (i : I) : (P.over W).sections :=
    PresheafOfModules.sectionsMk
      (fun V ↦ P.val.map V.unop.hom.op (b i)) (by
        intro V V' g
        change P.val.map g.unop.left.op (P.val.map V.unop.hom.op (b i)) = _
        rw [← PresheafOfModules.map_comp_apply]
        rfl)
  let a (i : I) : Q.over W ⟶ SheafOfModules.unit (X.ringCatSheaf.over W) :=
    E.inv ≫ F.map (e.hom ≫ SheafOfModules.freeπ i) ≫
      (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) (homOfLE hWU)).hom
  let d (i : I) : SheafOfModules.unit (X.ringCatSheaf.over W) ⟶ Q.over W :=
    (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) (homOfLE hWU)).inv ≫
      F.map (SheafOfModules.ιFree i ≫ e.inv) ≫ E.hom
  have ht (i : I) : (P.over W).unitHomEquiv.symm (t i) ≫ f.over W = d i := by
    apply (Q.over W).unitHomEquiv.injective
    rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro V
    change f.val.app (Opposite.op V.unop.left) (P.val.map V.unop.hom.op (b i)) = _
    rw [PresheafOfModules.naturality_apply, hb i, ← PresheafOfModules.map_comp_apply]
    let k := SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i ≫ e.inv
    let j : Over.mk (V.unop.hom ≫ homOfLE hWU) ⟶ Over.mk (𝟙 U) :=
      Over.homMk (V.unop.hom ≫ homOfLE hWU)
    have hn := PresheafOfModules.naturality_apply k.val j.op (1 : Γ(X, U))
    change k.val.app (Opposite.op (Over.mk (V.unop.hom ≫ homOfLE hWU)))
        (X.presheaf.map (V.unop.hom ≫ homOfLE hWU).op (1 : Γ(X, U))) =
      Q.val.map (V.unop.hom ≫ homOfLE hWU).op
        (k.val.app (Opposite.op (Over.mk (𝟙 U))) (1 : Γ(X, U))) at hn
    rw [map_one] at hn
    change Q.val.map (V.unop.hom ≫ homOfLE hWU).op
        (k.val.app (Opposite.op (Over.mk (𝟙 U))) (1 : Γ(X, U))) =
      k.val.app (Opposite.op (Over.mk (V.unop.hom ≫ homOfLE hWU))) (1 : Γ(X, V.unop.left))
    exact hn.symm
  let s : Q.over W ⟶ P.over W := ∑ i : I, a i ≫ (P.over W).unitHomEquiv.symm (t i)
  have hs : s ≫ f.over W = 𝟙 _ := by
    dsimp only [s]
    rw [Preadditive.sum_comp]
    simp_rw [Category.assoc, ht]
    dsimp only [a, d]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    calc
      _ = E.inv ≫ F.map (∑ i : I,
          e.hom ≫ SheafOfModules.freeπ i ≫ SheafOfModules.ιFree i ≫ e.inv) ≫ E.hom := by
        simp only [F.map_sum, Preadditive.comp_sum, Preadditive.sum_comp]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Functor.map_comp, Category.assoc]
      _ = 𝟙 _ := by
        have he : (∑ i : I,
            e.hom ≫ SheafOfModules.freeπ i ≫ SheafOfModules.ιFree i ≫ e.inv) = 𝟙 _ := by
          rw [← Preadditive.comp_sum]
          simp_rw [← Category.assoc]
          rw [← Preadditive.sum_comp, SheafOfModules.sum_freeπ_ιFree]
          simp
        rw [he, F.map_id]
        change E.inv ≫ (𝟙 _) ≫ E.hom = 𝟙 _
        simp only [Category.id_comp, E.inv_hom_id]
  let G := (overEquiv W).functor
  let eP := (overFunctorEquiv W).app P
  let eQ := (overFunctorEquiv W).app Q
  refine ⟨W, hxW, eQ.inv ≫ G.map s ≫ eP.hom, ?_⟩
  have hn : G.map (f.over W) ≫ eQ.hom =
      eP.hom ≫ (restrictFunctor W.ι).map f :=
    (overFunctorEquiv W).hom.naturality f
  simp only [Category.assoc]
  rw [← hn, ← Category.assoc (G.map s), ← G.map_comp, hs]
  simp

end AlgebraicGeometry.Scheme.Modules
