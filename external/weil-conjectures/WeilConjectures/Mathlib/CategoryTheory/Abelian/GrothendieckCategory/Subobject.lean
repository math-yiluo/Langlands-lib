/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject

/-!
# Distributivity of the subobject lattice of a Grothendieck abelian category

In a Grothendieck abelian category `C`, filtered colimits are exact (AB5). We deduce that
the lattice `Subobject X` of subobjects of an object `X : C` satisfies the distributivity
law `S ⊓ (⨆ i, T i) = ⨆ i, S ⊓ T i` for a directed family `T : ι → Subobject X`.

The `≥` inequality holds in any complete lattice; for `≤` we realize `⨆ i, T i` as a filtered
colimit of the `T i` (using `IsGrothendieckAbelian.subobjectMk_of_isColimit_eq_iSup` and
`IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup`) and use that the exactness of
filtered colimits turns the short exact sequences `S ⊓ T i ⟶ T i ⟶ X ⧸ S` into the sequence
`(⨆ i, S ⊓ T i) ⟶ (⨆ i, T i) ⟶ X ⧸ S`, which exhibits `⨆ i, S ⊓ T i` as `S ⊓ ⨆ i, T i`.

## Main results

- `CategoryTheory.IsGrothendieckAbelian.inf_iSup_of_directed`: the distributivity law.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

namespace IsGrothendieckAbelian

open Subobject

attribute [local instance] IsFiltered.isConnected

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

section

variable {X : C} {ι : Type w} [Nonempty ι]

/-- **AB5 distributivity of the subobject lattice.** In a Grothendieck abelian category, the
intersection with a fixed subobject `S` commutes with the supremum of a directed family of
subobjects. -/
lemma inf_iSup_of_directed (S : Subobject X) (T : ι → Subobject X)
    (hT : Directed (· ≤ ·) T) : S ⊓ (⨆ i, T i) = ⨆ i, S ⊓ T i := by
  refine le_antisymm ?_
    (iSup_le fun i => le_inf _root_.inf_le_left (_root_.inf_le_right.trans (le_iSup T i)))
  -- Regard `ι` as a filtered category, via the preorder induced by the directed family `T`.
  let _ : Preorder ι := Preorder.lift T
  have : IsDirectedOrder ι := ⟨fun i j => hT i j⟩
  have hTm : Monotone T := fun i j h => h
  have hSTm : Monotone (fun i => S ⊓ T i) := fun i j h => inf_le_inf_left S h
  let F : ι ⥤ MonoOver X := hTm.functor ⋙ Subobject.representative
  let F' : ι ⥤ MonoOver X := hSTm.functor ⋙ Subobject.representative
  let c₀ : Cocone F :=
    { pt := Subobject.representative.obj (⨆ i, T i)
      ι := { app := fun i => Subobject.representative.map (homOfLE (le_iSup T i))
             naturality := fun i j φ => Subsingleton.elim _ _ } }
  let c₀' : Cocone F' :=
    { pt := Subobject.representative.obj (⨆ i, S ⊓ T i)
      ι := { app := fun i => Subobject.representative.map (homOfLE (le_iSup _ i))
             naturality := fun i j φ => Subsingleton.elim _ _ } }
  have hm : Mono ((MonoOver.forget X).mapCocone c₀).pt.hom :=
    (inferInstance : Mono (⨆ i, T i).arrow)
  have hm' : Mono ((MonoOver.forget X).mapCocone c₀').pt.hom :=
    (inferInstance : Mono (⨆ i, S ⊓ T i).arrow)
  -- The suprema `⨆ i, T i` and `⨆ i, S ⊓ T i` are the filtered colimits of the two families.
  have hc : IsColimit ((Over.forget X).mapCocone ((MonoOver.forget X).mapCocone c₀)) :=
    isColimitMapCoconeOfSubobjectMkEqISup F _ (by simp [c₀, F])
  have hc' : IsColimit ((Over.forget X).mapCocone ((MonoOver.forget X).mapCocone c₀')) :=
    isColimitMapCoconeOfSubobjectMkEqISup F' _ (by simp [c₀', F'])
  -- The complexes `S ⊓ T i ⟶ T i ⟶ X ⧸ S`, assembled into a short complex of functors.
  let SC : ShortComplex (ι ⥤ C) :=
    { X₁ := hSTm.functor ⋙ Subobject.underlying
      X₂ := hTm.functor ⋙ Subobject.underlying
      X₃ := (Functor.const ι).obj (cokernel S.arrow)
      f := { app := fun i => Subobject.ofLE (S ⊓ T i) (T i) _root_.inf_le_right
             naturality := fun i j φ => by
               dsimp only [Functor.comp_obj, Functor.comp_map, Monotone.functor]
               rw [← cancel_mono (T j).arrow]
               simp }
      g := { app := fun i => (T i).arrow ≫ cokernel.π S.arrow
             naturality := fun i j φ => by
               dsimp only [Functor.comp_obj, Functor.comp_map, Monotone.functor]
               simp }
      zero := by ext i; exact Subobject.ofLE_inf_comp_arrow_comp_cokernel_π S (T i) }
  have hSC : SC.Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    refine evaluationJointlyReflectsLimits _ fun i => (KernelFork.isLimitMapConeEquiv _ _).2 ?_
    exact Subobject.isLimitKernelForkInf S (T i)
  have hVU : (⨆ i, S ⊓ T i) ≤ ⨆ i, T i :=
    iSup_le fun i => _root_.inf_le_right.trans (le_iSup T i)
  have hf : ∀ i, ((Over.forget X).mapCocone ((MonoOver.forget X).mapCocone c₀')).ι.app i ≫
      Subobject.ofLE _ _ hVU =
      SC.f.app i ≫ ((Over.forget X).mapCocone ((MonoOver.forget X).mapCocone c₀)).ι.app i :=
    fun i => by
      change Subobject.ofLE (S ⊓ T i) (⨆ i, S ⊓ T i) (le_iSup (fun i => S ⊓ T i) i) ≫
          Subobject.ofLE (⨆ i, S ⊓ T i) (⨆ i, T i) hVU =
        Subobject.ofLE (S ⊓ T i) (T i) _root_.inf_le_right ≫
          Subobject.ofLE (T i) (⨆ i, T i) (le_iSup T i)
      rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_comp_ofLE]
  have hg : ∀ i, ((Over.forget X).mapCocone ((MonoOver.forget X).mapCocone c₀)).ι.app i ≫
      ((⨆ i, T i).arrow ≫ cokernel.π S.arrow) =
      SC.g.app i ≫ (Limits.constCocone ι (cokernel S.arrow)).ι.app i :=
    fun i => by
      change Subobject.ofLE (T i) (⨆ i, T i) (le_iSup T i) ≫
          (⨆ i, T i).arrow ≫ cokernel.π S.arrow =
        ((T i).arrow ≫ cokernel.π S.arrow) ≫ 𝟙 _
      rw [← Category.assoc, Subobject.ofLE_arrow, Category.comp_id]
  -- Filtered colimits are exact, so `⨆ i, S ⊓ T i ⟶ ⨆ i, T i ⟶ X ⧸ S` is again exact,
  -- which exhibits `⨆ i, S ⊓ T i` as the kernel of `(⨆ i, T i).arrow ≫ cokernel.π S.arrow`.
  have hVS : (⨆ i, S ⊓ T i) ≤ S := iSup_le fun i => _root_.inf_le_left
  have hzero : Subobject.ofLE (⨆ i, S ⊓ T i) (⨆ i, T i) hVU ≫
      (⨆ i, T i).arrow ≫ cokernel.π S.arrow = 0 := by
    rw [← Category.assoc, Subobject.ofLE_arrow, ← Subobject.ofLE_arrow hVS, Category.assoc,
      cokernel.condition, comp_zero]
  have hEx : (ShortComplex.mk _ _ hzero).Exact :=
    Limits.colim.exact_mapShortComplex hSC hc' hc
      (Limits.isColimitConstCocone ι (cokernel S.arrow)) _ _ hf hg
  obtain ⟨β, hβ⟩ := KernelFork.IsLimit.lift' hEx.fIsKernel
    (Subobject.ofLE (S ⊓ ⨆ i, T i) (⨆ i, T i) _root_.inf_le_right)
    (Subobject.ofLE_inf_comp_arrow_comp_cokernel_π S (⨆ i, T i))
  have h1 : β ≫ Subobject.ofLE (⨆ i, S ⊓ T i) (⨆ i, T i) hVU =
      Subobject.ofLE (S ⊓ ⨆ i, T i) (⨆ i, T i) _root_.inf_le_right := hβ
  -- Finally, `S ⊓ ⨆ i, T i` maps to that kernel, hence is contained in `⨆ i, S ⊓ T i`.
  refine Subobject.le_of_comm β ?_
  have h2 := h1 =≫ (⨆ i, T i).arrow
  rw [Category.assoc, Subobject.ofLE_arrow, Subobject.ofLE_arrow] at h2
  exact h2

/-- **AB5 distributivity of the subobject lattice**, with the factors of the intersection
swapped. -/
lemma iSup_inf_of_directed (S : Subobject X) (T : ι → Subobject X)
    (hT : Directed (· ≤ ·) T) : (⨆ i, T i) ⊓ S = ⨆ i, T i ⊓ S := by
  simp only [_root_.inf_comm _ S, inf_iSup_of_directed S T hT]


end

end IsGrothendieckAbelian

end CategoryTheory
