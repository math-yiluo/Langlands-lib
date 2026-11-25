/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor

/-!
# The successor step for filtered colimits of right derived functors

Source: Stacks Project, Cohomology on Sites, Tag 0739, the induction diagram.
(blueprint: lem-weil-pbc-right-derived-filtered-colimit-successor).
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂ t

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Functor

/-- Preservation in degree `n` implies preservation in degree `n + 1` when filtered
colimits of injective diagrams are acyclic in that next degree.
Source: Stacks Project, Tag 0739, second paragraph and the comparison diagram.
(blueprint: lem-weil-pbc-right-derived-filtered-colimit-successor).

Proof:
1. Choose functorial injective embeddings in the Grothendieck abelian category `A`.
For a diagram `F`, form its injective diagram `J`, its cokernel diagram `Q`, and the
pointwise short exact sequence `0 → F → J → Q → 0`. Exactness of `I`-colimits gives
`0 → colim F → colim J → colim Q → 0`.
2. The natural connecting maps of the right derived delta-functor give exact rows
`colim Rⁿv(J) → colim Rⁿv(Q) → colim Rⁿ⁺¹v(F) → 0` and
`Rⁿv(colim J) → Rⁿv(colim Q) → Rⁿ⁺¹v(colim F) → 0`.
The first row is exact because colimits in `B` are exact and injectives have zero
positive derived functors. The second ends in zero by `hacyclic`.
3. The canonical comparison maps form a commuting ladder: the first square is
functoriality, and the second follows from naturality of the connecting maps for
each coprojection of the short exact sequences. The first two vertical maps are
isomorphisms by preservation in degree `n`.
4. The third vertical map is an isomorphism by the cokernel universal property,
or the four lemma with zero on the right. Thus the image of every colimit cocone
under `v.rightDerived (n + 1)` is a colimit cocone. -/
theorem preservesColimitsOfShape_rightDerived_succ
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [IsGrothendieckAbelian.{w} A] [Abelian B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]
    (I : Type t) [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]
    (n : ℕ)
    (hacyclic : ∀ (J : I ⥤ A), (∀ i : I, Injective (J.obj i)) →
      IsZero ((v.rightDerived (n + 1)).obj (colimit J)))
    [PreservesColimitsOfShape I (v.rightDerived n)] :
    PreservesColimitsOfShape I (v.rightDerived (n + 1)) := by
  classical
  obtain ⟨D, hD, _⟩ := exists_horseshoe_rightDerived_deltaFunctor v
  have (k : ℕ) : (D.F k).Additive := D.additive k
  have : PreservesColimitsOfShape I (D.F n) := by
    simpa only [hD] using (inferInstance : PreservesColimitsOfShape I (v.rightDerived n))
  have hI (X : A) [Injective X] : IsZero ((D.F (n + 1)).obj X) := by
    simpa only [hD] using v.isZero_rightDerived_obj_injective_succ n X
  have hC (J : I ⥤ A) (hJ : ∀ i : I, Injective (J.obj i)) :
      IsZero ((D.F (n + 1)).obj (colimit J)) := by
    simpa only [hD] using hacyclic J hJ
  have h : PreservesColimitsOfShape I (D.F (n + 1)) := by
    refine ⟨fun {F} ↦ ?_⟩
    suffices IsIso (colimit.post F (D.F (n + 1))) from
      preservesColimit_of_isIso_post (D.F (n + 1)) F
    let d := MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms A) (MorphismProperty.monomorphisms A).rlp
    let Z : I ⥤ Arrow A :=
      { obj i := Arrow.mk (0 : F.obj i ⟶ 0)
        map f := Arrow.homMk (F.map f) (𝟙 _) (by simp)
        map_id i := by ext <;> simp
        map_comp f g := by ext <;> simp }
    let J := Z ⋙ d.Z
    let j : F ⟶ J :=
      { app i := d.i.app (Z.obj i)
        naturality i k f := d.i.naturality (Z.map f) }
    have (i : I) : Mono (j.app i) := d.hi (Z.obj i)
    have : Mono j := NatTrans.mono_of_mono_app j
    have hJ (i : I) : Injective (J.obj i) := by
      exact inferInstanceAs
        (Injective (IsGrothendieckAbelian.monoMapFactorizationDataRlp
          (0 : F.obj i ⟶ 0)).Z)
    let S := ShortComplex.cokernelSequence j
    have : Mono S.f := inferInstanceAs (Mono j)
    have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact j⟩
    let T := S.map (colim (J := I) (C := A))
    have hT : T.ShortExact := hS.map_of_exact _
    let Si (i : I) := S.map ((evaluation I A).obj i)
    have hSi (i : I) : (Si i).ShortExact := hS.map_of_exact _
    let δ : S.X₃ ⋙ D.F n ⟶ F ⋙ D.F (n + 1) :=
      { app i := D.delta (Si i) (hSi i) n
        naturality i k f :=
          (D.naturality (Si i) (Si k) (hSi i) (hSi k)
            (S.mapNatTrans ((evaluation I A).map f)) n).symm }
    have hw : whiskerRight S.g (D.F n) ≫ δ = 0 := by
      ext i
      exact (D.exact_right (Si i) (hSi i) n).choose
    let L := ShortComplex.mk (whiskerRight S.g (D.F n)) δ hw
    have hepi (i : I) : Epi (δ.app i) := by
      obtain ⟨w, h⟩ := D.exact_left (Si i) (hSi i) n
      have := hJ i
      exact h.epi_f ((hI (J.obj i)).eq_of_tgt _ _)
    have : Epi δ := NatTrans.epi_of_epi_app δ
    have hL : L.Exact := by
      apply L.exact_iff_isZero_homology.mpr
      rw [IsZero.iff_id_eq_zero]
      ext i
      have hi : (L.map ((evaluation I B).obj i)).Exact :=
        (D.exact_right (Si i) (hSi i) n).choose_spec
      have hz := IsZero.of_iso
        ((L.map ((evaluation I B).obj i)).exact_iff_isZero_homology.mp hi)
        (L.mapHomologyIso ((evaluation I B).obj i)).symm
      exact hz.eq_of_src _ _
    let Lc := L.map (colim (J := I) (C := B))
    have hLc : Lc.Exact := hL.map _
    have : Epi Lc.g := inferInstanceAs (Epi ((colim (J := I) (C := B)).map δ))
    obtain ⟨wr, hr⟩ := D.exact_right T hT n
    let R := ShortComplex.mk ((D.F n).map T.g) (D.delta T hT n) wr
    have : Epi R.g := by
      obtain ⟨w, h⟩ := D.exact_left T hT n
      exact h.epi_f ((hC J hJ).eq_of_tgt _ _)
    let φ : Lc ⟶ R :=
      { τ₁ := colimit.post J (D.F n)
        τ₂ := colimit.post S.X₃ (D.F n)
        τ₃ := colimit.post F (D.F (n + 1))
        comm₁₂ := by
          exact colimit.map_post S.g (D.F n)
        comm₂₃ := by
          change colimit.post S.X₃ (D.F n) ≫ D.delta T hT n =
            colim.map δ ≫ colimit.post F (D.F (n + 1))
          apply colimit.hom_ext
          intro i
          simp only [colimit.ι_post_assoc, colimit.ι_map_assoc, colimit.ι_post]
          let ψ : Si i ⟶ T :=
            { τ₁ := colimit.ι F i
              τ₂ := colimit.ι J i
              τ₃ := colimit.ι S.X₃ i
              comm₁₂ := colimit.ι_map j i
              comm₂₃ := colimit.ι_map S.g i }
          exact (D.naturality (Si i) T (hSi i) hT ψ n).symm }
    have : IsIso φ.τ₁ := inferInstanceAs (IsIso (colimit.post J (D.F n)))
    have : IsIso φ.τ₂ := inferInstanceAs (IsIso (colimit.post S.X₃ (D.F n)))
    exact Abelian.isIso_of_epi_of_isIso
      (ShortComplex.mapToComposableArrows φ) hLc.exact_toComposableArrows
      hr.exact_toComposableArrows
      (by change Epi Lc.g; infer_instance)
      (by change Epi R.g; infer_instance)
      (by simpa using (inferInstance : Epi φ.τ₁))
      (by simpa using (inferInstance : IsIso φ.τ₂))
  simpa only [hD] using h

end CategoryTheory.Functor
