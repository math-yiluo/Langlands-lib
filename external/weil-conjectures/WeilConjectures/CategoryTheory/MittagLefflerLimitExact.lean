/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.MLSetsTowerLimitNonempty

/-!
# Mittag-Leffler quotients and exact inverse limits

Source: Stacks Project, Homology, Lemma Tag 02N1, parts (2) and (3)
(blueprint: lem-weil-pbc-mittag-leffler-limit-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

/-- A termwise short exact sequence of towers of abelian groups has ML quotient when its
middle system is ML, and its inverse limit is short exact when its kernel is ML.
Source: Stacks Project, Homology, Tag 02N1 (2), (3); Algebra, Tags 0598 and 03CA.
(blueprint: lem-weil-pbc-mittag-leffler-limit-exact)

The index `n : ℕ` denotes the positive index `n + 1`. Towers and their morphisms are
functors `ℕᵒᵖ ⥤ AddCommGrpCat` and natural transformations (`def-weil-inverse-system`), and
the sequence `0 → A → B → C → 0` is the short complex `S` of towers, short exact at every
index (`hS`), as in `isMittagLeffler_iff_of_isEssentiallyConstant` (Tag 070D). ML is
Mathlib's `IsMittagLeffler` of the underlying-set system
(`def-weil-pbc-mittag-leffler-system`); the images decrease, so it is stabilization of
images as subgroups. The inverse limit is Mathlib's `lim`, which in `AddCommGrpCat` is the
group of compatible sequences, and `S.map lim` is `0 → lim A → lim B → lim C → 0` with the
induced maps; its short exactness is injectivity of `lim u`, exactness at `lim B` and
surjectivity of `lim v`.

Proof (the node's six steps):
1. Write a, b, t for transitions of A, B, C, and use functoriality for their composites
from k to i. Naturality of u and v gives commuting squares for these composites.
Termwise exactness means u is injective, v is surjective, and ker v = im u.
Compatibility of a sequence with adjacent transitions implies compatibility with composites.
2. If B is ML at i with witness c, then surjectivity of v at k and naturality give
im(t_{k,i}) = v_i(im(b_{k,i})). Stabilization for B therefore implies stabilization
for C with the same witness c (`def-weil-pbc-mittag-leffler-system`).
3. Assume A is ML and fix a compatible c in the limit of C. The fibres E_i = v_i⁻¹(c_i)
are nonempty by surjectivity. Naturality and compatibility restrict b to a tower of
nonempty sets (`def-weil-inverse-system`).
4. Choose j witnessing ML for A at i. For k ≥ j, the image of E_k in E_i is contained
in that of E_j. For the reverse inclusion take e_j in E_j and any e'_k in E_k.
Put e'_j = b_{k,j}(e'_k). Exactness writes e_j - e'_j = u_j(α).
Stabilization supplies β in A_k with a_{k,i}(β) = a_{j,i}(α).
Then x_k = e'_k + u_k(β) is in E_k and b_{k,i}(x_k) = b_{j,i}(e_j).
Thus E is ML (`def-weil-pbc-mittag-leffler-system`).
5. Apply `lem-weil-pbc-ml-sets-tower-limit-nonempty` to obtain compatible e_i in E_i.
This gives a preimage of c, proving surjectivity of the map on limits.
6. A limit map is injective if all its components are. A compatible family in the
kernel of the second map has unique componentwise preimages under the first map.
Naturality and componentwise injectivity make them compatible. Thus the limit sequence
is left exact directly; combine with step 5. -/
theorem mittagLeffler_quotient_and_limit_exact
    (S : ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u}))
    (hS : ∀ n : ℕᵒᵖ, (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ShortExact) :
    ((S.X₂ ⋙ forget AddCommGrpCat).IsMittagLeffler →
      (S.X₃ ⋙ forget AddCommGrpCat).IsMittagLeffler) ∧
    ((S.X₁ ⋙ forget AddCommGrpCat).IsMittagLeffler →
      (S.map (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})).ShortExact) := by
  constructor
  · intro hB
    have hsurj (i : ℕᵒᵖ) : Function.Surjective (S.g.app i) := by
      exact (hS i).ab_surjective_g
    intro j
    obtain ⟨i, f, hf⟩ := hB j
    refine ⟨i, f, fun k g => ?_⟩
    rintro _ ⟨x, rfl⟩
    obtain ⟨b, rfl⟩ := hsurj i x
    obtain ⟨b', hb'⟩ := hf g ⟨b, rfl⟩
    refine ⟨S.g.app k b', ?_⟩
    change S.X₃.map g (S.g.app k b') = S.X₃.map f (S.g.app i b)
    calc
      _ = S.g.app j (S.X₂.map g b') :=
        (ConcreteCategory.congr_hom (S.g.naturality g) b').symm
      _ = S.g.app j (S.X₂.map f b) := congrArg (S.g.app j) hb'
      _ = _ := ConcreteCategory.congr_hom (S.g.naturality f) b
  · intro hA
    classical
    have hnat {F G : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (η : F ⟶ G)
        {i j : ℕᵒᵖ} (f : i ⟶ j) (x : F.obj i) :
        η.app j (F.map f x) = G.map f (η.app i x) :=
      ConcreteCategory.congr_hom (η.naturality f) x
    have hcoord {F G : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (η : F ⟶ G)
        (n : ℕᵒᵖ) (x : ↑(limit F)) :
        limit.π G n (limMap η x) = η.app n (limit.π F n x) :=
      ConcreteCategory.congr_hom (limMap_π η n) x
    have hcompat (F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) {i j : ℕᵒᵖ}
        (f : i ⟶ j) (x : ↑(limit F)) :
        F.map f (limit.π F i x) = limit.π F j x :=
      ConcreteCategory.congr_hom (limit.w F f) x
    let e (F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :=
      Types.isLimitEquivSections (isLimitOfPreserves (forget AddCommGrpCat) (limit.isLimit F))
    have he (F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (s : (F ⋙ forget AddCommGrpCat).sections)
        (n : ℕᵒᵖ) : limit.π F n ((e F).symm s) = s.val n :=
      Types.isLimitEquivSections_symm_apply
        (isLimitOfPreserves (forget AddCommGrpCat) (limit.isLimit F)) s n
    have hinj : Function.Injective (limMap S.f) := by
      intro x y hxy
      apply Concrete.limit_ext S.X₁
      intro n
      apply (hS n).ab_injective_f
      change S.f.app n (limit.π S.X₁ n x) = S.f.app n (limit.π S.X₁ n y)
      rw [← hcoord, ← hcoord, hxy]
    have hexact : (S.map lim).Exact := by
      apply (S.map lim).ab_exact_iff.mpr
      intro b hb
      have hb' (n : ℕᵒᵖ) : S.g.app n (limit.π S.X₂ n b) = 0 := by
        rw [← hcoord]
        change limit.π S.X₃ n ((S.map lim).g b) = 0
        rw [hb]
        exact map_zero _
      have ha (n : ℕᵒᵖ) : ∃ a : S.X₁.obj n, S.f.app n a = limit.π S.X₂ n b :=
        ((S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ab_exact_iff.mp
          (hS n).exact) _ (hb' n)
      choose a ha using ha
      have hacomp {i j : ℕᵒᵖ} (f : i ⟶ j) : S.X₁.map f (a i) = a j := by
        apply (hS j).ab_injective_f
        change S.f.app j (S.X₁.map f (a i)) = S.f.app j (a j)
        rw [hnat, ha, ha, hcompat]
      let s : (S.X₁ ⋙ forget AddCommGrpCat).sections := ⟨a, fun f => hacomp f⟩
      refine ⟨(e S.X₁).symm s, ?_⟩
      apply Concrete.limit_ext S.X₂
      intro n
      change limit.π S.X₂ n (limMap S.f _) = _
      rw [hcoord, he]
      exact ha n
    have hsurj : Function.Surjective (limMap S.g) := by
      intro c
      let E : ℕᵒᵖ ⥤ Type u :=
        { obj := fun n => { b : S.X₂.obj n // S.g.app n b = limit.π S.X₃ n c }
          map := fun {i j} f => ↾fun b => ⟨S.X₂.map f b.val, by
            rw [hnat, b.property, hcompat]⟩
          map_id := by
            intro n
            apply ConcreteCategory.hom_ext
            intro b
            apply Subtype.ext
            exact ConcreteCategory.congr_hom (S.X₂.map_id n) b.val
          map_comp := by
            intro i j k f g
            apply ConcreteCategory.hom_ext
            intro b
            apply Subtype.ext
            exact ConcreteCategory.congr_hom (S.X₂.map_comp f g) b.val }
      have hE (n : ℕᵒᵖ) : Nonempty (E.obj n) := by
        obtain ⟨b, hb⟩ := (hS n).ab_surjective_g (limit.π S.X₃ n c)
        exact ⟨⟨b, hb⟩⟩
      have hEML : E.IsMittagLeffler := by
        apply (Functor.isMittagLeffler_iff_subset_range_comp E).mpr
        intro j
        obtain ⟨i, f, hf⟩ :=
          (Functor.isMittagLeffler_iff_subset_range_comp _).mp hA j
        refine ⟨i, f, fun k g => ?_⟩
        rintro _ ⟨b, rfl⟩
        obtain ⟨d⟩ := hE k
        have hz : S.g.app i (b.val - S.X₂.map g d.val) = 0 := by
          rw [map_sub, hnat, b.property, d.property, hcompat, sub_self]
        obtain ⟨a, ha⟩ :=
          ((S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj i)).ab_exact_iff.mp
            (hS i).exact) _ hz
        change S.f.app i a = b.val - S.X₂.map g d.val at ha
        obtain ⟨a', ha'⟩ := hf g ⟨a, rfl⟩
        have hzero : S.g.app k (S.f.app k a') = 0 := by
          have hz : S.f.app k ≫ S.g.app k = 0 := by
            change (S.f ≫ S.g).app k = (0 : S.X₁ ⟶ S.X₃).app k
            exact congrArg (fun η : S.X₁ ⟶ S.X₃ => η.app k) S.zero
          exact ConcreteCategory.congr_hom hz a'
        refine ⟨⟨d.val + S.f.app k a', ?_⟩, ?_⟩
        · rw [map_add, hzero, add_zero]
          exact d.property
        · apply Subtype.ext
          change S.X₂.map (g ≫ f) (d.val + S.f.app k a') = S.X₂.map f b.val
          change S.X₁.map (g ≫ f) a' = S.X₁.map f a at ha'
          rw [map_add, ← hnat, ha', hnat]
          have hc : S.X₂.map (g ≫ f) d.val = S.X₂.map f (S.X₂.map g d.val) :=
            ConcreteCategory.congr_hom (S.X₂.map_comp g f) d.val
          rw [hc, ha, map_sub]
          abel
      obtain ⟨s, hs⟩ := Functor.nonempty_sections_of_isMittagLeffler E hEML
      let b : (S.X₂ ⋙ forget AddCommGrpCat).sections :=
        ⟨fun n => (s n).val, fun f => congrArg Subtype.val (hs f)⟩
      refine ⟨(e S.X₂).symm b, ?_⟩
      apply Concrete.limit_ext S.X₃
      intro n
      rw [hcoord, he]
      exact (s n).property
    exact ShortExact.mk' hexact ((AddCommGrpCat.mono_iff_injective _).mpr hinj)
      ((AddCommGrpCat.epi_iff_surjective _).mpr hsurj)

end CategoryTheory.ShortComplex
