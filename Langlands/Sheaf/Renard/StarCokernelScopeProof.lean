import Langlands.Sheaf.Renard.StarCokernelScopeStatements
import Mathlib.Logic.Small.Basic

/-!
# Proof of the star-sheaf cokernel injection and undersized obstructions

A colimit cokernel cofork of the actual star map `f` receives, for each leaf,
a global section glued from the integer-one section at that leaf. The induced
maps to the mod-two skyscrapers separate these sections. In the undersized
specialization this injection makes `Type v` small, which is impossible.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Langlands.Sheaf.Renard.StarDiagram

section Injection

variable {I : Type u}

local instance starCokernelScopeTopology : TopologicalSpace (Option I) := topology I

theorem live_starCover (a : Option I) : Live (starCover a) := by
  cases a with
  | none => exact live_E
  | some i => exact live_U i

/-- A cokernel arrow annihilates every section in the image of `f`. -/
theorem cofork_app_f (c : CokernelCofork (f.{u,v} (I := I))) (V : StarOpen I)
    (x : Sections (F.{u,v} (I := I)).obj.obj V) :
    (sheafHomEquiv _ _ c.π).app (op V) ((sheafHomEquiv _ _ (f.{u,v} (I := I))).app (op V) x) =
      0 :=
  congrArg (fun m => (sheafHomEquiv _ _ m).app (op V) x) (CokernelCofork.condition c)

/-- On an open without leaves `f` is the identity, so a cokernel arrow kills
every section of `G` there. -/
theorem cofork_app_eq_zero_of_not_leaf (c : CokernelCofork (f.{u,v} (I := I)))
    {V : StarOpen I} (hV : ¬ Leaf V) (x : Sections (G.{u,v} (I := I)).obj.obj V) :
    (sheafHomEquiv _ _ c.π).app (op V) x = 0 := by
  have hx : (sheafHomEquiv _ _ (f.{u,v} (I := I))).app (op V) x = x := by
    apply Subtype.ext
    apply ULift.ext
    change weight V * x.val.down = x.val.down
    simp [weight, hV]
  rw [← hx]
  exact cofork_app_f c V x

/-- The same vanishing after restricting a cokernel-arrow image to an open
without leaves. -/
theorem restrict_cofork_eq_zero_of_not_leaf (c : CokernelCofork (f.{u,v} (I := I)))
    {V W : StarOpen I} (h : W.obj ≤ V.obj) (hW : ¬ Leaf W)
    (x : Sections (G.{u,v} (I := I)).obj.obj V) :
    restriction c.pt.obj.obj h ((sheafHomEquiv _ _ c.π).app (op V) x) = 0 :=
  (restriction_naturality_apply _ h x).symm.trans (cofork_app_eq_zero_of_not_leaf c hW _)

/-- The integer coefficient of the `i`-th leaf family on a member of `starCover`. -/
noncomputable def leafValue (i : I) (a : Option I) : ℤ := by
  classical
  exact if a = some i then 1 else 0

theorem leafValue_self (i : I) : leafValue i (some i) = 1 := by
  simp [leafValue]

theorem leafValue_ne {i j : I} (h : j ≠ i) : leafValue i (some j) = 0 := by
  simp [leafValue, h]

/-- The image under the cofork arrow of the integer section `δ_{a,i}`. -/
noncomputable def leafFamily (c : CokernelCofork (f.{u,v} (I := I))) (i : I)
    (a : Option I) : Sections c.pt.obj.obj (starCover a) :=
  (sheafHomEquiv _ _ c.π).app (op (starCover a))
    (intSection (starCover a) (live_starCover a) (leafValue i a))

/-- A member of `starCover` containing a leaf point is the `U` of that leaf. -/
theorem starCover_eq_of_mem {a : Option I} {k : I} (h : some k ∈ (starCover a).obj) :
    a = some k := by
  cases a with
  | none =>
    change some k ∈ (E I).obj at h
    exact False.elim (Option.some_ne_none k ((mem_E _).mp h))
  | some j =>
    change some k ∈ (U I j).obj at h
    rcases (mem_U j _).mp h with h | h
    · exact False.elim (Option.some_ne_none k h)
    · rw [Option.some.inj h]

theorem leafFamily_compatible (c : CokernelCofork (f.{u,v} (I := I))) (i : I) :
    Compatible c.pt.obj.obj starCover (leafFamily c i) := by
  intro a b W hWa hWb
  by_cases hW : Leaf W
  · obtain ⟨k, hk⟩ := hW
    obtain rfl := starCover_eq_of_mem (hWa hk)
    obtain rfl := starCover_eq_of_mem (hWb hk)
    rfl
  · exact (restrict_cofork_eq_zero_of_not_leaf c hWa hW _).trans
      (restrict_cofork_eq_zero_of_not_leaf c hWb hW _).symm

theorem starCover_le (a : Option I) : (starCover a).obj ≤ (whole I).obj := le_whole _

/-- The global section of the cokernel vertex glued from the `i`-th leaf family. -/
noncomputable def leafSection (c : CokernelCofork (f.{u,v} (I := I))) (i : I) :
    Sections c.pt.obj.obj (whole I) :=
  (c.pt.unique_gluing (whole I) starCover starCover_covers (leafFamily c i)
    (leafFamily_compatible c i)).exists.choose

theorem leafSection_restrict (c : CokernelCofork (f.{u,v} (I := I))) (i : I)
    (a : Option I) :
    restriction c.pt.obj.obj (starCover_le a) (leafSection c i) = leafFamily c i a :=
  (c.pt.unique_gluing (whole I) starCover starCover_covers (leafFamily c i)
    (leafFamily_compatible c i)).exists.choose_spec a

/-- A factorization of `g` through the cofork arrow, evaluated on a section. -/
theorem factor_apply (c : CokernelCofork (f.{u,v} (I := I)))
    {T : BasisSheaf.{u,v} (allOpenBasis (Option I))} {g : G.{u,v} (I := I) ⟶ T}
    (φ : c.pt ⟶ T) (hφ : c.π ≫ φ = g) (V : StarOpen I)
    (x : Sections (G.{u,v} (I := I)).obj.obj V) :
    (sheafHomEquiv _ _ φ).app (op V) ((sheafHomEquiv _ _ c.π).app (op V) x) =
      (sheafHomEquiv _ _ g).app (op V) x := by
  subst hφ
  rfl

theorem mem_starCover_some (i : I) : some i ∈ (starCover (some i)).obj :=
  (mem_U i _).mpr (Or.inr rfl)

/-- The colimit factorization of `gi i` detects the `i`-th glued section on `U i`. -/
theorem leafSection_detect (c : CokernelCofork (f.{u,v} (I := I))) (hc : IsColimit c)
    (i j : I) :
    (sheafHomEquiv _ _
        (CokernelCofork.IsColimit.desc' hc (gi.{u,v} i) (f_comp_gi_eq_zero i)).1).app
        (op (starCover (some i)))
        (restriction c.pt.obj.obj (starCover_le (some i)) (leafSection c j)) =
      modSection i (starCover (some i)) (mem_starCover_some i)
        (leafValue j (some i) : ZMod 2) := by
  rw [leafSection_restrict]
  exact (factor_apply c _ (CokernelCofork.IsColimit.desc' hc (gi.{u,v} i)
    (f_comp_gi_eq_zero i)).2 _ _).trans
      (gi_apply_section i (starCover (some i)) (mem_starCover_some i) _)

theorem leafSection_injective (c : CokernelCofork (f.{u,v} (I := I))) (hc : IsColimit c) :
    Function.Injective (leafSection c) := by
  intro i j hij
  by_contra hne
  have h := leafSection_detect c hc i i
  rw [hij, leafSection_detect c hc i j] at h
  have he := congrArg
    (fun s : PointSections.{u,v} i (starCover (some i)) => s.val.down) h
  simp only [modSection_val, leafValue_self, leafValue_ne hne, Int.cast_zero,
    Int.cast_one] at he
  exact zero_ne_one he

end Injection

/-- Every actual colimit cokernel cofork of the star map has at least `I`
distinct global sections. -/
theorem cokernelSectionInjection : CokernelSectionInjectionStatement.{u,v} := by
  intro I c hc
  exact ⟨⟨leafSection c, leafSection_injective c hc⟩⟩

/-- A cokernel in the undersized category would make `Type v` small. -/
theorem undersizedNoCokernel : UndersizedNoCokernelStatement.{v} := by
  intro h
  obtain ⟨e⟩ := cokernelSectionInjection.{v + 1, v} (Type v) _
    (cokernelIsCokernel _)
  exact not_small_type.{v, v} (small_of_injective e.injective)

/-- Cokernel existence does not depend on which zero-morphism structure is used,
since such a structure on a category is unique. -/
theorem hasCokernel_of_hasZeroMorphisms_eq {C : Type*} [Category C]
    (Z₁ Z₂ : HasZeroMorphisms C) {X Y : C} (g : X ⟶ Y)
    (h : @HasCokernel C _ Z₁ X Y g) : @HasCokernel C _ Z₂ X Y g := by
  obtain rfl : Z₁ = Z₂ := Subsingleton.elim _ _
  exact h

/-- An abelian structure would supply the forbidden cokernel. -/
theorem undersizedNotAbelian : UndersizedNotAbelianStatement.{v} := by
  intro ⟨A⟩
  apply undersizedNoCokernel
  exact hasCokernel_of_hasZeroMorphisms_eq _ _ _ (@Abelian.has_cokernels _ _ A |>.has_colimit _)

/-- The exact closed aggregate target. -/
theorem cokernelScopeStatements : CokernelScopeStatements.{u,v} :=
  ⟨cokernelSectionInjection, undersizedNoCokernel, undersizedNotAbelian⟩

end Langlands.Sheaf.Renard.StarDiagram
