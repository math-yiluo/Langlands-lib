import Langlands.Automorphic.CuspidalWhittaker.WhittakerCoefficient
import Langlands.Automorphic.LocalRealization
import Langlands.Group.GL.UpperUnipotent

/-!
# A local Whittaker functional on an embedded cuspidal local component

Let `S` be a nonzero `GL_{r+1}(K_v)`-stable space of cuspidal automorphic forms. Choose a form
`φ ∈ S` and `g ∈ GL_{r+1}(𝔸_K)` with `W_φ(g) ≠ 0`, write `g = h · ι_v(g_v)` with `h` trivial at
`v`, and put `ℓ(x) = W_x(h)`. Then `ℓ` is a nonzero linear form on `S` with
`ℓ(π(u) x) = χ_v(∑ᵢ u_{i,i+1}) ℓ(x)` for every upper unitriangular `u ∈ GL_{r+1}(K_v)`, where
`χ_v` is the local component of the standard character of `𝔸_K / K`.
-/

noncomputable section

set_option linter.unusedSectionVars false

universe u

namespace Langlands.Automorphic.CuspidalWhittaker

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Automorphic.ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {v : Global.FinitePlace F} {r : ℕ}

attribute [local instance] Langlands.Automorphic.localRealizationRationalAddCommGroup
  Langlands.Automorphic.localRealizationContinuousAddCommGroup
  Langlands.Automorphic.localRealizationSmoothAddCommGroup
  Langlands.Automorphic.localRealizationFormsAddCommGroup
  Langlands.Automorphic.LocalRealization.localRealizationSpaceAddCommGroup

/-! ### Entries of local elements of `GL_{r+1}(𝔸_K)` -/

theorem localInclusion_apply_apply (u : FiniteLocalGL F (r + 1) v) (i j : Fin (r + 1))
    (w : Global.FinitePlace F) :
    (localInclusion F (r + 1) v u) i j w = localProjection F (r + 1) w (localInclusion F (r + 1) v u) i j :=
  rfl

theorem ofFinite_localInclusion_eq_one {u : FiniteLocalGL F (r + 1) v} {i j : Fin (r + 1)}
    (h : u i j = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteCompletion F v)) i j) :
    (AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v u)).val i j =
      (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i j := by
  refine adeles_ext ?_ ?_
  · change (1 : InfiniteAdelicGL F (r + 1)).val i j = _
    rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · change (localInclusion F (r + 1) v u) i j = _
    refine IsDedekindDomain.FiniteAdeleRing.ext F fun w => ?_
    rw [localInclusion_apply_apply]
    by_cases hw : w = v
    · subst hw
      rw [localProjection_localInclusion, h, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · rw [localProjection_localInclusion_of_ne F (r + 1) v w hw, Units.val_one, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs <;> rfl

theorem ofFinite_localInclusion_offDiag (u : FiniteLocalGL F (r + 1) v) {i j : Fin (r + 1)}
    (hij : i ≠ j) :
    (AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v u)).val i j =
      finiteToAdeles F (finiteSingle F v (u i j)) := by
  refine adeles_ext ?_ ?_
  · change (1 : InfiniteAdelicGL F (r + 1)).val i j = 0
    rw [Units.val_one, Matrix.one_apply_ne hij]
  · change (localInclusion F (r + 1) v u) i j = finiteSingle F v (u i j)
    refine IsDedekindDomain.FiniteAdeleRing.ext F fun w => ?_
    rw [localInclusion_apply_apply]
    by_cases hw : w = v
    · subst hw
      rw [localProjection_localInclusion, finiteSingle_apply_same]
    · rw [localProjection_localInclusion_of_ne F (r + 1) v w hw, Units.val_one,
        Matrix.one_apply_ne hij, finiteSingle_apply_ne F hw]

theorem isUpperColId_ofFinite (u : GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v)) :
    IsUpperColId 0 (AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v u.val)).val := by
  intro i j hij
  have hji : j ≤ i := by
    rcases hij with h | h
    · exact Fin.le_def.mpr h
    · exact Fin.le_def.mpr (by omega)
  refine ofFinite_localInclusion_eq_one ?_
  rcases lt_or_eq_of_le hji with hlt | heq
  · rw [GeneralLinear.UpperUnipotent.entry_eq_zero u hlt, Matrix.one_apply_ne (ne_of_gt hlt)]
  · subst heq
    rw [GeneralLinear.UpperUnipotent.entry_diag, Matrix.one_apply_eq]

theorem superSum_ofFinite (u : GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v)) :
    superSum 0 (AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v u.val)) =
      finiteToAdeles F (finiteSingle F v (∑ i : Fin r, u.val i.castSucc i.succ)) := by
  unfold superSum
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ite_eq_left (Nat.zero_le _), ofFinite_localInclusion_offDiag]
  exact fun e => by
    have := congrArg Fin.val e
    simp at this

/-- Elements trivial at `v` commute with the image of `GL_{r+1}(K_v)`. -/
theorem ofFinite_localInclusion_commute {h0 : AdelicGL F (r + 1)}
    (hv : localProjection F (r + 1) v (AdelicGL.finite F (r + 1) h0) = 1)
    (u : FiniteLocalGL F (r + 1) v) :
    h0 * AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v u) =
      AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v u) * h0 := by
  apply (AdelicGL.split F (r + 1)).injective
  rw [map_mul, map_mul]
  refine Prod.ext ?_ ?_
  · change AdelicGL.infinite F (r + 1) h0 * AdelicGL.infinite F (r + 1)
        (AdelicGL.pair F (r + 1) 1 (localInclusion F (r + 1) v u)) =
      AdelicGL.infinite F (r + 1) (AdelicGL.pair F (r + 1) 1 (localInclusion F (r + 1) v u)) *
        AdelicGL.infinite F (r + 1) h0
    rw [AdelicGL.infinite_pair, mul_one, one_mul]
  · change AdelicGL.finite F (r + 1) h0 * AdelicGL.finite F (r + 1)
        (AdelicGL.pair F (r + 1) 1 (localInclusion F (r + 1) v u)) =
      AdelicGL.finite F (r + 1) (AdelicGL.pair F (r + 1) 1 (localInclusion F (r + 1) v u)) *
        AdelicGL.finite F (r + 1) h0
    rw [AdelicGL.finite_pair]
    apply ext_localProjection
    intro w
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [hv, one_mul, mul_one]
    · rw [localProjection_localInclusion_of_ne F (r + 1) v w hw, mul_one, one_mul]

/-! ### The local functional -/

variable (S : LocalRealization F (r + 1) v)

theorem levelProps_form (hS : S.IsCuspidal) (x : S.Space) :
    LevelProps r (evaluate F (r + 1) (S.toContinuous x)) :=
  levelProps_top _ fun _ _ h ha hb g => S.constantTerm_eq_zero hS h ha hb x g

theorem descend_representation (g : FiniteLocalGL F (r + 1) v) (x : S.Space)
    (a : AdelicGL F (r + 1)) :
    descend r (evaluate F (r + 1) (S.toContinuous (S.representation g x))) a =
      descend r (evaluate F (r + 1) (S.toContinuous x))
        (a * AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v g)) := by
  rw [show evaluate F (r + 1) (S.toContinuous (S.representation g x)) = fun a' =>
      evaluate F (r + 1) (S.toContinuous x)
        (a' * AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v g)) from
    funext fun a' => S.evaluate_representation g x a']
  exact descend_mul_right r _ _ a



theorem evaluate_toContinuous_add (x y : S.Space) (a : AdelicGL F (r + 1)) :
    evaluate F (r + 1) (S.toContinuous (x + y)) a =
      evaluate F (r + 1) (S.toContinuous x) a + evaluate F (r + 1) (S.toContinuous y) a :=
  congrArg (fun f => evaluate F (r + 1) f a) (map_add S.toContinuous x y)

theorem evaluate_toContinuous_smul (c : ℂ) (x : S.Space) (a : AdelicGL F (r + 1)) :
    evaluate F (r + 1) (S.toContinuous (c • x)) a = c * evaluate F (r + 1) (S.toContinuous x) a :=
  congrArg (fun f => evaluate F (r + 1) f a) (map_smul S.toContinuous c x)

/-- Every adelic element is `h · ι_v(g_v)` with `h` trivial at `v`. -/
theorem exists_trivial_at_mul (g0 : AdelicGL F (r + 1)) :
    ∃ (h0 : AdelicGL F (r + 1)) (gv : FiniteLocalGL F (r + 1) v),
      localProjection F (r + 1) v (AdelicGL.finite F (r + 1) h0) = 1 ∧
        h0 * AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v gv) = g0 := by
  refine ⟨g0 * (AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v
    (localProjection F (r + 1) v (AdelicGL.finite F (r + 1) g0))))⁻¹,
    localProjection F (r + 1) v (AdelicGL.finite F (r + 1) g0), ?_, inv_mul_cancel_right _ _⟩
  rw [map_mul, map_inv, map_mul, map_inv]
  change _ * (localProjection F (r + 1) v (AdelicGL.finite F (r + 1)
    (AdelicGL.pair F (r + 1) 1 (localInclusion F (r + 1) v _))))⁻¹ = 1
  rw [AdelicGL.finite_pair, localProjection_localInclusion, mul_inv_cancel]

/-- The linear form `x ↦ W_x(h)`. -/
def whittakerFunctional (hS : S.IsCuspidal) (h0 : AdelicGL F (r + 1)) : Module.Dual ℂ S.Space where
  toFun x := descend r (evaluate F (r + 1) (S.toContinuous x)) h0
  map_add' x y := by
    rw [show evaluate F (r + 1) (S.toContinuous (x + y)) = fun a =>
        evaluate F (r + 1) (S.toContinuous x) a + evaluate F (r + 1) (S.toContinuous y) a from
      funext (evaluate_toContinuous_add S x y)]
    exact descend_add r le_rfl _ _ (levelProps_form S hS x) (levelProps_form S hS y) h0
  map_smul' c x := by
    rw [show evaluate F (r + 1) (S.toContinuous (c • x)) = fun a =>
        c * evaluate F (r + 1) (S.toContinuous x) a from
      funext (evaluate_toContinuous_smul S c x)]
    exact descend_const_mul r c _ h0

theorem whittakerFunctional_apply (hS : S.IsCuspidal) (h0 : AdelicGL F (r + 1)) (x : S.Space) :
    whittakerFunctional S hS h0 x = descend r (evaluate F (r + 1) (S.toContinuous x)) h0 := rfl



theorem whittakerFunctional_equivariant (hS : S.IsCuspidal) {h0 : AdelicGL F (r + 1)}
    (hv : localProjection F (r + 1) v (AdelicGL.finite F (r + 1) h0) = 1)
    (u : GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v)) (x : S.Space) :
    whittakerFunctional S hS h0 (S.representation u.val x) =
      (localCharacter F v (∑ i : Fin r, u.val i.castSucc i.succ) : ℂ) *
        whittakerFunctional S hS h0 x := by
  have hL : LevelProps 0 (descend r (evaluate F (r + 1) (S.toContinuous x))) :=
    levelProps_descend (K := F) (r := r) r le_rfl (evaluate F (r + 1) (S.toContinuous x))
      (levelProps_form S hS x)
  have he := hL.equivariant (AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v u.val)) h0
    (isUpperColId_ofFinite u)
  rw [superSum_ofFinite] at he
  calc whittakerFunctional S hS h0 (S.representation u.val x)
      = descend r (evaluate F (r + 1) (S.toContinuous (S.representation u.val x))) h0 :=
        whittakerFunctional_apply S hS h0 _
    _ = descend r (evaluate F (r + 1) (S.toContinuous x))
          (h0 * AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v u.val)) :=
        descend_representation S u.val x h0
    _ = descend r (evaluate F (r + 1) (S.toContinuous x))
          (AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v u.val) * h0) :=
        congrArg (descend r (evaluate F (r + 1) (S.toContinuous x)))
          (ofFinite_localInclusion_commute hv u.val)
    _ = (adelicCharacter F (finiteToAdeles F
          (finiteSingle F v (∑ i : Fin r, u.val i.castSucc i.succ))) : ℂ) *
          descend r (evaluate F (r + 1) (S.toContinuous x)) h0 := he
    _ = (localCharacter F v (∑ i : Fin r, u.val i.castSucc i.succ) : ℂ) *
          whittakerFunctional S hS h0 x :=
        congrArg₂ (fun (t : Circle) (z : ℂ) => (t : ℂ) * z) (localCharacter_apply F v _).symm
          (whittakerFunctional_apply S hS h0 x).symm

theorem exists_ne_zero_of_ne_bot (hne : S ≠ ⊥) : ∃ x : S.Space, x ≠ 0 := by
  by_contra h
  apply hne
  apply Subrepresentation.toSubmodule_injective
  show S.toSubmodule = ⊥
  rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  exact h ⟨⟨x, hx⟩, fun e => hx0 (congrArg Subtype.val e)⟩

theorem exists_evaluate_ne_zero {x : S.Space} (hx : x ≠ 0) :
    ∃ g, evaluate F (r + 1) (S.toContinuous x) g ≠ 0 := by
  by_contra h'
  have h : ∀ g, evaluate F (r + 1) (S.toContinuous x) g = 0 := fun g => by
    by_contra hg
    exact h' ⟨g, hg⟩
  apply hx
  apply S.toContinuous_injective
  rw [map_zero S.toContinuous]
  apply toContinuousMap_injective F (r + 1)
  rw [map_zero (toContinuousMap F (r + 1))]
  ext g
  exact h g

theorem whittakerFunctional_ne_zero (hS : S.IsCuspidal) {h0 : AdelicGL F (r + 1)}
    {gv : FiniteLocalGL F (r + 1) v} {x : S.Space}
    (hg : descend r (evaluate F (r + 1) (S.toContinuous x))
      (h0 * AdelicGL.ofFinite F (r + 1) (localInclusion F (r + 1) v gv)) ≠ 0) :
    whittakerFunctional S hS h0 ≠ 0 := by
  intro hℓ
  exact hg ((descend_representation S gv x h0).symm.trans
    ((whittakerFunctional_apply S hS h0 _).symm.trans
      ((LinearMap.congr_fun hℓ (S.representation gv x)).trans (LinearMap.zero_apply _))))

/-- **Existence of a local Whittaker functional** on a nonzero embedded cuspidal component. -/
theorem exists_localWhittakerFunctional (hS : S.IsCuspidal) (hne : S ≠ ⊥) :
    ∃ ℓ : Module.Dual ℂ S.Space, ℓ ≠ 0 ∧
      ∀ (u : GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v)) (x : S.Space),
        ℓ (S.representation u.val x) =
          (localCharacter F v (∑ i : Fin r, u.val i.castSucc i.succ) : ℂ) * ℓ x := by
  refine (exists_ne_zero_of_ne_bot S hne).elim fun x0 hx0 => ?_
  refine (exists_descend_ne_zero (K := F) (r := r) r le_rfl
    (evaluate F (r + 1) (S.toContinuous x0)) (levelProps_form S hS x0)
    (exists_evaluate_ne_zero S hx0)).elim fun g0 hg0 => ?_
  refine (exists_trivial_at_mul (v := v) g0).elim fun h0 hh0 => hh0.elim fun gv hgv => ?_
  refine ⟨whittakerFunctional S hS h0, whittakerFunctional_ne_zero S hS (gv := gv) (x := x0) ?_,
    whittakerFunctional_equivariant S hS hgv.1⟩
  rw [hgv.2]
  exact hg0

end Langlands.Automorphic.CuspidalWhittaker
