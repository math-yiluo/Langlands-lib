import Langlands.Algebra.RegularTensorContractionNaturality

/-!
# The canonical regular-tensor comparison

Proof of the published closed comparison target, using the original quotient,
regular bimodule action, and a common local unit for finite tensor expressions.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uM uN

namespace RegularTensorContraction

variable (A : Type uA) (M : Type uM) [NonUnitalRing A]
  [AddCommGroup M] [NonUnitalModule A M]

local instance : NonUnitalModule Aᵐᵒᵖ A := NonUnitalModule.rightRegular A
local instance : NonUnitalModule A (Tensor A M) := tensorModule A M

@[simp] theorem contraction_pure (a : A) (m : M) :
    contraction A M (pure A M a m) = a • m := rfl

@[simp] theorem smul_pure (a b : A) (m : M) :
    a • pure A M b m = pure A M (a * b) m := rfl

theorem pure_add (a : A) (m n : M) :
    pure A M a (m + n) = pure A M a m + pure A M a n :=
  NonUnitalModuleTensor.tmul_add A A M a m n

@[simp] theorem pure_zero (a : A) : pure A M a 0 = 0 :=
  NonUnitalModuleTensor.tmul_zero A A M a

/-- The specified contraction respects the actual residual left action. -/
theorem contraction_smul (a : A) (t : Tensor A M) :
    contraction A M (a • t) = a • contraction A M t := by
  have h : (contraction A M).comp
        (NonUnitalModule.toEndHom (tensorModule A M) a) =
      (NonUnitalModule.toEndHom ‹NonUnitalModule A M› a).comp (contraction A M) := by
    apply NonUnitalModuleTensor.hom_ext A
    intro b m
    change (a * b) • m = a • (b • m)
    exact mul_smul a b m
  exact DFunLike.congr_fun h t

/-- Above one common local unit, every tensor is a pure tensor of its contraction. -/
theorem exists_normal_form (hA : IsIdempotented A) (t : Tensor A M) :
    ∃ e : Idempotent A, ∀ f : Idempotent A, e ≤ f →
      pure A M (f : A) (contraction A M t) = t := by
  classical
  obtain ⟨q, rfl⟩ := NonUnitalModuleTensor.projection_surjective A A M t
  refine TensorProduct.inductionOn q ?_ ?_
  · intro a m
    obtain ⟨e, he⟩ := hA.exists_mem_corner a
    have hea := ((Idempotent.mem_corner_iff e a).mp he).1
    refine ⟨e, fun f hef => ?_⟩
    change pure A M (f : A) (a • m) = pure A M a m
    calc
      pure A M (f : A) (a • m) = pure A M ((f : A) * a) m :=
        (NonUnitalModuleTensor.tmul_balanced A A M a (f : A) m).symm
      _ = pure A M a m := by rw [Idempotent.mul_eq_of_le hef hea]
  · intro q r hq hr
    obtain ⟨e, he⟩ := hq
    obtain ⟨f, hf⟩ := hr
    obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
    refine ⟨g, fun k hgk => ?_⟩
    rw [map_add, map_add, pure_add]
    rw [he k (le_trans (hg e (by simp)) hgk),
      hf k (le_trans (hg f (by simp)) hgk)]

/-- The common-local-unit normal form gives a zero kernel. -/
theorem contraction_injective (hA : IsIdempotented A) :
    Function.Injective (contraction A M) := by
  intro s t hst
  obtain ⟨e, he⟩ := exists_normal_form A M hA (s - t)
  have hz : contraction A M (s - t) = 0 := by rw [map_sub, hst, sub_self]
  have h := he e le_rfl
  rw [hz, pure_zero] at h
  exact sub_eq_zero.mp h.symm

/-- Every contraction value lies in the actual original nondegenerate part. -/
theorem contraction_mem (hA : IsIdempotented A) (t : Tensor A M) :
    contraction A M t ∈ nondegeneratePart hA M := by
  obtain ⟨e, he⟩ := exists_normal_form A M hA t
  refine ⟨e, ?_⟩
  have h := congrArg (contraction A M) (he e le_rfl)
  exact h

/-- The additive image is exactly the original part, even for degenerate ambient modules. -/
theorem contraction_range (hA : IsIdempotented A) :
    (contraction A M).range = (nondegeneratePart hA M).toAddSubgroup := by
  ext m
  constructor
  · rintro ⟨t, rfl⟩
    exact contraction_mem A M hA t
  · intro hm
    obtain ⟨e, he⟩ := hm
    exact ⟨pure A M (e : A) m, he⟩

/-- A bijective original intertwiner has an inverse original intertwiner. -/
private theorem exists_module_inverse {X : Type uM} {Y : Type uN}
    [AddCommGroup X] [AddCommGroup Y]
    [NonUnitalModule A X] [NonUnitalModule A Y]
    (F : NonUnitalModuleHom A X Y) (hF : Function.Bijective F) :
    ∃ G : NonUnitalModuleHom A Y X,
      G.comp F = NonUnitalModuleHom.id A X ∧
      F.comp G = NonUnitalModuleHom.id A Y := by
  classical
  let E : X ≃+ Y := AddEquiv.ofBijective F.toAddMonoidHom hF
  let G : NonUnitalModuleHom A Y X :=
    { toAddMonoidHom := E.symm.toAddMonoidHom
      map_smul' := by
        intro a y
        apply E.injective
        change E (E.symm (a • y)) = F (a • E.symm y)
        rw [E.apply_symm_apply, NonUnitalModuleHom.map_smul]
        change a • y = a • E (E.symm y)
        rw [E.apply_symm_apply] }
  refine ⟨G, ?_, ?_⟩
  · apply NonUnitalModuleHom.ext
    intro x
    exact E.symm_apply_apply x
  · apply NonUnitalModuleHom.ext
    intro y
    exact E.apply_symm_apply y

/-- The contraction factors through the actual part as an isomorphism. -/
theorem has_comparison (hA : IsIdempotented A) : HasComparison A M hA := by
  let F : Forward A M hA :=
    { toFun := fun t => ⟨contraction A M t, contraction_mem A M hA t⟩
      map_zero' := Subtype.ext (map_zero (contraction A M))
      map_add' := fun s t => Subtype.ext (map_add (contraction A M) s t)
      map_smul' := fun a t => Subtype.ext (contraction_smul A M a t) }
  have hF : Function.Bijective F := by
    constructor
    · intro s t h
      exact contraction_injective A M hA (congrArg Subtype.val h)
    · intro m
      obtain ⟨e, he⟩ := m.property
      exact ⟨pure A M (e : A) m.val, Subtype.ext he⟩
  obtain ⟨G, hGF, hFG⟩ := exists_module_inverse A F hF
  refine ⟨F, G, rfl, hGF, hFG, ?_⟩
  intro m e he
  apply contraction_injective A M hA
  change (F (G m)).val = (e : A) • m.val
  have hm : F (G m) = m :=
    congrArg (fun H : NonUnitalModuleHom A (nondegeneratePart hA M)
      (nondegeneratePart hA M) => H m) hFG
  rw [hm, he]

/-- Only nondegeneracy of the ambient module permits a whole-module comparison. -/
theorem nondegenerate_comparison (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    NondegenerateComparison A M := by
  let F : NonUnitalModuleHom A (Tensor A M) M :=
    { toAddMonoidHom := contraction A M
      map_smul' := contraction_smul A M }
  have hF : Function.Bijective F := by
    constructor
    · exact contraction_injective A M hA
    · intro m
      obtain ⟨e, he⟩ := hM m
      exact ⟨pure A M (e : A) m, he⟩
  obtain ⟨G, hGF, hFG⟩ := exists_module_inverse A F hF
  refine ⟨F, G, rfl, hGF, hFG, ?_⟩
  intro m e he
  apply hF.1
  change F (G m) = (e : A) • m
  have hm : F (G m) = m :=
    congrArg (fun H : NonUnitalModuleHom A M M => H m) hFG
  rw [hm, he]

/-- All comparison clauses for one arbitrary original ambient module. -/
theorem module_comparison (hA : IsIdempotented A) : ModuleComparison A M hA :=
  ⟨⟨contraction_pure A M, contraction_smul A M,
      contraction_injective A M hA, contraction_range A M hA⟩,
    has_comparison A M hA, nondegenerate_comparison A M hA⟩

end RegularTensorContraction

/-- The canonical comparison for arbitrary original modules and independent universes. -/
theorem regularTensorContraction : RegularTensorContractionTheorem.{uA, uM, uN} := by
  intro A _ hA
  refine ⟨?_, ?_, ?_⟩
  · intro M _ _
    exact RegularTensorContraction.module_comparison A M hA
  · intro N _ _
    exact RegularTensorContraction.module_comparison A N hA
  · intro M _ _ N _ _ f
    exact ⟨RegularTensorContraction.contraction_naturality A f,
      RegularTensorContraction.comparison_naturality A hA f⟩

end Langlands.Algebra
