import Langlands.Algebra.RenardForgetfulFunctorStatements
import Langlands.Algebra.RegularTensorContraction

/-!
# Renard I.2.3: restriction, coextension and the forgetful comparisons

Proof of the published statements, with all three universes independent.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MulOpposite

namespace Langlands.Algebra.RenardForgetfulFunctor

universe uA uB uM

/-- The published unital adjunction, including its specified Hom formula. -/
theorem unitalCoextensionAdjunction :
    UnitalCoextensionAdjunctionStatement.{uA, uB, uM} := by
  intro A B _ _ φ
  refine ⟨ModuleCat.restrictCoextendScalarsAdj φ, ?_⟩
  intro N M g n b
  rfl

section LocalUnits

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  (φ : A →ₙ+* B) (hφ : NonUnitalModuleRestrictScalars.HasTwoSidedLocalUnits φ)

/-- Multiplicativity sends the actual idempotents to actual idempotents. -/
def imageIdempotent (e : Idempotent A) : Idempotent B :=
  ⟨φ (e : A), by
    change φ (e : A) * φ (e : A) = φ (e : A)
    exact (map_mul φ _ _).symm.trans (congrArg φ e.property.eq)⟩

include hφ

/-- The two-sided local units give the target ring's finite-corner property. -/
theorem target_isIdempotented : IsIdempotented B := by
  intro s
  obtain ⟨e, he⟩ := hφ s
  refine ⟨imageIdempotent φ e, ?_⟩
  intro b hb
  change φ (e : A) * b * φ (e : A) = b
  rw [(he b hb).1, (he b hb).2]

/-- The image idempotents bound every finite family of target idempotents. -/
theorem image_filtering (s : Finset (Idempotent B)) :
    ∃ e : Idempotent A,
      ∀ f ∈ s, φ (e : A) * (f : B) = f ∧ (f : B) * φ (e : A) = f := by
  classical
  obtain ⟨e, he⟩ := hφ (s.image (fun f : Idempotent B => (f : B)))
  exact ⟨e, fun f hf => he f (Finset.mem_image.mpr ⟨f, hf, rfl⟩)⟩

/-- Being fixed by an idempotent is unchanged by scalar restriction. -/
theorem fixed_iff (M : Type uM) [AddCommGroup M] [NonUnitalModule B M] (m : M) :
    (∃ e : Idempotent B, (e : B) • m = m) ↔
      ∃ e : Idempotent A, φ (e : A) • m = m := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨e, he⟩ := hφ {(f : B)}
    refine ⟨e, ?_⟩
    calc
      φ (e : A) • m = φ (e : A) • ((f : B) • m) := congrArg _ hf.symm
      _ = m := by rw [← mul_smul, (he f (by simp)).1, hf]
  · rintro ⟨e, he⟩
    exact ⟨imageIdempotent φ e, he⟩

end LocalUnits

/-- An additive bijective intertwiner gives an isomorphism in the full subcategory. -/
private def isoOfBijective {A : Type uA} [NonUnitalRing A]
    {M N : NondegenerateModuleCat.{uA, uM} A}
    (f : NonUnitalModuleHom A M.obj N.obj) (hf : Function.Bijective f) : M ≅ N := by
  let E : M.obj ≃+ N.obj := AddEquiv.ofBijective f.toAddMonoidHom hf
  let g : NonUnitalModuleHom A N.obj M.obj :=
    { toAddMonoidHom := E.symm.toAddMonoidHom
      map_smul' := by
        intro a n
        apply E.injective
        change E (E.symm (a • n)) = f (a • E.symm n)
        rw [E.apply_symm_apply, f.map_smul]
        change a • n = a • E (E.symm n)
        rw [E.apply_symm_apply] }
  exact
    { hom := ObjectProperty.homMk f
      inv := ObjectProperty.homMk g
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        apply NonUnitalModuleHom.ext
        intro m
        exact E.symm_apply_apply m
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        apply NonUnitalModuleHom.ext
        intro n
        exact E.apply_symm_apply n }

/-- The specified tensor functor contracts naturally to scalar restriction. -/
theorem tensorForgetfulRemark {A : Type uA} {B : Type uB}
    [NonUnitalRing A] [NonUnitalRing B] (hA : IsIdempotented A)
    (φ : A →ₙ+* B) (hφ : NonUnitalModuleRestrictScalars.HasTwoSidedLocalUnits φ) :
    TensorForgetfulRemark.{uA, uB, uM} A B hA φ hφ := by
  classical
  let : NonUnitalModule A B :=
    NonUnitalModuleRestrictScalars.module φ (NonUnitalModule.regular B)
  let : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
  have hB := target_isIdempotented φ hφ
  have hLeft := NonUnitalModuleRestrictScalars.HasTwoSidedLocalUnits.hasLeftLocalUnits φ hφ
  change ActionsCommute A B B ∧ IsNondegenerateBimodule A B B ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro a b c
    change φ a * (c * b) = (φ a * c) * b
    exact (mul_assoc _ _ _).symm
  · exact ⟨hLeft, NondegenerateTensorFunctor.rightRegular_isNondegenerate hB⟩
  · intro hAB hnd
    let F := NondegenerateTensorFunctor.F.{uA, uB, max uB uM} hA hAB hnd
    let R := NonUnitalModuleRestrictScalars.nondegenerateFunctor.{uA, uB, max uB uM}
      φ hLeft
    let c (N : NondegenerateModuleCat.{uB, max uB uM} B) :
        NonUnitalModuleHom A (F.obj N).obj (R.obj N).obj :=
      { toAddMonoidHom := RegularTensorContraction.contraction B N.obj
        map_smul' := by
          intro a t
          have h :
              (RegularTensorContraction.contraction B N.obj).comp
                (NonUnitalModule.toEndHom
                  (NonUnitalBimoduleTensor.leftModule hAB N.obj) a) =
              (NonUnitalModule.toEndHom N.obj.isModule (φ a)).comp
                (RegularTensorContraction.contraction B N.obj) := by
            apply NonUnitalModuleTensor.hom_ext B
            intro b n
            change (φ a * b) • n = φ a • (b • n)
            exact mul_smul _ _ _
          exact DFunLike.congr_fun h t }
    have hc (N : NondegenerateModuleCat.{uB, max uB uM} B) : Function.Bijective (c N) := by
      refine ⟨RegularTensorContraction.contraction_injective B N.obj hB, ?_⟩
      intro n
      obtain ⟨e, he⟩ := N.property n
      exact ⟨RegularTensorContraction.pure B N.obj (e : B) n, he⟩
    exact ⟨NatIso.ofComponents (fun N => isoOfBijective (c N) (hc N)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      apply NonUnitalModuleHom.ext
      intro t
      exact DFunLike.congr_fun (RegularTensorContraction.contraction_naturality B f.hom) t)⟩

/-- The nondegenerate regular-source Hom is naturally the restricted module. -/
theorem pseudoForgetfulRemark {A : Type uA} {B : Type uB}
    [NonUnitalRing A] [NonUnitalRing B] (hA : IsIdempotented A)
    (φ : A →ₙ+* B) (hφ : NonUnitalModuleRestrictScalars.HasTwoSidedLocalUnits φ) :
    PseudoForgetfulRemark.{uA, uB, uM} A B hA φ hφ := by
  classical
  let : NonUnitalModule Aᵐᵒᵖ B :=
    NonUnitalModuleRestrictScalars.module (NonUnitalRingHom.op φ)
      (NonUnitalModule.rightRegular B)
  let : NonUnitalModule B B := NonUnitalModule.regular B
  have hB := target_isIdempotented φ hφ
  have hLeft := NonUnitalModuleRestrictScalars.HasTwoSidedLocalUnits.hasLeftLocalUnits φ hφ
  change ActionsCommute B A B ∧ IsNondegenerateBimodule B A B ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro b a c
    change b * (c * φ a) = (b * c) * φ a
    exact (mul_assoc _ _ _).symm
  · refine ⟨NondegenerateTensorFunctor.regular_isNondegenerate hB, ?_⟩
    intro b
    obtain ⟨e, he⟩ := hφ {b}
    exact ⟨⟨op (e : A), congrArg op e.property⟩, (he b (by simp)).2⟩
  · intro hBA
    let P := RenardHomFunctors.pseudoF.{uA, uB, max uB uM} hBA hA
    let R := NonUnitalModuleRestrictScalars.nondegenerateFunctor.{uA, uB, max uB uM}
      φ hLeft
    let actionHom (N : NondegenerateModuleCat.{uB, max uB uM} B) (n : N.obj) :
        NonUnitalModuleHom B B N.obj :=
      { toFun := fun b => b • n
        map_zero' := NonUnitalModule.zero_smul n
        map_add' := fun b c => NonUnitalModule.add_smul b c n
        map_smul' := fun b c => mul_smul b c n }
    let u (N : NondegenerateModuleCat.{uB, max uB uM} B) :
        NonUnitalModuleHom A (R.obj N).obj (P.obj N).obj :=
      { toFun := fun n => ⟨actionHom N n, by
          apply (RenardHomFunctors.mem_pseudoPart hBA hA _).mpr
          obtain ⟨e, he⟩ :=
            (NonUnitalModuleRestrictScalars.isNondegenerate φ hLeft N.property) n
          change φ (e : A) • (show N.obj from n) = n at he
          refine ⟨e, fun b => ?_⟩
          change (b * φ (e : A)) • (show N.obj from n) = b • (show N.obj from n)
          rw [mul_smul, he]⟩
        map_zero' := by
          apply Subtype.ext
          apply NonUnitalModuleHom.ext
          intro b
          change b • (0 : N.obj) = 0
          exact smul_zero b
        map_add' := by
          intro n m
          apply Subtype.ext
          apply NonUnitalModuleHom.ext
          intro b
          change b • ((show N.obj from n) + (show N.obj from m)) =
            b • (show N.obj from n) + b • (show N.obj from m)
          exact smul_add b (show N.obj from n) (show N.obj from m)
        map_smul' := by
          intro a n
          apply Subtype.ext
          apply NonUnitalModuleHom.ext
          intro b
          change b • (φ a • (show N.obj from n)) = (b * φ a) • (show N.obj from n)
          exact (mul_smul _ _ _).symm }
    have hu (N : NondegenerateModuleCat.{uB, max uB uM} B) : Function.Bijective (u N) := by
      constructor
      · intro n m h
        change N.obj at n m
        obtain ⟨e, he⟩ := N.property (n - m)
        have hh := congrArg (fun p : (P.obj N).obj =>
          (show NonUnitalModuleHom B B N.obj from p.val) (e : B)) h
        change (e : B) • n = (e : B) • m at hh
        rw [smul_sub, hh, sub_self] at he
        exact sub_eq_zero.mp he.symm
      · intro ψ
        change RenardHomFunctors.pseudoPart hBA hA N.obj at ψ
        let ψhom : NonUnitalModuleHom B B N.obj := ψ.val
        obtain ⟨e, he⟩ := (RenardHomFunctors.mem_pseudoPart hBA hA ψ.val).mp ψ.property
        refine ⟨ψhom (φ (e : A)), ?_⟩
        apply Subtype.ext
        apply NonUnitalModuleHom.ext
        intro b
        change b • ψhom (φ (e : A)) = ψhom b
        calc
          b • ψhom (φ (e : A)) = ψhom (b * φ (e : A)) :=
            (ψhom.map_smul b (φ (e : A))).symm
          _ = ψhom b := he b
    exact ⟨(NatIso.ofComponents (fun N => isoOfBijective (u N) (hu N)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      apply NonUnitalModuleHom.ext
      intro n
      apply Subtype.ext
      apply NonUnitalModuleHom.ext
      intro b
      exact (f.hom.map_smul b n).symm)).symm⟩

/-- The full closing Remark, for the published original actions and universes. -/
theorem forgetfulFunctorRemark : ForgetfulFunctorRemarkStatement.{uA, uB, uM} := by
  intro A B _ _ hA φ hφ
  exact ⟨target_isIdempotented φ hφ, image_filtering φ hφ, fixed_iff φ hφ,
    tensorForgetfulRemark hA φ hφ, pseudoForgetfulRemark hA φ hφ⟩

/-- The unital right adjoint and both forgetful comparisons of Renard I.2.3. -/
theorem renardForgetfulFunctorStatements :
    RenardForgetfulFunctorStatements.{uA, uB, uM} :=
  ⟨unitalCoextensionAdjunction, forgetfulFunctorRemark⟩

end Langlands.Algebra.RenardForgetfulFunctor
