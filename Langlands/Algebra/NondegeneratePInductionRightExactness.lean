import Langlands.Algebra.NondegenerateInductionExactnessStatements
import Langlands.Algebra.NondegenerateModuleExactnessProof
import Langlands.Algebra.NonUnitalModuleExactnessProof
import Langlands.Algebra.NonUnitalTensorHomAdjunctionProof

/-! # Right exactness of the actual regular-carrier induction P -/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NondegeneratePInductionRightExactness
open NonUnitalModuleTensor (tmul)

universe uA uB v

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]

attribute [local instance] NonUnitalModule.regular

variable [NonUnitalModule Aᵐᵒᵖ B]
  (hB : IsIdempotented B)
  (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
  (hnd : @IsNondegenerateBimodule B A B _ _ _ (NonUnitalModule.regular B) _)

local notation "PF" =>
  NondegenerateTensorFunctor.P (A := A) (B := B) hB hBA hnd

private theorem original_surjective (hA : IsIdempotented A)
    {M N : NondegenerateModuleCat.{uA, v} A} (g : M ⟶ N) [Epi g] :
    Function.Surjective g.hom.toAddMonoidHom := by
  let := NondegenerateModuleCat.abelian.{uA, v} A hA
  let := Functor.preservesEpimorphisms_of_map_exact (nondegenerateInclusion A)
    (nondegenerateInclusion_map_exact hA)
  have : Epi g.hom := inferInstanceAs (Epi ((nondegenerateInclusion A).map g))
  have : Epi ((IntegerUnitization.equivalence A).functor.map g.hom) := inferInstance
  exact (ModuleCat.epi_iff_surjective
    ((IntegerUnitization.equivalence A).functor.map g.hom)).1 inferInstance

section Descent

/-- Descend the curried map along the actual surjection, at its original universe. -/
private def descendedCurry (S : ShortComplex (NondegenerateModuleCat.{uA, v} A))
  (hex : S.f.hom.rangeSubmodule = S.g.hom.kernelSubmodule)
  (hgs : Function.Surjective S.g.hom.toAddMonoidHom)
  {N : NondegenerateModuleCat.{uB, max uB v} B}
  (φ : (PF).obj S.X₂ ⟶ N) (hφ : (PF).map S.f ≫ φ = 0) :
    NonUnitalTensorHomAdjunction.Left.CurriedHom A B S.X₃.obj B N.obj hBA := by
  letI := NonUnitalBimoduleHomActions.sourceAction (Z := N.obj) hBA
  let c := NonUnitalTensorHomAdjunction.Left.curry A B S.X₂.obj B N.obj hBA φ.hom
  have hk : S.g.hom.toAddMonoidHom.ker ≤ c.toAddMonoidHom.ker := by
    intro m hm
    have hm' : m ∈ S.f.hom.rangeSubmodule := hex.symm ▸ hm
    obtain ⟨l, rfl⟩ := hm'
    change c (S.f.hom.toAddMonoidHom l) = 0
    apply NonUnitalModuleHom.ext
    intro b
    exact congrArg (fun k : (PF).obj S.X₁ ⟶ N => k.hom.toAddMonoidHom (tmul A B S.X₁.obj b l)) hφ
  let d := S.g.hom.toAddMonoidHom.liftOfSurjective hgs ⟨c.toAddMonoidHom, hk⟩
  have hd (m : S.X₂.obj) : d (S.g.hom.toAddMonoidHom m) = c m := by
    exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  exact {
    toAddMonoidHom := d
    map_smul' a n := by
      obtain ⟨m, rfl⟩ := hgs n
      rw [← S.g.hom.map_smul, hd, hd, c.map_smul] }

private theorem descendedCurry_g (S : ShortComplex (NondegenerateModuleCat.{uA, v} A))
  (hex : S.f.hom.rangeSubmodule = S.g.hom.kernelSubmodule)
  (hgs : Function.Surjective S.g.hom.toAddMonoidHom)
  {N : NondegenerateModuleCat.{uB, max uB v} B}
  (φ : (PF).obj S.X₂ ⟶ N) (hφ : (PF).map S.f ≫ φ = 0) (m : S.X₂.obj) :
    descendedCurry hB hBA hnd S hex hgs φ hφ (S.g.hom.toAddMonoidHom m) =
      NonUnitalTensorHomAdjunction.Left.curry A B S.X₂.obj B N.obj hBA φ.hom m := by
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- Uncurry the original descended map into the given actual nondegenerate object. -/
private def descendedTensor (S : ShortComplex (NondegenerateModuleCat.{uA, v} A))
  (hex : S.f.hom.rangeSubmodule = S.g.hom.kernelSubmodule)
  (hgs : Function.Surjective S.g.hom.toAddMonoidHom)
  {N : NondegenerateModuleCat.{uB, max uB v} B}
  (φ : (PF).obj S.X₂ ⟶ N) (hφ : (PF).map S.f ≫ φ = 0) : (PF).obj S.X₃ ⟶ N :=
  ObjectProperty.homMk
    (NonUnitalTensorHomAdjunction.Left.uncurry A B S.X₃.obj B N.obj hBA
      (descendedCurry hB hBA hnd S hex hgs φ hφ))

private theorem map_g_descendedTensor (S : ShortComplex (NondegenerateModuleCat.{uA, v} A))
  (hex : S.f.hom.rangeSubmodule = S.g.hom.kernelSubmodule)
  (hgs : Function.Surjective S.g.hom.toAddMonoidHom)
  {N : NondegenerateModuleCat.{uB, max uB v} B}
  (φ : (PF).obj S.X₂ ⟶ N) (hφ : (PF).map S.f ≫ φ = 0) :
    (PF).map S.g ≫ descendedTensor hB hBA hnd S hex hgs φ hφ = φ := by
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro t
  have he := NonUnitalModuleTensor.hom_ext A
    (f := ((PF).map S.g ≫ descendedTensor hB hBA hnd S hex hgs φ hφ).hom.toAddMonoidHom)
    (g := φ.hom.toAddMonoidHom) (fun b m =>
      congrArg (fun k : NonUnitalModuleHom B B N.obj => k b)
        (descendedCurry_g hB hBA hnd S hex hgs φ hφ m))
  exact DFunLike.congr_fun he t

private theorem map_g_cancel
    (S : ShortComplex (NondegenerateModuleCat.{uA, v} A))
    (hgs : Function.Surjective S.g.hom.toAddMonoidHom)
    {N : NondegenerateModuleCat.{uB, max uB v} B}
    (l k : (PF).obj S.X₃ ⟶ N) (hlk : (PF).map S.g ≫ l = (PF).map S.g ≫ k) : l = k := by
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro t
  have he := NonUnitalModuleTensor.hom_ext A
    (f := l.hom.toAddMonoidHom) (g := k.hom.toAddMonoidHom) (fun b n => by
      obtain ⟨m, rfl⟩ := hgs n
      exact congrArg (fun r : (PF).obj S.X₂ ⟶ N => r.hom.toAddMonoidHom (tmul A B S.X₂.obj b m)) hlk)
  exact DFunLike.congr_fun he t

end Descent

/-- P preserves every exact short complex with an epimorphic right boundary,
including that boundary, for independent ring and source carrier universes. -/
theorem sequenceRightExact (hA : IsIdempotented A) :
    let := NondegenerateModuleCat.abelian.{uA, v} A hA
    let := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
    Langlands.Renard.SequenceRightExact PF := by
  dsimp only
  let := NondegenerateModuleCat.abelian.{uA, v} A hA
  let := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
  intro S hS
  have := hS.2
  have hgs := original_surjective hA S.g
  have hex : S.f.hom.rangeSubmodule = S.g.hom.kernelSubmodule :=
    (NonUnitalModuleCat.exact_iff_rangeSubmodule_eq_kernelSubmodule
      (S.map (nondegenerateInclusion A))).1 (nondegenerateInclusion_map_exact hA S hS.1)
  apply ((S.map PF).exact_and_epi_g_iff_g_is_cokernel).2
  refine ⟨CokernelCofork.IsColimit.ofπ ((PF).map S.g) (S.map PF).zero
    (fun {N} φ hφ => descendedTensor hB hBA hnd S hex hgs φ hφ)
    (fun {N} φ hφ => map_g_descendedTensor hB hBA hnd S hex hgs φ hφ) ?_⟩
  intro N φ hφ l hl
  apply map_g_cancel hB hBA hnd S hgs l (descendedTensor hB hBA hnd S hex hgs φ hφ)
  exact hl.trans (map_g_descendedTensor hB hBA hnd S hex hgs φ hφ).symm

end Langlands.Algebra.NondegeneratePInductionRightExactness
