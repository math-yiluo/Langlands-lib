import Langlands.Geometry.Analytic.EtaleCoverGluing
import Langlands.Geometry.Analytic.EtaleHomSheafStatement
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Comparison of surjective étale maps with a common kernel pair -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P R X Y : LocalizedCategory.{u, v, v} (K := K)} {r s : R ⟶ P}

private theorem exists_desc_of_kernelPair (hSheaf : EtaleHomSheafStatement.{u, v})
    (p : P ⟶ X) (hp : etale p) (hps : Function.Surjective (localizedSpaceFunctor.map p))
    (h : IsPullback r s p p) (a : P ⟶ Y) (ha : r ≫ a = s ≫ a) :
    ∃ d : X ⟶ Y, p ≫ d = a := by
  obtain ⟨d, hd⟩ := exists_glue_of_etale_cover (hSheaf K X Y)
    (fun _ : Unit => P) (fun _ => p) (fun _ => hp) (fun x => ⟨(), hps x⟩)
    (fun _ => a) (fun T _ _ b c hbc => by
      let l : T ⟶ R := h.lift b c hbc
      calc
        b ≫ a = (l ≫ r) ≫ a := congrArg (· ≫ a) (h.lift_fst b c hbc).symm
        _ = (l ≫ s) ≫ a := by rw [Category.assoc, Category.assoc, ha]
        _ = c ≫ a := congrArg (· ≫ a) (h.lift_snd b c hbc))
  exact ⟨d, hd ()⟩

/-- Given étale Hom descent, two surjective étale morphisms with a common
kernel pair have isomorphic targets, compatibly with the morphisms. -/
def etaleQuotientIsoOfCommonKernelPair (hSheaf : EtaleHomSheafStatement.{u, v})
    (p : P ⟶ X) (q : P ⟶ Y) (hp : etale p) (hq : etale q)
    (hps : Function.Surjective (localizedSpaceFunctor.map p))
    (hqs : Function.Surjective (localizedSpaceFunctor.map q))
    (hX : IsPullback r s p p) (hY : IsPullback r s q q) :
    {e : X ≅ Y // p ≫ e.hom = q} := by
  let hpq := exists_desc_of_kernelPair hSheaf p hp hps hX q hY.w
  let hqp := exists_desc_of_kernelPair hSheaf q hq hqs hY p hX.w
  let f := Classical.choose hpq
  let g := Classical.choose hqp
  have hf : p ≫ f = q := Classical.choose_spec hpq
  have hg : q ≫ g = p := Classical.choose_spec hqp
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply hom_ext_of_etale_cover (hSheaf K X X) (fun _ : Unit => P) (fun _ => p)
      (fun _ => hp) (fun x => ⟨(), hps x⟩)
    intro j
    rw [← Category.assoc, hf, hg, Category.comp_id]
  · apply hom_ext_of_etale_cover (hSheaf K Y Y) (fun _ : Unit => P) (fun _ => q)
      (fun _ => hq) (fun y => ⟨(), hqs y⟩)
    intro j
    rw [← Category.assoc, hg, hf, Category.comp_id]

end Langlands.Analytic.SaturatedAtlasPresentation
