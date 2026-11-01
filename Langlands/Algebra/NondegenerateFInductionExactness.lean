import Langlands.Algebra.NondegenerateInductionExactnessStatements
import Langlands.Algebra.RegularTensorContraction
import Langlands.Algebra.NondegenerateModuleExactnessConcrete
import Langlands.Algebra.NondegenerateILeftExactness

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Algebra

universe uA uB v

namespace NondegenerateFInductionExactness

open NondegenerateModuleExactnessConcrete


section Tensor

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule A B]

local instance : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B

variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hAB : ActionsCommute A B B) (hnd : IsNondegenerateBimodule A B B)

private theorem contraction_surjective (N : NondegenerateModuleCat.{uB, v} B) :
    Function.Surjective (RegularTensorContraction.contraction B N.obj) := by
  intro n
  obtain ⟨e, he⟩ := N.property n
  exact ⟨RegularTensorContraction.pure B N.obj (e : B) n, he⟩

private theorem contraction_map {M N : NondegenerateModuleCat.{uB, v} B}
    (f : M ⟶ N) (t : ((NondegenerateTensorFunctor.F hA hAB hnd).obj M).obj) :
    RegularTensorContraction.contraction B N.obj
        (((NondegenerateTensorFunctor.F hA hAB hnd).map f).hom.toAddMonoidHom t) =
      f.hom.toAddMonoidHom (RegularTensorContraction.contraction B M.obj t) :=
  DFunLike.congr_fun (RegularTensorContraction.contraction_naturality B f.hom) t

include hB

/-- Every exact triple is preserved by the actual tensor F. -/
theorem F_map_exact (S : ShortComplex (NondegenerateModuleCat.{uB, v} B)) :
    let := NondegenerateModuleCat.abelian.{uB, v} B hB
    let := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
    S.Exact → (S.map (NondegenerateTensorFunctor.F hA hAB hnd)).Exact := by
  dsimp only
  let := NondegenerateModuleCat.abelian.{uB, v} B hB
  let := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
  intro hS
  apply (exact_iff hA _).2
  intro y hy
  have hk : S.g.hom.toAddMonoidHom
      (RegularTensorContraction.contraction B S.X₂.obj y) = 0 := by
    exact (contraction_map hA hAB hnd S.g y).symm.trans
      ((congrArg (RegularTensorContraction.contraction B S.X₃.obj) hy).trans (map_zero _))
  obtain ⟨x, hx⟩ := (exact_iff hB S).1 hS _ hk
  obtain ⟨t, ht⟩ := contraction_surjective S.X₁ x
  refine ⟨t, RegularTensorContraction.contraction_injective B S.X₂.obj hB ?_⟩
  exact (contraction_map hA hAB hnd S.f t).trans
    ((congrArg S.f.hom.toAddMonoidHom ht).trans hx)

/-- The actual F preserves the required boundary monomorphism. -/
theorem F_map_mono {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N) :
    let := NondegenerateModuleCat.abelian.{uB, v} B hB
    let := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
    Mono f → Mono ((NondegenerateTensorFunctor.F hA hAB hnd).map f) := by
  dsimp only
  let := NondegenerateModuleCat.abelian.{uB, v} B hB
  let := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
  intro hf
  apply (mono_iff hA _).2
  intro x y hxy
  apply RegularTensorContraction.contraction_injective B M.obj hB
  apply (mono_iff hB f).1 hf
  rw [← contraction_map hA hAB hnd f x, ← contraction_map hA hAB hnd f y, hxy]

/-- The actual F preserves the required boundary epimorphism. -/
theorem F_map_epi {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N) :
    let := NondegenerateModuleCat.abelian.{uB, v} B hB
    let := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
    Epi f → Epi ((NondegenerateTensorFunctor.F hA hAB hnd).map f) := by
  dsimp only
  let := NondegenerateModuleCat.abelian.{uB, v} B hB
  let := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
  intro hf
  apply (epi_iff hA _).2
  intro y
  obtain ⟨x, hx⟩ := (epi_iff hB f).1 hf
    (RegularTensorContraction.contraction B N.obj y)
  obtain ⟨t, ht⟩ := contraction_surjective M x
  refine ⟨t, RegularTensorContraction.contraction_injective B N.obj hB ?_⟩
  exact (contraction_map hA hAB hnd f t).trans
    ((congrArg f.hom.toAddMonoidHom ht).trans hx)

/-- Both full one-sided sequence tests for F. -/
theorem F_sequenceExact :
    let := NondegenerateModuleCat.abelian.{uB, v} B hB
    let := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
    Langlands.Renard.SequenceExact (NondegenerateTensorFunctor.F hA hAB hnd) := by
  dsimp only
  let := NondegenerateModuleCat.abelian.{uB, v} B hB
  let := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
  constructor
  · intro S ⟨hS, hf⟩
    exact ⟨F_map_exact hA hB hAB hnd S hS, F_map_mono hA hB hAB hnd S.f hf⟩
  · intro S ⟨hS, hg⟩
    exact ⟨F_map_exact hA hB hAB hnd S hS, F_map_epi hA hB hAB hnd S.g hg⟩

end Tensor

end NondegenerateFInductionExactness

/-- Renard I.2.4 for the actual F and I at independent ring and carrier universes. -/
theorem nondegenerateFInductionExactness :
    NondegenerateFInductionExactnessTheorem.{uA, uB, v} := by
  intro A B _ _ hA hB _ hAB hnd
  exact ⟨NondegenerateFInductionExactness.F_sequenceExact hA hB hAB hnd,
    NondegenerateILeftExactness.sequenceLeftExact hAB hB hA⟩

example : NondegenerateFInductionExactnessTheorem.{0, 1, 0} :=
  nondegenerateFInductionExactness

example : NondegenerateFInductionExactnessTheorem.{1, 0, 2} :=
  nondegenerateFInductionExactness

end Langlands.Algebra
