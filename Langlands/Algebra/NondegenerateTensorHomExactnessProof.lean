import Langlands.Algebra.NondegenerateTensorHomExactnessStatements
import Langlands.Algebra.NondegenerateModuleExactnessConcrete
import Langlands.CategoryTheory.Renard.HomExactnessComparison

/-!
# Exactness of the nondegenerate tensor and Hom functors

The tensor proof descends balanced biadditive maps through a surjection, proving
the cokernel universal property directly. The Hom clauses specialize the
published general Hom left-exactness theorems.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NondegenerateTensorHomExactness

universe uA uX uY uM

open NonUnitalModuleTensor (Tensor tmul)

section Tensor

variable {A : Type uA} [NonUnitalRing A]
  {X : Type uX} [AddCommGroup X] [NonUnitalModule A X]

private def descendedBiadditive
    (S : ShortComplex (NondegenerateModuleCat.{uA, uY} Aᵐᵒᵖ))
    (hex : ∀ y : S.X₂.obj, S.g.hom.toAddMonoidHom y = 0 →
      ∃ x : S.X₁.obj, S.f.hom.toAddMonoidHom x = y)
    (hgs : Function.Surjective S.g.hom.toAddMonoidHom)
    {N : ModuleCat.{max uY uX} ℤ}
    (φ : (tensorFunctor A X).obj S.X₂ ⟶ N)
    (hφ : (tensorFunctor A X).map S.f ≫ φ = 0) :
    NonUnitalModuleTensor.balancedMaps A (X := S.X₃.obj) (Y := X) (Z := N) := by
  let b := NonUnitalModuleTensor.restrict A φ.hom.toAddMonoidHom
  have hk : S.g.hom.toAddMonoidHom.ker ≤ b.val.ker := by
    intro y hy
    obtain ⟨l, rfl⟩ := hex y hy
    apply AddMonoidHom.ext
    intro x
    exact congrArg (fun k : (tensorFunctor A X).obj S.X₁ ⟶ N =>
      k.hom (tmul A S.X₁.obj X l x)) hφ
  let d := S.g.hom.toAddMonoidHom.liftOfSurjective hgs ⟨b.val, hk⟩
  have hd (y : S.X₂.obj) : d (S.g.hom.toAddMonoidHom y) = b.val y :=
    AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨d, ?_⟩
  intro a z x
  obtain ⟨y, rfl⟩ := hgs z
  rw [← S.g.hom.map_smul, hd, hd]
  exact b.property a y x

private theorem descendedBiadditive_g
    (S : ShortComplex (NondegenerateModuleCat.{uA, uY} Aᵐᵒᵖ))
    (hex : ∀ y : S.X₂.obj, S.g.hom.toAddMonoidHom y = 0 →
      ∃ x : S.X₁.obj, S.f.hom.toAddMonoidHom x = y)
    (hgs : Function.Surjective S.g.hom.toAddMonoidHom)
    {N : ModuleCat.{max uY uX} ℤ}
    (φ : (tensorFunctor A X).obj S.X₂ ⟶ N)
    (hφ : (tensorFunctor A X).map S.f ≫ φ = 0) (y : S.X₂.obj) (x : X) :
    (descendedBiadditive S hex hgs φ hφ).val (S.g.hom.toAddMonoidHom y) x =
      φ.hom (tmul A S.X₂.obj X y x) := by
  exact congrArg (fun b : X →+ N => b x)
    (AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _)

private def descendedTensor
    (S : ShortComplex (NondegenerateModuleCat.{uA, uY} Aᵐᵒᵖ))
    (hex : ∀ y : S.X₂.obj, S.g.hom.toAddMonoidHom y = 0 →
      ∃ x : S.X₁.obj, S.f.hom.toAddMonoidHom x = y)
    (hgs : Function.Surjective S.g.hom.toAddMonoidHom)
    {N : ModuleCat.{max uY uX} ℤ}
    (φ : (tensorFunctor A X).obj S.X₂ ⟶ N)
    (hφ : (tensorFunctor A X).map S.f ≫ φ = 0) :
    (tensorFunctor A X).obj S.X₃ ⟶ N := by
  let d := NonUnitalModuleTensor.lift A
    (descendedBiadditive S hex hgs φ hφ).val
    (descendedBiadditive S hex hgs φ hφ).property
  exact ModuleCat.ofHom {
    toFun := d
    map_add' := d.map_add
    map_smul' n t := by simpa using map_intCast_smul d ℤ ℤ n t }

private theorem map_g_descendedTensor
    (S : ShortComplex (NondegenerateModuleCat.{uA, uY} Aᵐᵒᵖ))
    (hex : ∀ y : S.X₂.obj, S.g.hom.toAddMonoidHom y = 0 →
      ∃ x : S.X₁.obj, S.f.hom.toAddMonoidHom x = y)
    (hgs : Function.Surjective S.g.hom.toAddMonoidHom)
    {N : ModuleCat.{max uY uX} ℤ}
    (φ : (tensorFunctor A X).obj S.X₂ ⟶ N)
    (hφ : (tensorFunctor A X).map S.f ≫ φ = 0) :
    (tensorFunctor A X).map S.g ≫ descendedTensor S hex hgs φ hφ = φ := by
  have he := NonUnitalModuleTensor.hom_ext A
    (f := ((tensorFunctor A X).map S.g ≫
      descendedTensor S hex hgs φ hφ).hom.toAddMonoidHom)
    (g := φ.hom.toAddMonoidHom)
    (fun y x => descendedBiadditive_g S hex hgs φ hφ y x)
  ext t
  exact DFunLike.congr_fun he t

private theorem map_g_cancel
    (S : ShortComplex (NondegenerateModuleCat.{uA, uY} Aᵐᵒᵖ))
    (hgs : Function.Surjective S.g.hom.toAddMonoidHom)
    {N : ModuleCat.{max uY uX} ℤ}
    (l k : (tensorFunctor A X).obj S.X₃ ⟶ N)
    (hlk : (tensorFunctor A X).map S.g ≫ l = (tensorFunctor A X).map S.g ≫ k) :
    l = k := by
  have he := NonUnitalModuleTensor.hom_ext A
    (f := l.hom.toAddMonoidHom) (g := k.hom.toAddMonoidHom) (fun z x => by
      obtain ⟨y, rfl⟩ := hgs z
      exact congrArg (fun r : (tensorFunctor A X).obj S.X₂ ⟶ N =>
        r.hom (tmul A S.X₂.obj X y x)) hlk)
  ext t
  exact DFunLike.congr_fun he t

/-- The balanced tensor preserves an exact sequence with epimorphic right boundary. -/
theorem tensorRightExact : TensorRightExactStatement.{uA, uX, uY} := by
  intro A _ hA X _ _ _hX
  let := NondegenerateModuleCat.abelian.{uA, uY} Aᵐᵒᵖ hA.op
  intro S hS
  have hgs := (NondegenerateModuleExactnessConcrete.epi_iff hA.op S.g).1 hS.2
  have hex := (NondegenerateModuleExactnessConcrete.exact_iff hA.op S).1 hS.1
  apply ((S.map (tensorFunctor A X)).exact_and_epi_g_iff_g_is_cokernel).2
  refine ⟨CokernelCofork.IsColimit.ofπ ((tensorFunctor A X).map S.g)
    (S.map (tensorFunctor A X)).zero
    (fun {N} φ hφ => descendedTensor S hex hgs φ hφ)
    (fun {N} φ hφ => map_g_descendedTensor S hex hgs φ hφ) ?_⟩
  intro N φ hφ l hl
  apply map_g_cancel S hgs l (descendedTensor S hex hgs φ hφ)
  exact hl.trans (map_g_descendedTensor S hex hgs φ hφ).symm

end Tensor

/-- Renard I.2.2 Proposition, with all four published universes independent. -/
theorem statements : Statements.{uA, uX, uY, uM} := by
  refine ⟨tensorRightExact, ?_, ?_⟩
  · intro A _ hA X
    let := NondegenerateModuleCat.abelian.{uA, uM} A hA
    exact Langlands.Renard.contravariantHomLeftExact X
  · intro A _ hA X
    let := NondegenerateModuleCat.abelian.{uA, uM} A hA
    exact Langlands.Renard.covariantHomLeftExact X

end Langlands.Algebra.NondegenerateTensorHomExactness
