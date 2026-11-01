import Langlands.Algebra.NondegenerateInductionExactnessStatements
import Langlands.Algebra.NondegenerateModuleExactnessConcrete

/-!
# Left exactness of the actual right induction functor

The original Hom lift is obtained pointwise through the injective first map.
Uniqueness of those preimages preserves additivity, the specified A-action,
and the idempotent fixing the original Hom element.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Algebra.NondegenerateILeftExactness

universe uA uB v

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule A B]

local instance : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B

variable (hAB : ActionsCommute A B B) (hB : IsIdempotented B)

/-- Postcomposition in the actual induction part preserves injectivity. -/
theorem map_injective {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N)
    (hf : Function.Injective f.hom.toAddMonoidHom) :
    Function.Injective ((RenardHomFunctors.I hAB hB).map f).hom.toAddMonoidHom := by
  intro phi psi h
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  intro b
  apply hf
  exact congrArg (fun k : ((RenardHomFunctors.I hAB hB).obj N).obj => k.val.toAddMonoidHom b) h

/-- Lift an induction kernel element through the injective first original map.
The same right idempotent fixes the pointwise lift. -/
theorem kernel_lift (S : ShortComplex (NondegenerateModuleCat.{uA, v} A))
    (hf : Function.Injective S.f.hom.toAddMonoidHom)
    (hex : ∀ y : S.X₂.obj, S.g.hom.toAddMonoidHom y = 0 → ∃ x : S.X₁.obj, S.f.hom.toAddMonoidHom x = y)
    (phi : ((RenardHomFunctors.I hAB hB).obj S.X₂).obj)
    (hphi : ((RenardHomFunctors.I hAB hB).map S.g).hom.toAddMonoidHom phi = 0) :
    ∃ psi : ((RenardHomFunctors.I hAB hB).obj S.X₁).obj,
      ((RenardHomFunctors.I hAB hB).map S.f).hom.toAddMonoidHom psi = phi := by
  classical
  let f : NonUnitalModuleHom A S.X₁.obj S.X₂.obj := S.f.hom
  let p : NonUnitalModuleHom A B S.X₂.obj := phi.val
  have hg (b : B) : S.g.hom.toAddMonoidHom (p b) = 0 :=
    congrArg (fun k : ((RenardHomFunctors.I hAB hB).obj S.X₃).obj =>
      k.val.toAddMonoidHom b) hphi
  let r (b : B) : S.X₁.obj := Classical.choose (hex (p b) (hg b))
  have hr (b : B) : f (r b) = p b :=
    Classical.choose_spec (hex (p b) (hg b))
  let lift : NonUnitalModuleHom A B S.X₁.obj :=
    { toFun := r
      map_zero' := hf (by
        change f (r 0) = f 0
        rw [hr, NonUnitalModuleHom.map_zero, NonUnitalModuleHom.map_zero])
      map_add' := fun b c => hf (by
        change f (r (b + c)) = f (r b + r c)
        rw [hr, f.map_add, hr, hr]
        exact p.map_add b c)
      map_smul' := fun a b => hf (by
        change f (r (a • b)) = f (a • r b)
        rw [hr, f.map_smul, hr]
        exact p.map_smul a b) }
  have hpart : lift ∈ RenardHomFunctors.inductionPart hAB hB S.X₁.obj := by
    obtain ⟨e, he⟩ := (RenardHomFunctors.mem_inductionPart hAB hB p).1 phi.property
    apply (RenardHomFunctors.mem_inductionPart hAB hB lift).2
    refine ⟨e, fun b => ?_⟩
    apply hf
    change f (r (b * (e : B))) = f (r b)
    rw [hr, hr]
    exact he b
  refine ⟨⟨lift, hpart⟩, ?_⟩
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  exact hr

/-- The actual right induction functor preserves every left exact sequence. -/
theorem sequenceLeftExact (hA : IsIdempotented A) :
    let := NondegenerateModuleCat.abelian.{uA, v} A hA
    let := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
    Langlands.Renard.SequenceLeftExact (RenardHomFunctors.I hAB hB) := by
  let := NondegenerateModuleCat.abelian.{uA, v} A hA
  let := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
  dsimp only
  intro S ⟨hex, hmono⟩
  have hf := (NondegenerateModuleExactnessConcrete.mono_iff hA S.f).1 hmono
  constructor
  · apply (NondegenerateModuleExactnessConcrete.exact_iff hB
      (S.map (RenardHomFunctors.I hAB hB))).2
    exact kernel_lift hAB hB S hf
      ((NondegenerateModuleExactnessConcrete.exact_iff hA S).1 hex)
  · exact (NondegenerateModuleExactnessConcrete.mono_iff hB _).2
      (map_injective hAB hB S.f hf)

end Langlands.Algebra.NondegenerateILeftExactness
