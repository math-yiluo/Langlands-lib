import Langlands.AbelianScheme.RationalBaseChangeFaithfulness
import Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctionsProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # Rigidity of abelian-scheme homomorphisms under surjective base change -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme

variable {S T : Scheme.{u}} (b : T ⟶ S) [Surjective b] {A B : AbelianScheme S}

private theorem baseChange_map_eq_zero (f : A ⟶ B) (hf : (baseChange b).map f = 0) :
    f = 0 := by
  have he : η[A.X].left ≫ hom f = η[B.X].left :=
    congrArg (fun g => g.left) (IsMonHom.one_hom (groupHom f).hom.hom)
  have hp : ∀ x : A.X.left, hom f x = hom (0 : A ⟶ B) x := by
    intro x
    obtain ⟨x', hx'⟩ := (pullback.fst A.X.hom b).surjective x
    have hf' := hf.trans ((baseChange b).map_zero A B).symm
    have hh := congrArg
      (fun g => hom g ≫ pullback.fst B.X.hom b) hf'
    change ((Over.pullback b).map (groupHom f).hom.hom).left ≫ pullback.fst B.X.hom b =
      ((Over.pullback b).map (groupHom (0 : A ⟶ B)).hom.hom).left ≫
        pullback.fst B.X.hom b at hh
    simp only [Over.pullback_map_left, pullback.lift_fst] at hh
    have hpt := congrArg (fun g : pullback A.X.hom b ⟶ B.X.left => g x') hh
    simpa only [Scheme.Hom.comp_apply, hx'] using hpt
  have hconst : hom f = A.X.hom ≫ η[A.X].left ≫ hom f :=
    Langlands.AlgebraicGeometry.factorizationOfGlobalFunctions
      A.X.left S B.X.left A.X.hom η[A.X].left (hom f)
      η[A.X].w
      (Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions A.X.left S A.X.hom
        A.smooth A.proper A.geometricallyConnected) (fun x => by
        rw [he]
        exact hp x)
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change hom f = A.X.hom ≫ η[B.X].left
  simpa only [he] using hconst

/-- Base change along a surjection on points is faithful on abelian-scheme
homomorphisms. -/
theorem baseChange_map_injective_of_surjective :
    Function.Injective (fun f : A ⟶ B => (baseChange b).map f) := by
  intro f g h
  change (baseChange b).map f = (baseChange b).map g at h
  apply sub_eq_zero.mp
  apply baseChange_map_eq_zero b
  rw [Functor.map_sub, h, sub_self]

/-- Tensoring the integral rigidity map with ℚ gives rigidity of rational
homomorphisms under the same surjective base change. -/
theorem rationalBaseChangeIsFaithful_of_surjective : RationalBaseChangeIsFaithful b := by
  intro U V
  let F := (baseChange b).mapLinearMap (R := ℤ) (X := U) (Y := V)
  have hF : Function.Injective F := baseChange_map_injective_of_surjective b
  have hQ : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have hmap : ∀ f : Hom0 U V, rationalBaseChangeHom b f = F.lTensor ℚ f := by
    intro f
    induction f using TensorProduct.inductionOn with
    | tmul q f => rw [rationalBaseChangeHom_tmul, LinearMap.lTensor_tmul]; rfl
    | add f g hf hg => rw [map_add, map_add, hf, hg]
  intro f g h
  apply Module.Flat.lTensor_preserves_injective_linearMap F hF
  rw [← hmap f, ← hmap g, h]

end Langlands.AbelianScheme
