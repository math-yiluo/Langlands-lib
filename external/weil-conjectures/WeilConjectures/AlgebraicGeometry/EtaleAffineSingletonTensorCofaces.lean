/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeComparison
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorPureCofaces

/-! # Cofaces of the affine singleton tensor comparison
Source: Stacks Project, Tag 03P2, the tensor differential formula.
(blueprint: new-etale-affine-singleton-tensor-cofaces).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The pure-tensor normalized degree comparisons commute with each coface.
Source: Stacks Project, Tag 03P2, affine proof: omission of one projection inserts
one into the corresponding tensor factor; Tag 03DR for restriction functoriality.
(blueprint: new-etale-affine-singleton-tensor-cofaces)

Proof: evaluate the categorical product at its sole index. Test the two composites
on a tensor m tensor tprod(b). Such tensors additively generate, by ordinary tensor
induction and indexed tensor induction. The Amitsur coface inserts one in position j.
By the normalization equation its image is the product of the other pulled-back
b(k), multiplied by the coefficient section pulled back from U. On the Čech side,
the coface is restriction along the product projection omitting j. Restriction is
additive and semilinear over the pullback of functions. Its composition law identifies
the restricted coefficient section with the direct restriction from U. The universal
property of the product identifies the composites of the retained projections with
their original projections. Thus the products of functions agree; the omitted factor
is one. Equality on generators gives the equation. No affineness is needed here:
it was used only to produce the normalized degree comparisons. -/
theorem singletonTensorDegreeComparison_coface
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U)
    (e : ∀ n : ℕ, (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n)
    (he : ∀ n, IsSingletonTensorDegreeComparison X F U W g n (e n)) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    ∀ (n : ℕ) (j : Fin (n + 2)),
      (e n).hom ≫ (singletonTensorCechCosimplicial X F U W g).δ j =
        (singletonTensorForget U.left).map
          ((Algebra.TensorProduct.amitsurCosimplicialObject Γ(U.left, ⊤) Γ(W.left, ⊤)
            Γ((Modules.tensorPullback U.hom).obj F, ⊤)).δ j) ≫ (e (n + 1)).hom := by
  classical
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  intro n j
  apply AddCommGrpCat.ext
  intro x
  obtain ⟨x⟩ := x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    change (_ : _ →+ _) (ULift.up x + ULift.up y) =
      (_ : _ →+ _) (ULift.up x + ULift.up y)
    simp only [map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul m b =>
    induction b using PiTensorProduct.induction_on generalizing m with
    | add b c hb hc =>
      simp only [TensorProduct.tmul_add]
      change (_ : _ →+ _) (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] b) +
        ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] c)) = (_ : _ →+ _)
          (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] b) + ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] c))
      simp only [map_add]
      exact congrArg₂ (· + ·) (hb m) (hc m)
    | smul_tprod r b =>
      simp only [← TensorProduct.smul_tmul]
      exact singletonTensorDegreeComparison_pure_coface_fixed X F U W g e he n j (r • m) b

end
end AlgebraicGeometry.Scheme
