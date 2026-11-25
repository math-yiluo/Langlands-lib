/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.EtaleSingletonTensorPureImage

/-! # Pure sections in the normalized comparison range

Source: Stacks Project, Tag 03P2, affine tensor calculation.
(blueprint: new-etale-singleton-tensor-normalized-range) -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- Every normalized pure section belongs to the evaluated comparison range.
Source: Stacks Project, Tag 03P2, affine tensor calculation.
(blueprint: new-etale-singleton-tensor-normalized-range)

Proof: a generator has the form (product of projection pullbacks of b(k)) times
restriction of m. Take ULift.up (m tensor tprod(b)) in the source. The normalization
hypothesis identifies its image under f, followed by evaluation at the unique index
and ULift.down, with the given generator. Hence the generator is in the range.
This uses neither affineness nor quasi-coherence beyond that needed to state the
complex; no assertion is made that these generators span all target sections.
-/
theorem singletonTensorDegreeComparisonHom_normalized_range
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f) :
    let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
    let N := Γ((Modules.tensorPullback P.left.hom).obj F, ⊤)
    let D : (Fin (n + 1) → Fin 1) → AddCommGrpCat.{u + 1} :=
      fun _ ↦ AddCommGrpCat.of (ULift.{u + 1} N)
    let q : (singletonTensorCech X F U W g).X n →+ N :=
      (AddEquiv.ulift : ULift.{u + 1} N ≃+ N).toAddMonoidHom.comp
        (Pi.π D (fun _ ↦ 0)).hom
    Set.range (fun p : Γ((Modules.tensorPullback U.hom).obj F, ⊤) ×
      (Fin (n + 1) → Γ(W.left, ⊤)) ↦
        (∏ k : Fin (n + 1),
          (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop (p.2 k)) •
            Modules.etaleTensorSectionsRestriction F P.hom p.1) ⊆
      (q.comp f.hom).range := by
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  exact fun y ⟨p, hp⟩ ↦
    ⟨_, (singletonTensorDegreeComparisonHom_pure_image.{u}
      X F U W g n f hf p.1 p.2).trans hp⟩

end
end AlgebraicGeometry.Scheme
