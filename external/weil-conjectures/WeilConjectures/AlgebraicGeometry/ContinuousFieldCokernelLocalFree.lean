/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix

import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm

/-!
# Local freeness of cokernels of continuous matrices of locally constant rank

Source: Hemo--Richarz--Scholbach, Example 3.1, and the Gaussian elimination step
of the accompanying rank/descent argument.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A finite presentation matrix of locally constant pointwise rank has locally free
cokernel over continuous field-valued coefficients, with no noetherian hypothesis.
Source: the rank/descent argument, steps 6--7, accompanying Hemo--Richarz--Scholbach,
Example 3.1 (auxiliary; not a blueprint node).
Proof: the fibres of the rank function form an open cover. On a rank-r fibre,
nonvanishing r by r minors cover; this includes the empty minor when r is zero.
On each such open the chosen minor is invertible as a continuous matrix: its inverse
is its adjugate divided by its nowhere-zero determinant. Permute rows and columns,
then perform the two invertible block operations. The Schur complement vanishes at
every point by the pointwise rank bound, so its entries are zero continuous functions.
The matrix is equivalent to a block identity and zero. Identify regular-module
endomorphisms with global continuous functions by their value on one, and finite-free
maps with matrices by biproduct inclusions and projections. These identifications
respect restriction and composition. Thus the invertible matrix operations give
isomorphisms of module sheaves, and the cokernel is the remaining finite biproduct of
regular modules. Inverse image preserves cokernels and finite biproducts; transport
through the given ring-object isomorphism and compose the open covers. -/
theorem exists_finiteFree_cover_cokernel_of_locallyConstant_rank
    (E : Type u) [NormedField E] (V : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) [MonObj R]
    (e : R ⟶ (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E)) [IsIso e] [IsMonHom e]
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n)
    (hr : IsLocallyConstant (fun v : V ↦
      ((continuousFieldPresentationMatrix E V e f).map (fun a ↦ a v)).rank)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage V, ∀ i : C.I₀,
      Mod.IsFree ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj R)
        (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod R).obj (cokernel f)) := by
  obtain ⟨C, hC⟩ := exists_cover_continuousField_presentation_normalForm E V R e f hr
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨r, s, t, a, b, h⟩ := hC i
  let F := (upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod R
  let T := (upperStar AddCommGrpCat.{u + 1} (C.f i)).obj R
  let k : Mod.finiteFree T r ⊞ Mod.finiteFree T s ⟶
      Mod.finiteFree T r ⊞ Mod.finiteFree T t := biprod.map (𝟙 _) 0
  have hk : k = biprod.fst ≫ biprod.inl := by
    apply biprod.hom_ext <;> simp [k]
  refine ⟨t, ⟨PreservesCokernel.iso F f ≪≫ cokernel.mapIso (F.map f) k a b ?_ ≪≫
    cokernelIsoOfEq hk ≪≫ cokernelEpiComp _ _ ≪≫ cokernelBiprodInlIso⟩⟩
  change F.map f ≫ b.hom = a.hom ≫ k
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale
