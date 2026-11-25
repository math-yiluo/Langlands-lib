/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.ZMod

/-! # Finite-sum presentation of constant coefficients killed by a prime

Source: the coefficient-extension step of `lem-sc-c3-degree-two`, realizing blueprint
`sec-proper-base-change/sk-thm-p1/lem-sc-c3`; the finite-subcoproduct construction is
Mathlib `CategoryTheory.Limits.CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The underlying abelian sheaf of `Λ/pΛ` is a filtered colimit of finite sums of
 the constant prime-field sheaf. This statement concerns coefficients only: it imposes
 no dimension, smoothness, compactness, or characteristic condition on the scheme.
 Source: the coefficient-extension step of `lem-sc-c3-degree-two`, realizing blueprint
 `sec-proper-base-change/sk-thm-p1/lem-sc-c3`. The construction uses Mathlib
 `Module.Basis.ofVectorSpace`, `ModuleCat.finsuppCoconeIsColimit`,
 `CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone`, and
 `CategoryTheory.constantCommuteCompose`.
 (blueprint: proposition-p-torsion-smooth-proper-curve--4).

 Proof: Put M = Λ/(p). Its additive group is killed by p, so it has the canonical
 ZMod p module structure. Restrict scalars along the ring equivalence from ULift (ZMod p)
 to ZMod p, keeping coefficients in Type (u + 1). Choose a basis B of M over this lifted
 field. The basis representation identifies M with finitely supported functions B →₀ R,
 which are the coproduct of copies of R in ModuleCat R. The coproduct is the filtered
 colimit of its finite subcoproducts, indexed by Finset (Discrete B). Apply coefficient
 forgetting followed by the constant abelian sheaf functor; both preserve these colimits.
 The constant-sheaf/forgetting comparison identifies the point with the underlying
 abelian sheaf of constantModSheaf Λ C p. Transport the mapped cocone along this point
 isomorphism. Each finite stage is a coproduct of copies of the constant prime-field
 sheaf. Identify the finite coproduct with its biproduct and reindex its finite set by
 Fin n. The zero quotient has an empty basis, whose finite-subset category has one
 object and whose finite stage is the empty biproduct. The argument also allows arbitrary
 infinite bases and schemes without any geometric hypothesis. -/
theorem exists_constantModSheaf_finite_sum_colimit
    (Λ : Type (u + 1)) [CommRing Λ] (C : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (constantModSheaf Λ C p))),
      Nonempty (IsColimit (Cocone.mk _ ι)) ∧
      ∀ i, ∃ n : ℕ, Nonempty (D.obj i ≅ ⨁ fun _ : Fin n ↦ C.constantZMod p) := by
  classical
  let M := Λ ⧸ (Ideal.span {(p : Λ)} : Ideal Λ)
  have hp : ∀ x : M, p • x = 0 := by
    intro x
    have hp0 : (p : M) = 0 := by
      exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton_self (p : Λ))
    rw [nsmul_eq_mul, hp0, zero_mul]
  let : Module (ZMod p) M := AddCommGroup.zmodModule hp
  let R := ULift.{u + 1} (ZMod p)
  let : Module R M := Module.compHom M ULift.ringEquiv.toRingHom
  let B := Module.Basis.ofVectorSpaceIndex R M
  let b : Module.Basis B R M := Module.Basis.ofVectorSpace R M
  let a : B → ModuleCat.{u + 1} R := fun _ ↦ ModuleCat.of R R
  let T : ModuleCat.{u + 1} R ⥤ Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ⋙
      constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : PreservesColimits (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} R
  have : PreservesColimits T := by
    dsimp [T, constantSheaf]
    infer_instance
  let eM : (∐ a) ≅ ModuleCat.of R M :=
    (colimit.isColimit (Discrete.functor a)).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit R R B) ≪≫ b.repr.symm.toModuleIso
  have : PreservesLimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    inferInstance
  have : PreservesFilteredColimits (forget (ModuleCat.{u + 1} Λ)) := inferInstance
  have : PreservesFilteredColimits (forget AddCommGrpCat.{u + 1}) := inferInstance
  have : C.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
    apply GrothendieckTopology.instPreservesSheafification
  let e : T.obj (∐ a) ≅
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (constantModSheaf Λ C p)) :=
    T.mapIso eM ≪≫ (constantCommuteCompose C.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).symm.app (ModuleCat.of Λ M)
  let D := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor a) ⋙ T
  let c := T.mapCocone (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone a)
  let c' := c.extend e.hom
  have hc : IsColimit c := isColimitOfPreserves T
    (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone a)
  have hc' : IsColimit c' := IsColimit.ofIsoColimit hc (Cocone.ext e)
  refine ⟨Finset (Discrete B), inferInstance, inferInstance, D, c'.ι, ⟨hc'⟩, ?_⟩
  intro s
  refine ⟨Fintype.card s, ⟨?_⟩⟩
  change T.obj (∐ fun x : s ↦ a x.val.as) ≅ _
  exact PreservesCoproduct.iso T (fun x : s ↦ a x.val.as) ≪≫
    (biproduct.isoCoproduct (fun _ : s ↦ C.constantZMod p)).symm ≪≫
    biproduct.whiskerEquiv (f := fun _ : s ↦ C.constantZMod p)
      (g := fun _ : Fin (Fintype.card s) ↦ C.constantZMod p)
      (Fintype.equivFin s) (fun _ ↦ Iso.refl _)

end AlgebraicGeometry.Etale
