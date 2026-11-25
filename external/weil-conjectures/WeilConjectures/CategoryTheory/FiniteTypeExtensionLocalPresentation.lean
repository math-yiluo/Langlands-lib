/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import WeilConjectures.CategoryTheory.LocalModuleIso

/-!
# Local constant presentations of extensions

Source: Stacks Project, Modules on Sites, Tag 093U (3), extension paragraph.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

attribute [local instance] Abelian.hasFiniteBiproducts
  preservesBinaryBiproducts_of_preservesBinaryProducts

namespace SheafOfModules
set_option linter.style.haveILetI false
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {B : Type u} [CommRing B]

/-- Locally split finite-free presentations give constant finite-module presentations
of the middle term of an extension.
Source: Stacks Project, Modules on Sites, Tag 093U (3).
(auxiliary; not a blueprint node).

Proof: Choose a finite free surjection onto the constant quotient module. Its kernel is
finite by Noetherianity. Constant-module exactness and exact restriction give the
corresponding short exact sequence on every slice. Lift the finite-free morphism through
the extension epi on a covering sieve. The kernel property produces a map from the
constant relation module to the constant submodule. The cokernel-presentation lemma
expresses the middle term as the cokernel of the map with components minus this map and
the original relation inclusion. Preservation of binary biproducts identifies its target
with the constant of the finite direct sum. No local linearity of this relation map is
asserted here. -/
theorem exists_cover_constant_presentation [IsNoetherianRing B]
    (S : ShortComplex (ringedSiteModules.{u}
      ((constantSheaf J RingCat.{u}).obj (RingCat.of B))))
    (hS : S.ShortExact) (U : C) (M N : ModuleCat.{u} B)
    (hM : Module.Finite B M) (hN : Module.Finite B N)
    (eM : S.X₁.over U ≅ ((strictPerfectConstantSheaf J B).obj M).over U)
    (eN : S.X₃.over U ≅ ((strictPerfectConstantSheaf J B).obj N).over U) :
    ∃ T ∈ J U, ∀ (V : C) (f : V ⟶ U), T f →
      ∃ K Q : ModuleCat.{u} B, Module.Finite B K ∧ Module.Finite B Q ∧
        ∃ a : ((strictPerfectConstantSheaf J B).obj K).over V ⟶
          ((strictPerfectConstantSheaf J B).obj Q).over V,
          Nonempty (S.X₂.over V ≅ cokernel a) := by
  letI : PreservesFiniteLimits (strictPerfectConstantSheaf J B) :=
    (strictPerfectConstantSheaf_exact J B).1
  letI : PreservesFiniteColimits (strictPerfectConstantSheaf J B) :=
    (strictPerfectConstantSheaf_exact J B).2
  let := hM
  let := hN
  let F := strictPerfectConstantSheaf J B
  let R := (constantSheaf J RingCat.{u}).obj (RingCat.of B)
  obtain ⟨n, q₀, hq⟩ := Module.Finite.exists_fin' B N
  let P := ModuleCat.of B (Fin n → B)
  let q : P ⟶ N := ModuleCat.ofHom q₀
  have : Epi q := (ModuleCat.epi_iff_surjective q).2 hq
  have : Module.Finite B (kernel q : ModuleCat.{u} B) :=
    Module.Finite.of_injective (kernel.ι q).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  let T := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hT : T.ShortExact := ⟨ShortComplex.exact_kernel q⟩
  have : Epi S.g := hS.epi_g
  obtain ⟨A, hA, h⟩ := exists_cover_lift_constant_finite_free S.X₂ S.X₃ S.g n U
    ((F.map q).over U ≫ eN.inv)
  refine ⟨A, hA, ?_⟩
  intro V f hf
  letI : PreservesFiniteLimits (overFunctor.{u} R V) := (overFunctor_exact R V).1
  letI : PreservesFiniteColimits (overFunctor.{u} R V) := (overFunctor_exact R V).2
  obtain ⟨l, hl⟩ := h V f hf
  let eMV := restrictIso S.X₁ (F.obj M) f.op eM
  let eNV := restrictIso S.X₃ (F.obj N) f.op eN
  let i := eMV.inv ≫ S.f.over V
  let p := S.g.over V ≫ eNV.hom
  have hip : i ≫ p = 0 := by
    simp only [i, p, Category.assoc, ← Functor.map_comp_assoc, S.zero,
      Functor.map_zero, zero_comp, comp_zero]
  let S' := ShortComplex.mk i p hip
  have hS' : S'.ShortExact := by
    refine ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (S₁ := S.map (overFunctor R V)) (S₂ := S')
        eMV (Iso.refl _) eNV ?_ ?_) (hS.map_of_exact (overFunctor R V))
    · simp [S', i]
      rfl
    · simp [S', p]
      rfl
  have hlp : l ≫ p = (F.map q).over V := by
    dsimp only [p]
    rw [← Category.assoc, hl]
    ext W x
    change eN.hom.val.app ((Over.map f).op.obj W)
      (eN.inv.val.app ((Over.map f).op.obj W) ((F.map q).val.app (Opposite.op W.unop.left) x)) =
      (F.map q).val.app (Opposite.op W.unop.left) x
    have he := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.val.app ((Over.map f).op.obj W)) eN.inv_hom_id)
      ((F.map q).val.app (Opposite.op W.unop.left) x)
    exact he
  have hTV := ((hT.map_of_exact F).map_of_exact (overFunctor R V))
  obtain ⟨g, hg, ⟨ec⟩⟩ := exists_cokernel_presentation_of_lift i p
    ((F.map (kernel.ι q)).over V) ((F.map q).over V) hip
    (by rw [← Functor.map_comp, ← Functor.map_comp, kernel.condition, Functor.map_zero,
      Functor.map_zero]) hS' hTV l hlp
  let e := (overFunctor R V).mapIso (F.mapBiprod M P) ≪≫
    (overFunctor R V).mapBiprod (F.obj M) (F.obj P)
  let a := biprod.lift (-g) ((F.map (kernel.ι q)).over V) ≫ e.inv
  have hQ : Module.Finite B (M ⊞ P : ModuleCat.{u} B) :=
    Module.Finite.of_surjective (ModuleCat.biprodIsoProd M P).inv.hom
      (ModuleCat.biprodIsoProd M P).toLinearEquiv.symm.surjective
  refine ⟨kernel q, M ⊞ P, inferInstance, hQ, a, ⟨ec ≪≫ ?_⟩⟩
  exact cokernel.mapIso _ a (Iso.refl _) e.symm (by simp [a])

end SheafOfModules
