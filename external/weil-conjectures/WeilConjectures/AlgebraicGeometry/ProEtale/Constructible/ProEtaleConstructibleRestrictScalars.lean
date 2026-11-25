/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueLayerConstructible

/-!
# Constructibility under restriction of scalars between finite coefficient rings

Restriction of scalars along a ring map `A → B` of finite rings preserves constructibility of
pro-etale module sheaves. If the ring map is surjective, restriction also reflects
constructibility.

## References

* Stacks Project, Tags 09AJ and 093U
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- A sheaf of `B`-modules whose restriction of scalars along a surjective ring map
`f : A → B` is locally constant with finite stalks is itself locally constant with finite
stalks: on each member of the trivializing cover, it is the extension of scalars of its
restriction, and extension of scalars of a constant sheaf is constant. -/
theorem isFiniteLocallyConstant_of_restrictScalars {X : Scheme.{u}}
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (h : IsFiniteLocallyConstant A
      ((sheafCompose (Scheme.ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)).obj F)) :
    IsFiniteLocallyConstant B F := by
  obtain ⟨I, W, g, hg, h⟩ := h
  refine ⟨I, W, g, hg, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := h i
  let J := Scheme.ProEt.topology (W i)
  let adj := WeilConjectures.residueSheafExtendAdjunction f (W i)
  have := CategoryTheory.Sheaf.restrictScalars_full J f hf
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  let G := ((g i)^*[ModuleCat.{u + 1} B]).obj F
  let e₁ : (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)).obj G ≅
      (constantSheaf J (ModuleCat.{u + 1} A)).obj M :=
    ((WeilConjectures.residueRestrictionPullbackIso f (g i)).app F).symm ≪≫ e
  let E := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f
  let := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f).isLeftAdjoint
  let e₂ : (WeilConjectures.residueSheafExtend f (W i)).obj
      ((constantSheaf J (ModuleCat.{u + 1} A)).obj M) ≅
      (constantSheaf J (ModuleCat.{u + 1} B)).obj (E.obj M) :=
    (presheafToSheafCompComposeAndSheafifyIso J E).app ((Functor.const _).obj M) ≪≫
      (presheafToSheaf J _).mapIso (NatIso.ofComponents (fun _ ↦ Iso.refl _)
        (by intros; simp))
  let : Algebra A B := f.toAlgebra
  have : Module.Finite A M := hM
  refine ⟨E.obj M, ?_, ⟨(asIso (adj.counit.app G)).symm ≪≫
    (WeilConjectures.residueSheafExtend f (W i)).mapIso e₁ ≪≫ e₂⟩⟩
  exact inferInstanceAs (Module.Finite B (TensorProduct A B M))

/-- Constructibility of a sheaf of `B`-modules is reflected by restriction of scalars along a
surjective ring map `f : A → B`, with the same stratification. -/
theorem isConstructible_of_restrictScalars {X : Scheme.{u}}
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (h : IsConstructible A
      ((sheafCompose (Scheme.ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)).obj F)) :
    IsConstructible B F := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun i ↦ isFiniteLocallyConstant_of_restrictScalars f hf _
    (isFiniteLocallyConstant_of_iso
      ((WeilConjectures.residueRestrictionPullbackIso f (S.immersion i)).app F) (hS i))⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

/-- Restriction of scalars along a ring map `f: A → B` of finite rings preserves
constructibility of pro-etale module sheaves. -/
theorem IsConstructibleProEtaleModuleSheaf.restrictScalars {T : Scheme.{u}}
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (f : A →+* B)
    {F : proEtaleRingModules T (proEtaleConstantRing T B)}
    (hF : IsConstructibleProEtaleModuleSheaf T B F) :
    IsConstructibleProEtaleModuleSheaf T A
      ((proEtaleRingRestrictScalars ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).obj F) := by
  rw [proEtaleModuleRestriction_constructible_iff] at hF ⊢
  exact ProEtale.isConstructible_of_iso ((WeilConjectures.restrictionEncodingIso T f).app F).symm
    (WeilConjectures.fixedConstructible_restrict T (RingHom.ulift.{u + 1, u + 1} f) _ hF)

/-- Restriction of scalars along a surjective ring map `f: A → B` of finite rings reflects
constructibility of pro-etale module sheaves. -/
theorem IsConstructibleProEtaleModuleSheaf.of_restrictScalars {T : Scheme.{u}}
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (f : A →+* B)
    (hf : Function.Surjective f) {F : proEtaleRingModules T (proEtaleConstantRing T B)}
    (hF : IsConstructibleProEtaleModuleSheaf T A
      ((proEtaleRingRestrictScalars ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).obj F)) :
    IsConstructibleProEtaleModuleSheaf T B F := by
  rw [proEtaleModuleRestriction_constructible_iff] at hF ⊢
  have hf' : Function.Surjective (RingHom.ulift.{u + 1, u + 1} f) := fun b ↦
    ⟨ULift.up (hf b.down).choose, ULift.ext (hf b.down).choose_spec⟩
  exact ProEtale.isConstructible_of_restrictScalars _ hf' _
    (ProEtale.isConstructible_of_iso ((WeilConjectures.restrictionEncodingIso T f).app F) hF)

end AlgebraicGeometry.Scheme
