/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompletedCoefficients
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientRingComparison

/-! # Local integer approximations of reconstructed completed coefficients

Source: the integer-modulo-powers step of the local generator argument.
(blueprint: lem-sfb-completed-coefficient-local-integers).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory Opposite
namespace CategoryTheory

/-- The sieve where a ring section is an integer modulo a specified natural multiple.
Source: integer-modulo-powers linearity criterion
(blueprint: lem-sfb-completed-coefficient-local-integers). -/
def integerApproximationSieve {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w}) (k : ℕ)
    {V : Cᵒᵖ} (r : R.obj.obj V) : Sieve V.unop where
  arrows W f := ∃ (a : ℤ) (b : R.obj.obj (op W)),
    R.obj.map f.op r = a + k • b
  downward_closed := by
    rintro W Z f ⟨a, b, hb⟩ h
    refine ⟨a, R.obj.map h.op b, ?_⟩
    rw [op_comp, R.obj.map_comp, ConcreteCategory.comp_apply, hb]
    simp only [map_add, map_intCast, map_nsmul]

end CategoryTheory
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

open CategoryTheory.Limits

attribute [local irreducible] upperStarFromPoint
  InternalAbelianSheafModule.sectionModuleEquivalenceCore
  Scheme.purTwistZlCompletionOfUniverses
open scoped CategoryTheory.Obj CategoryTheory.Functor

private theorem localImageOfCokernel (X : Scheme.{u})
    {A B Q : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    (f : A ⟶ B) (q : B ⟶ Q) (h : f ≫ q = 0)
    (hc : IsColimit (CokernelCofork.ofπ q h)) (V : X.ProEtᵒᵖ)
    (x : B.obj.obj V) (hx : q.hom.app V x = 0) :
    Presheaf.imageSieve f.hom x ∈ Scheme.ProEt.topology X V.unop := by
  let S := ShortComplex.mk f q h
  have hS : S.Exact := S.exact_of_g_is_cokernel hc
  have := hS.epi_toCycles
  have : Sheaf.IsLocallySurjective S.toCycles :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := S.toCycles)).2 inferInstance
  let E := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
    (evaluation _ _).obj V
  let hk := KernelFork.mapIsLimit _ S.cyclesIsKernel E
  let φ : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ E.obj B := AddCommGrpCat.ofHom
    { toFun := fun k ↦ k.down • x
      map_zero' := zero_zsmul x
      map_add' := fun a b ↦ add_zsmul x a.down b.down }
  have hφ : φ ≫ E.map q = 0 := by
    ext k
    change q.hom.app V (k.down • x) = 0
    rw [map_zsmul, hx, smul_zero]
  obtain ⟨t, ht⟩ := KernelFork.IsLimit.lift' hk φ hφ
  let z := t (ULift.up (1 : ℤ))
  have hz : S.iCycles.hom.app V z = x := by
    have hh := ConcreteCategory.congr_hom ht (ULift.up (1 : ℤ))
    exact hh.trans (one_zsmul x)
  refine (Scheme.ProEt.topology X).superset_covering ?_
    (Presheaf.imageSieve_mem _ S.toCycles.hom z)
  rintro W i ⟨y, hy⟩
  refine ⟨y, ?_⟩
  have hh := congrArg (fun g ↦ g.hom.app (op W) y) S.toCycles_i
  dsimp only at hh
  rw [← hh, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, hy, NatTrans.naturality_apply, hz]

private theorem constantCommuteUnit {C D B : Type*} [Category* C] [Category* D]
    [Category* B] (J : GrothendieckTopology C) (U : D ⥤ B)
    [HasWeakSheafify J D] [HasWeakSheafify J B]
    [J.HasSheafCompose U] [J.PreservesSheafification U] (A : D) :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) U ≫
        ((constantCommuteCompose J U).hom.app A).hom =
      (Functor.constComp Cᵒᵖ A U).hom ≫
        toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj A)) := by
  rw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
    sheafComposeIso_inv_fac, ← toSheafify_naturality]

private theorem constantAbUnit (X : Scheme.{u}) (A : CommRingCat.{u + 1})
    (V : X.ProEtᵒᵖ) (x : A) :
    (sfbConstantRingAbIso X A).hom.hom.app V
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj A)).app V x) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app V x := by
  let J := Scheme.ProEt.topology X
  let : J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let : J.PreservesSheafification (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  have h₁ := congrArg (fun t ↦ t.app V x)
    (constantCommuteUnit J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) A)
  have h₂ := congrArg (fun t ↦ t.app V x)
    (constantCommuteUnit J (forget₂ RingCat.{u + 1} Ab.{u + 1})
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj A))
  exact (congrArg (fun z ↦ ((constantCommuteCompose J
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).hom.app
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj A)).hom.app V z) h₁).trans h₂

private theorem reductionCokernelPositive (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (n : ℕ) :
    ∃ h : (purZlPowerMultiplication l X (n + 1)).hom ≫
        (purZlReduction l X (n + 1)).hom = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (purZlReduction l X (n + 1)).hom h)) := by
  obtain ⟨m, e, he⟩ := pur_condensed_zl_reduction_mod_ell_power l X
  let f := purZlPowerMultiplication l X (n + 1)
  let d := (Mod.forget
    (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)).mapIso (e n)
  have hd : cokernel.π f.hom ≫ d.hom = (purZlReduction l X (n + 1)).hom :=
    (he.1 n).2.2.2
  have hz : f.hom ≫ (purZlReduction l X (n + 1)).hom = 0 := by
    rw [← hd, ← Category.assoc, cokernel.condition, zero_comp]
  exact ⟨hz, ⟨IsCokernel.ofIso _ (cokernelIsCokernel f.hom)
    (CokernelCofork.ofπ _ hz) (Iso.refl _) (Iso.refl _) d
      (by simp) (by simpa using hd.symm)⟩⟩

/-- Reconstructed completed coefficients are locally integers modulo every positive
ell-power. This involves only the coefficient ring, with no modules or additive maps.

Source: the first step of lem-sfb-diagonal-completed-free-generator;
lem-pur-condensed-zl-reduction-mod-ell-power and the normalized coefficient comparison.
(blueprint: lem-sfb-completed-coefficient-local-integers).

Proof: reduce the section by purZlReduction at exponent n+1. The residue sheaf is the
constant cyclic ring Z/l^(n+1), so locally its section is the image of an integer a.
The difference from a is in the kernel of reduction. The cokernel calculation in
pur_condensed_zl_reduction_mod_ell_power says this kernel is the sheaf image of
multiplication by l^(n+1). Refine the cover to lift the difference to a section b.
Reconstruction of section rings preserves the underlying abelian sheaves and their
integer multiples, so the resulting equality is precisely r=a+l^(n+1)b. The local
lifts define the displayed covering sieve. This also handles the empty object. -/
theorem completedCoefficient_localIntegers (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (n : ℕ) :
    let S := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X)
          (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))
    ∀ (V : X.ProEtᵒᵖ) (r : S.obj.obj V),
      integerApproximationSieve S (l ^ (n + 1)) r ∈ Scheme.ProEt.topology X V.unop := by
  intro S V r
  classical
  let J := Scheme.ProEt.topology X
  let A := CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))
  let F := sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let G := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  obtain ⟨e, he, _⟩ := completedCoefficientRingComparison_existsUnique l X
  let q : S ⟶ G.obj (Scheme.purTwistFiniteRing X l n) :=
    e.hom ≫ G.map (Scheme.purTwistZlProjection X l n)
  let ρ : F.obj S ⟶ (constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of A) :=
    (purZlReduction l X (n + 1)).hom
  let d := sfbConstantRingAbIso X A
  have hq : F.map q ≫ d.hom = ρ := by
    dsimp only [q]
    rw [Functor.map_comp, Category.assoc, ← he n, ← Category.assoc,
      ← Functor.map_comp, e.hom_inv_id, F.map_id, Category.id_comp]
  let η := toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))
  have hcast (T : X.ProEtᵒᵖ) (a : ℤ) :
      ρ.hom.app T (a : S.obj.obj T) = η.app T (a : A) := by
    rw [← hq]
    change d.hom.hom.app T (q.hom.app T (a : S.obj.obj T)) = _
    rw [map_intCast]
    have hh := constantAbUnit X A T (a : A)
    have ha := map_intCast
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj A)).app T).hom a
    exact (congrArg (d.hom.hom.app T) ha).symm.trans hh
  refine J.transitive (Presheaf.imageSieve_mem J η (ρ.hom.app V r)) _ ?_
  rintro W f ⟨z, hz⟩
  let a : ℤ := z.down.val
  have haz : (a : A) = z := by
    apply ULift.ext
    change ((z.down.val : ℤ) : ZMod (l ^ (n + 1))) = z.down
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val z.down
  have hx : ρ.hom.app (op W) (S.obj.map f.op r - (a : S.obj.obj (op W))) = 0 := by
    rw [map_sub, hcast]
    apply sub_eq_zero.mpr
    have hn := NatTrans.naturality_apply ρ.hom f.op r
    exact hn.trans (hz.symm.trans (congrArg (η.app (op W)) haz.symm))
  obtain ⟨hzero, ⟨hc⟩⟩ :
      ∃ h : (l ^ (n + 1) • 𝟙 (F.obj S)) ≫ ρ = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ ρ h)) :=
    reductionCokernelPositive l X n
  have hl := localImageOfCokernel X _ _ hzero hc (op W)
    (S.obj.map f.op r - (a : S.obj.obj (op W))) hx
  refine J.superset_covering ?_ hl
  rintro Z j ⟨b, hb⟩
  let b' : S.obj.obj (op Z) := b
  refine ⟨a, b', ?_⟩
  have hb' : l ^ (n + 1) • b' =
      S.obj.map j.op (S.obj.map f.op r - (a : S.obj.obj (op W))) := hb
  rw [map_sub, map_intCast] at hb'
  change S.obj.map (j ≫ f).op r = (a : S.obj.obj (op Z)) + l ^ (n + 1) • b'
  rw [op_comp, S.obj.map_comp, ConcreteCategory.comp_apply, hb']
  abel

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
