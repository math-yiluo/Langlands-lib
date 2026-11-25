/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Cohomology of the one-column finite free Hom complex

Source: Stacks Project, Tag 08I5, the one-column Hom calculation.
(blueprint: lem-sc-single-supported-finite-free-homology-iso)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

private noncomputable def soleFactorIso {B : Type u} [Category B] [HasZeroMorphisms B]
    {f : ℤ → B} (c : Fan f) (hc : IsLimit c) (i : ℤ)
    (hz : ∀ j, j ≠ i → IsZero (f j)) : c.pt ≅ f i where
  hom := c.proj i
  inv := hc.lift (Fan.mk (f i) (fun j ↦ if h : j = i then eqToHom (congrArg f h.symm) else 0))
  hom_inv_id := by
    apply hc.hom_ext
    rintro ⟨j⟩
    rw [Category.assoc, hc.fac]
    by_cases h : j = i
    · subst j
      simp
      rfl
    · exact (hz j h).eq_of_tgt _ _
  inv_hom_id := by
    change hc.lift (Fan.mk (f i)
      (fun j ↦ if h : j = i then eqToHom (congrArg f h.symm) else 0)) ≫
      c.π.app (Discrete.mk i) = 𝟙 (f i)
    rw [hc.fac]
    simp

private lemma homMap_zero_left
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {A A' B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} :
    SheafOfModules.homObjMap (R := R) (0 : A' ⟶ A) (𝟙 B) = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map (𝟙 B : B ⟶ B).val = 0
  ext W x
  change ((𝟙 B : B ⟶ B).val.app _).hom ((φ.app W).hom 0) = 0
  rw [map_zero, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- A one-column finite free source gives a finite sum of shifted target cohomology.

Source: Stacks Project, Tag 08I5, the finite-free column calculation in its proof;
Tag 0A8X, the product Hom differential.
Proof: in each Hom degree project to source degree k. Every other factor is zero
because its source is zero; the inverse is the product lift with that component
and zero elsewhere. The source differential is zero: for the only potentially
nonzero source degree its next term is zero. Thus projection intertwines the Hom
differential with postcomposition by the target differential. Evaluate on the r
basis sections under hfree. This naturally identifies internal Hom from E^k with
r copies of the target module, compatibly with restrictions and differentials.
We obtain the reindexed complex with terms r copies of I^(k+n) and differential
r copies of d_I. The reindexing has no sign change because it translates the
complex shape directly. Finite biproducts are exact in any abelian category and
therefore commute with kernels and cokernels, hence with homology. This gives the
asserted isomorphism. The coproduct and biproduct coincide because the index is
finite. For r=0 both sides are zero; the same reasoning applies to empty opens
and unbounded targets.
(blueprint: lem-sc-single-supported-finite-free-homology-iso). -/
theorem single_supported_finiteFree_homology_iso
    (X : Scheme.{u}) (U : X.Opens)
    (E I : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (k : ℤ) (hE : ∀ i : ℤ, i ≠ k → IsZero (E.X i))
    (r : ℕ) (hfree : E.X k ≅ SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r))) (n : ℤ) :
    Nonempty (((homComplex (R := X.toRingedSpace.sheaf.over U) E I).homology n) ≅
      ∐ (fun _ : ULift.{u} (Fin r) ↦ I.homology (k + n))) := by
  classical
  let R := X.toRingedSpace.sheaf.over U
  let A := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  let H : A ⥤ A := (SheafOfModules.homFunctor R).obj (op (E.X k))
  let : H.Additive := ⟨by
    intro M N f g
    apply SheafOfModules.hom_ext
    ext W φ
    rfl⟩
  let : H.PreservesHomology := (Functor.exact_tfae H).out 1 3 |>.mp (by
    intro S hS
    obtain ⟨hz, hs, _⟩ := SheafOfModules.finiteFreeInternalHomExact (R := R) r (E.X k) hfree S hS
    exact hs)
  obtain ⟨π, hlim, hdiff, _⟩ :=
    homComplex_projections_exists.{u, u, u, u} (R := R)
  let K := homComplex (R := R) E I
  let proj (j : ℤ) : K.X j ⟶ H.obj (I.X (k + j)) := π E I j k (k + j) rfl
  have hz (j p : ℤ) (hp : p ≠ k) :
      IsZero (SheafOfModules.homObj (R := R) (E.X p) (I.X (p + j))) :=
    ((SheafOfModules.homFunctor R).flip.obj (I.X (p + j))).map_isZero (hE p hp).op
  have hproj (j : ℤ) : IsIso (proj j) := by
    exact (soleFactorIso _ (Classical.choice (hlim E I j)) k (hz j)).isIso_hom
  let ep (j : ℤ) : K.X j ≅ H.obj (I.X (k + j)) := @asIso _ _ _ _ (proj j) (hproj j)
  have hd (j l : ℤ) (hjl : j + 1 = l) :
      K.d j l ≫ (ep l).hom = (ep j).hom ≫ H.map (I.d (k + j) (k + l)) := by
    have h := hdiff E I j l k (k + l) (k + j) (k + 1) hjl rfl rfl (by omega)
    have hzero : E.d k (k + 1) = 0 := (hE (k + 1) (by omega)).eq_of_tgt _ _
    change K.d j l ≫ proj l = proj j ≫
      SheafOfModules.homObjMap (R := R) (𝟙 (E.X k)) (I.d (k + j) (k + l))
    dsimp only [K, homComplex, proj]
    simpa only [hzero, homMap_zero_left, comp_zero, smul_zero, sub_zero] using h
  let S := I.sc' (k + (n - 1)) (k + n) (k + (n + 1))
  let eS : K.sc' (n - 1) n (n + 1) ≅ S.map H :=
    ShortComplex.isoMk (ep (n - 1)) (ep n) (ep (n + 1))
      (hd (n - 1) n (by omega)).symm (hd n (n + 1) rfl).symm
  let eK := K.homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp)
  let eI := I.homologyIsoSc' (k + (n - 1)) (k + n) (k + (n + 1))
    (by simp; omega) (by simp; omega)
  let eHom : H.obj (I.homology (k + n)) ≅
      ∐ (fun _ : ULift.{u} (Fin r) ↦ I.homology (k + n)) :=
    ((SheafOfModules.homFunctor R).flip.obj (I.homology (k + n))).mapIso hfree.symm.op ≪≫
      SheafOfModules.homObjFreeIso.{u} (R := R) (I.homology (k + n))
        (ULift.{u} (Fin r)) ≪≫
      biproduct.isoCoproduct (fun _ : ULift.{u} (Fin r) ↦ I.homology (k + n))
  exact ⟨eK ≪≫ ShortComplex.homologyMapIso eS ≪≫ S.mapHomologyIso H ≪≫
    H.mapIso eI.symm ≪≫ eHom⟩

end AlgebraicGeometry
