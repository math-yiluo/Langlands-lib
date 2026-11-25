/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyProduct


@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem fan_projection_isIso
    {A : Type*} [Category A] [HasZeroMorphisms A]
    {I : Type*} {F : I → A} {H : A}
    (g : ∀ i, H ⟶ F i) (hg : IsLimit (Fan.mk H g))
    (j : I) (hz : ∀ i, i ≠ j → IsZero (F i)) : IsIso (g j) := by
  classical
  let v : F j ⟶ H := Fan.IsLimit.lift hg
    (fun i ↦ if h : j = i then eqToHom (congrArg F h) else 0)
  have hv : ∀ i, v ≫ g i = if h : j = i then eqToHom (congrArg F h) else 0 :=
    fun i ↦ Fan.IsLimit.fac hg _ i
  refine ⟨⟨v, ?_, ?_⟩⟩
  · apply Fan.IsLimit.hom_ext hg
    intro i
    by_cases hi : i = j
    · subst i
      simp [Category.assoc, hv]
    · exact (hz i hi).eq_of_tgt _ _
  · simpa using hv j

private theorem homObj_isZero_right
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u})
    (A B : SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (hB : IsZero B) : IsZero (SheafOfModules.homObj (R := R) A B) := by
  apply (IsZero.iff_id_eq_zero _).2
  rw [← SheafOfModules.homObjMap_id (R := R)]
  rw [hB.eq_of_src (𝟙 B) 0]
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver R.obj U.unop).map (𝟙 A.val) ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj U.unop).map 0 = 0
  ext W x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Invertibility of the cycle-compatible finite-free homology evaluation map.

Source: Stacks Project, Tag 0BQY, finite-free Hom calculation in Lemma 48.15.4;
Tag 0A8X, the product terms and differential of the Hom complex.
(blueprint: new-v4-finite-free-zero-homology-evaluation-iso).

Proof: The fixed projections identify the Hom complex with the product over p
of complexes having terms Hom(E.X p,K.X(p+n)). Their differentials have only the
K term, since the E differential vanishes. Remove the zero factors outside the
finite interval specified by hsupp, leaving a finite product. For each remaining
p, choose the given finite-free basis; internal Hom out of E.X p is thereby
naturally a finite product of copies of the identity. It is exact by
finiteFreeInternalHomExact, so its homology is Hom(E.X p,H^(p+n)(K)). Finite
products in an abelian category preserve kernels and cokernels, hence homology.
By hK all factors except p=-n are zero. The surviving projection thus induces
an isomorphism g from H^n(Hom(E,K)) to Hom(E.X(-n),H^0(K)). Since E has zero
differentials, both its cycle inclusion and class map are isomorphisms.
The equation hc identifies c with the kernel lift of this same projection;
the equation hf identifies f, after these E isomorphisms, with g. Cancel the
P class epimorphism to obtain that equality. Consequently f is an isomorphism.
If -n is outside the support all surviving objects are zero. Rank zero, a zero
ring, and empty site objects give the same calculation. This proves only
invertibility of a supplied compatible map, not existence or cycle descent. -/
theorem finiteFreeZero_homologyEvaluation_iso
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u})
    (E K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n : ℤ) (hK : ∀ k : ℤ, k ≠ 0 → IsZero (K.homology k))
    (hzero : ∀ a b : ℤ, E.d a b = 0)
    (hsupp : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (E.X k))
    (hfree : ∀ k : ℤ, ∃ r : ℕ, Nonempty (E.X k ≅
      SheafOfModules.free (ULift.{u} (Fin r))))
    (f : (homComplex (R := R) E K).homology n ⟶
      SheafOfModules.homObj (R := R) (E.homology (-n)) (K.homology 0))
    (c : (homComplex (R := R) E K).cycles n ⟶
      SheafOfModules.homObj (R := R) (E.cycles (-n)) (K.cycles 0))
    (hc : c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
      (homComplex (R := R) E K).iCycles n ≫
        (Classical.choose (homComplex_projections_exists (R := R)))
          E K n (-n) 0 (by omega) ≫
        SheafOfModules.homObjMap (R := R) (E.iCycles (-n)) (𝟙 _))
    (hf : c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
      (homComplex (R := R) E K).homologyπ n ≫ f ≫
        SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _)) :
    IsIso f := by
  classical
  let P := homComplex (R := R) E K
  obtain ⟨g, ⟨hg⟩, hcomp⟩ := finiteFreeZero_homologyProduct R E K n hzero hsupp hfree
  have hgIso : IsIso (g (-n) (-n + n) rfl) :=
    fan_projection_isIso (fun p ↦ g p (p + n) rfl) hg (-n) (by
      intro p hp
      exact homObj_isZero_right R _ _ (hK (p + n) (by omega)))
  have hgIso' : ∀ q (h : -n + n = q), IsIso (g (-n) q h) := by
    intro q h
    subst q
    exact hgIso
  have hgIso0 : IsIso (g (-n) 0 (by omega)) := hgIso' 0 (by omega)
  have : IsIso (E.iCycles (-n)) :=
    E.isIso_iCycles (-n) (-n + 1) (by simp) (hzero _ _)
  have : IsIso (E.homologyπ (-n)) :=
    E.isIso_homologyπ (-n - 1) (-n) (by simp) (hzero _ _)
  let d := c ≫ SheafOfModules.homObjMap (R := R) (inv (E.iCycles (-n))) (𝟙 _)
  have hd : d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
      P.iCycles n ≫ (Classical.choose (homComplex_projections_exists (R := R)))
        E K n (-n) 0 (by omega) := by
    dsimp only [d]
    calc
      _ = c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) ≫
          SheafOfModules.homObjMap (R := R) (inv (E.iCycles (-n))) (𝟙 _) := by
        simp only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
          Category.id_comp, Category.comp_id]
      _ = _ := by
        rw [← Category.assoc c, hc]
        simp only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
          IsIso.inv_hom_id, SheafOfModules.homObjMap_id,
          Category.comp_id, P]
  have hdπ := hcomp (-n) 0 (by omega) d hd
  have heq : f ≫ SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _) ≫
      SheafOfModules.homObjMap (R := R) (inv (E.iCycles (-n))) (𝟙 _) =
      g (-n) 0 (by omega) := by
    apply (cancel_epi (P.homologyπ n)).1
    rw [← hdπ]
    simpa only [P, d, Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
      Category.id_comp, Category.comp_id] using
      congrArg (fun t ↦ t ≫ SheafOfModules.homObjMap (R := R)
        (inv (E.iCycles (-n))) (𝟙 (K.homology 0))) hf.symm
  have : IsIso (SheafOfModules.homObjMap (R := R) (E.homologyπ (-n))
      (𝟙 (K.homology 0))) :=
    inferInstanceAs (IsIso (((SheafOfModules.homFunctor R).flip.obj
      (K.homology 0)).map (E.homologyπ (-n)).op))
  have : IsIso (SheafOfModules.homObjMap (R := R) (inv (E.iCycles (-n)))
      (𝟙 (K.homology 0))) :=
    inferInstanceAs (IsIso (((SheafOfModules.homFunctor R).flip.obj
      (K.homology 0)).map (inv (E.iCycles (-n))).op))
  have : IsIso (f ≫ SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _) ≫
      SheafOfModules.homObjMap (R := R) (inv (E.iCycles (-n))) (𝟙 _)) := by
    rw [heq]
    exact hgIso0
  exact IsIso.of_isIso_comp_right f
    (SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _) ≫
      SheafOfModules.homObjMap (R := R) (inv (E.iCycles (-n))) (𝟙 _))

end CategoryTheory
