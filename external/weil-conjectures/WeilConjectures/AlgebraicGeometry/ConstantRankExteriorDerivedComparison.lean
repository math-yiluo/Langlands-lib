/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso

/-! # A constant-rank exterior complex in the derived category

Source: Stacks Project, Tag 0BR0, the convention for a locally constant shift
(blueprint: lem-sc-constant-rank-exterior-derived-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

-- Naturality compares exterior maps across the scheme and ring-sheaf module interfaces.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def exteriorIso {X : Scheme.{u}} (M N : X.Modules)
    (d : ℕ) (e : M ≅ N) : exteriorPower M d ≅ exteriorPower N d := by
  let ep : M.val ≅ N.val := (toPresheafOfModules X).mapIso e
  let es (U : X.Opensᵒᵖ) : (_root_.PresheafOfModules.exteriorPower (R := _) M.val d).obj U ≅
      (_root_.PresheafOfModules.exteriorPower (R := _) N.val d).obj U :=
    (ModuleCat.exteriorPower.functor (X.presheaf.obj U) d).mapIso
      ((PresheafOfModules.evaluation X.ringCatSheaf.obj U).mapIso ep)
  let pe : _root_.PresheafOfModules.exteriorPower (R := _) M.val d ≅
      _root_.PresheafOfModules.exteriorPower (R := _) N.val d :=
    PresheafOfModules.isoMk es (by
      intro U V f
      let : CommRing (X.ringCatSheaf.obj.obj U) :=
        inferInstanceAs (CommRing (X.presheaf.obj U))
      let : CommRing (X.ringCatSheaf.obj.obj V) :=
        inferInstanceAs (CommRing (X.presheaf.obj V))
      apply ModuleCat.hom_ext
      apply exteriorPower.linearMap_ext
      ext a
      change exteriorPower.map d (e.hom.val.app V).hom
          ((_root_.PresheafOfModules.exteriorPower (R := _) M.val d).map f
            (exteriorPower.ιMulti (X.presheaf.obj U) d a)) =
        ((_root_.PresheafOfModules.exteriorPower (R := _) N.val d).map f)
          (exteriorPower.map d (e.hom.val.app U).hom (exteriorPower.ιMulti (X.presheaf.obj U) d a))
      have hm := (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := _) M.val d f) a
      have hn := (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := _) N.val d f)
          (fun i ↦ e.hom.val.app U (a i))
      have hu := exteriorPower.map_apply_ιMulti (R := X.presheaf.obj U) (n := d)
        (e.hom.val.app U).hom a
      have hv := exteriorPower.map_apply_ιMulti (R := X.presheaf.obj V) (n := d)
        (e.hom.val.app V).hom
        (fun i ↦ M.val.map f (a i))
      have he : (fun i ↦ e.hom.val.app V (M.val.map f (a i))) =
          (fun i ↦ N.val.map f (e.hom.val.app U (a i))) := by
        funext i
        exact PresheafOfModules.naturality_apply e.hom.val f (a i)
      erw [hu, hm, hv]
      change exteriorPower.ιMulti (X.presheaf.obj V) d
          (fun i ↦ e.hom.val.app V (M.val.map f (a i))) = _
      rw [he]
      exact hn.symm)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso pe

private theorem zeroPushforward {X Y : Scheme.{u}} [IsEmpty Y]
    (f : Y ⟶ X) (A : Y.Modules) : Limits.IsZero ((pushforward f).obj A) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply hom_ext
  intro U
  ext m
  let V := f ⁻¹ᵁ U
  have hV : V = ⊥ := by
    ext x
    exact isEmptyElim x
  have : Subsingleton (Y.presheaf.obj (Opposite.op V)) := by
    rw [hV]
    infer_instance
  have hs : Subsingleton (A.val.obj (Opposite.op V)) :=
    Module.subsingleton (Y.presheaf.obj (Opposite.op V)) (A.val.obj (Opposite.op V))
  change (m : A.val.obj (Opposite.op V)) = 0
  exact hs.elim _ _

private theorem termIso {X : Scheme.{u}} (M : X.Modules) (d : ℕ) (i : ℤ) :
    Nonempty (locallyRankedExteriorTerm M (LocallyConstant.const X d) i ≅
      if i = (d : ℤ) then exteriorPower M d else
        (Limits.HasZeroObject.zero (C := X.Modules)).choose) := by
  classical
  by_cases hi : i = (d : ℤ)
  · subst i
    have hrank : exteriorRankOpen (LocallyConstant.const X d) d = ⊤ := by
      ext x
      simp [exteriorRankOpen]
    let T (U : X.Opens) : X.Modules :=
      (pushforward U.ι).obj (exteriorPower ((restrictFunctor U.ι).obj M) d)
    simp only [locallyRankedExteriorTerm, Int.natCast_nonneg, ite_eq_left, Int.toNat_natCast]
    change Nonempty (T (exteriorRankOpen (LocallyConstant.const X d) d) ≅ exteriorPower M d)
    rw [hrank]
    exact exteriorSheaf_fullOpen_pushforward_iso M d
  · simp only [ite_eq_right hi]
    by_cases hn : 0 ≤ i
    · have hd : d ≠ i.toNat := by
        intro h
        apply hi
        simpa [h] using (Int.toNat_of_nonneg hn).symm
      have : IsEmpty (exteriorRankOpen (LocallyConstant.const X d) i.toNat).toScheme :=
        ⟨fun x ↦ hd x.property⟩
      rw [locallyRankedExteriorTerm, ite_eq_left hn]
      exact ⟨(zeroPushforward _ _).isoZero⟩
    · simp only [locallyRankedExteriorTerm, ite_eq_right hn]
      exact ⟨Iso.refl _⟩

/-- A constant rank function gives a single exterior power in the indicated degree;
an isomorphism of the input sheaves transports that exterior power.
No smoothness, local freeness or duality hypothesis is needed.
Source: Stacks Project, Tag 0BR0, the expression wedge^r N[-r]
(blueprint: lem-sc-constant-rank-exterior-derived-comparison).

Proof: the fibre of the constant function d over d is all of X, while each other
fibre is empty. Restriction and pushforward along the inclusion of the full open
compose to the identity, and exterior powers commute with this restriction.
Pushforward from an empty open is zero. Thus the locally ranked exterior complex
has exteriorPower M d in degree d and zero in every other degree, with zero
 differential. The sectionwise exterior-power maps induced by e and e.inv commute
with restrictions (check on pure wedges) and are inverse; sheafification gives
exteriorPower M d isomorphic to exteriorPower N d. These maps give a degreewise
isomorphism to the single complex with that sheaf in degree d. Apply the derived
localization functor, and the single/shift comparison: a single in degree d is
the degree-zero single shifted by -d. Empty X and d = 0 obey the same calculation. -/
theorem constantRankExterior_derived_iso {X : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M N : X.Modules) (d : ℕ) (e : M ≅ N) :
    Nonempty (((DerivedCategory.Q (C :=
      SheafOfModules.{u} (moduleRings X.toRingedSpace))).obj
        (locallyRankedExteriorComplex M (LocallyConstant.const X d))) ≅
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (exteriorPower N d))⟦-(d : ℤ)⟧) := by
  classical
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let F : C := exteriorPower M d
  let K : CochainComplex C ℤ :=
    locallyRankedExteriorComplex M (LocallyConstant.const X d)
  let S : CochainComplex C ℤ := (CochainComplex.singleFunctor C (d : ℤ)).obj F
  have components (i : ℤ) : Nonempty (K.X i ≅ S.X i) := by
    obtain ⟨t⟩ := termIso M d i
    by_cases hi : i = (d : ℤ)
    · exact ⟨(t ≪≫ eqToIso (ite_eq_left hi)) ≪≫
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) (d : ℤ) F i hi).symm⟩
    · exact ⟨(t ≪≫ eqToIso (ite_eq_right hi)) ≪≫
        ((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (d : ℤ) F i hi).isoZero).symm⟩
  let c : K ≅ S := HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (components i).some) (by
      intro i j hij
      have hj : i + 1 = j := hij
      subst j
      simp [S, K, CochainComplex.singleFunctor,
        locallyRankedExteriorComplex, HomologicalComplex.single_obj_d])
  exact ⟨DerivedCategory.Q.mapIso c ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ C (d : ℤ)).app F).symm ≪≫
    (DerivedCategory.singleFunctor C (d : ℤ)).mapIso (exteriorIso M N d e) ≪≫
    (((DerivedCategory.singleFunctors C).shiftIso (-(d : ℤ)) (d : ℤ) 0
      (by simp)).app (exteriorPower N d)).symm⟩

end AlgebraicGeometry.Scheme.Modules
