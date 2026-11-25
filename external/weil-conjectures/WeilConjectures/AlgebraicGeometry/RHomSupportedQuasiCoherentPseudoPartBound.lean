/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution

/-! # Lower bound for internal Hom out of a pseudo-coherent complex

The local lower-bound clause of the pseudo-coherent internal-Hom lemma: for `K`
pseudo-coherent and `L` bounded below, every point has an open neighbourhood on which the
cohomology sheaves of `RHom(K, L)` vanish below some degree (Stacks Project, Tag 0A6H,
clause (1)). -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem homObj_isZero_of_source
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P Z : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hP : IsZero P) : IsZero (SheafOfModules.homObj (R := R) P Z) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← SheafOfModules.homObjMap_id (R := R) (M := P) (N := Z), hP.eq_zero_of_src (𝟙 P)]
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map (𝟙 Z.val) = 0
  ext W x
  change (φ.app W).hom 0 = 0
  exact map_zero _

private theorem homObj_isZero_of_target
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P Z : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hZ : IsZero Z) : IsZero (SheafOfModules.homObj (R := R) P Z) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← SheafOfModules.homObjMap_id (R := R) (M := P) (N := Z), hZ.eq_zero_of_tgt (𝟙 Z)]
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map (𝟙 P.val) ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map 0 = 0
  ext W x
  rfl

private theorem homComplex_isStrictlyGE
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (b m : ℤ) (hP : ∀ i : ℤ, b < i → IsZero (P.X i))
    [I.IsStrictlyGE m] : (homComplex (R := R) P I).IsStrictlyGE (m - b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  obtain ⟨π, hπ, _, _⟩ := Classical.choose_spec
    (homComplex_exists (C := C) (J := J) (R := R))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (hπ P I n).some.hom_ext
  intro j
  by_cases hj : b < j.as
  · exact (homObj_isZero_of_source J R _ _ (hP j.as hj)).eq_of_tgt _ _
  · exact (homObj_isZero_of_target J R _ _
      (I.isZero_of_isStrictlyGE m (j.as + n) (by omega))).eq_of_tgt _ _

/-- The local lower-bound component of the pseudo-coherent internal-Hom lemma.

Source: Stacks Project, Tag 0A6H, clause (1).
On an affine neighbourhood carrying a bounded-above finite-free model of the source,
the affine Hom-complex estimate gives a lower bound; exact restriction transports it
to the stated neighbourhood. This is split from quasi-coherence to isolate the
cohomological estimate.
(blueprint: new-lem-sc-rhom-supported-qcoherent-pseudo-part-bound). -/
theorem rhom_supported_quasiCoherent_pseudo_part_bound
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hL : schemeDerivedQCohProperty X L)
    (hK : Scheme.IsPseudoCoherent X K) (hGE : ∃ a : ℤ, L.IsGE a) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
            ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).obj (op K, L)))) := by
  -- The lower bound itself does not require quasi-coherence.
  have _hQC := hL
  intro x
  obtain ⟨U, hxU, P, hPbound, _hPfinite, ⟨eP⟩⟩ := hK x
  obtain ⟨b, hb⟩ := hPbound
  obtain ⟨a, ha⟩ := hGE
  let D := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let : Category.{w} (@DerivedCategory (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X.toRingedSpace).over U)
        (forget₂ CommRingCat RingCat)).obj (X.toRingedSpace.sheaf.over U))) _ _
      (inferInstanceAs (HasDerivedCategory.{w} D))) :=
    inferInstanceAs (Category.{w} (DerivedCategory D))
  let QU := DerivedCategory.Q (C := D)
  let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  have hLU : (F.mapDerivedCategory.obj L).IsGE a := by
    rw [DerivedCategory.isGE_iff]
    intro n hn
    exact (F.map_isZero ((DerivedCategory.isGE_iff L a).mp ha n hn)).of_iso
      ((F.mapDerivedCategoryHomologyFunctorIso n).app L).symm
  let := hLU
  obtain ⟨G, hG, ⟨eG⟩⟩ :=
    (F.mapDerivedCategory.obj L).exists_iso_Q_obj_of_isGE a
  let := hG
  obtain ⟨I, i, hi, ⟨m, hm⟩, _hIinj, hI⟩ :=
    SheafOfModules.exists_boundedBelow_injective_resolution
      ((Opens.grothendieckTopology X.toRingedSpace).over U)
      (X.toRingedSpace.sheaf.over U) G ⟨a, hG⟩
  let := hi
  let := hm
  let := hI
  let eI : QU.obj I ≅ F.mapDerivedCategory.obj L :=
    (asIso (QU.map i)).symm ≪≫ eG.symm
  obtain ⟨eH⟩ := @derivedInternalHom_obj_iso.{u, w} (Over U) _
    ((Opens.grothendieckTopology X.toRingedSpace).over U)
    (X.toRingedSpace.sheaf.over U)
    (inferInstanceAs (HasDerivedCategory.{w} D))
    (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L) P I inferInstance eP.symm eI
  obtain ⟨eR⟩ := derivedInternalHom_restrict_open X.toRingedSpace U K L
  have hHom := homComplex_isStrictlyGE
    ((Opens.grothendieckTopology X.toRingedSpace).over U)
    (X.toRingedSpace.sheaf.over U) P I b m hb
  let := hHom
  have hQ : (QU.obj
      (homComplex (R := X.toRingedSpace.sheaf.over U) P I)).IsGE (m - b) :=
    inferInstance
  refine ⟨U, hxU, m - b, ?_⟩
  intro n hn
  have hzero := (DerivedCategory.isGE_iff _ (m - b)).mp hQ n hn
  exact hzero.of_iso
    (((F.mapDerivedCategoryHomologyFunctorIso n).app _) ≪≫
      (DerivedCategory.homologyFunctor D n).mapIso (eR.symm ≪≫ eH))

end AlgebraicGeometry
