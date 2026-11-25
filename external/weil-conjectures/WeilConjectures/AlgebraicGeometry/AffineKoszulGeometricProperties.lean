/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.AlgebraicGeometry.KoszulRestrictionZero

/-! # Geometric properties of the explicit affine Koszul complex
Source: Stacks Project, Tags 0A9A and 0663.
(blueprint: lem-pc-affine-koszul-geometric-properties).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- On any open of `Spec A`, the sheaf associated to an exterior power of `A^r` is free of
finite rank: the wedge basis of the exterior power gives the free generators. -/
theorem exists_tilde_exteriorPower_iso_free (A : Type u) [CommRing A] (r q : ℕ)
    (U : (Spec (.of A)).Opens) :
    ∃ m : ℕ, Nonempty
      ((SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) U).obj
        ((tilde.functor (.of A)).obj (ModuleCat.of A (⋀[A]^q (Fin r →₀ A)))) ≅
        SheafOfModules.free
          (R := (moduleRings (Spec (.of A)).toRingedSpace).over U) (ULift.{u} (Fin m))) := by
  classical
  let I := Set.powersetCard (Fin r) q
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower q
  let e : I ≃ ULift.{u} (Fin (Fintype.card I)) :=
    (Fintype.equivFin I).trans Equiv.ulift.symm
  let c := (b.reindex e).repr.toModuleIso
  let F := SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) U
  refine ⟨Fintype.card I, ⟨?_⟩⟩
  exact F.mapIso ((tilde.functor (.of A)).mapIso c ≪≫
      tildeFinsupp (ULift.{u} (Fin (Fintype.card I)))) ≪≫
    (SheafOfModules.mapFreeIso F (ULift.{u} (Fin (Fintype.card I))) (Iso.refl _)).symm

/-- The exterior power of degree `q` of `A^r` vanishes when `r < q`. -/
theorem isZero_exteriorPower_finsupp_of_lt (A : Type u) [CommRing A] (r q : ℕ) (hq : r < q) :
    IsZero (ModuleCat.of A (⋀[A]^q (Fin r →₀ A))) := by
  classical
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower q
  have : IsEmpty (Set.powersetCard (Fin r) q) := ⟨fun s ↦ by
    have h := Finset.card_le_univ s.val
    have hs : s.val.card = q := s.property
    simp only [Fintype.card_fin, hs] at h
    omega⟩
  have : Subsingleton (⋀[A]^q (Fin r →₀ A)) :=
    b.repr.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem koszul_strictly_perfect (A : Type u) [CommRing A] (r : ℕ)
    (f : Fin r → A) (U : (Spec (.of A)).Opens) :
    let K := ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      _ _ _ _ (tilde.functor (.of A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
      ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat))
    Scheme.IsStrictlyPerfect (Spec (.of A)) U
      (((SheafOfModules.overFunctor.{u}
        (moduleRings (Spec (.of A)).toRingedSpace) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) := by
  classical
  let L := ExteriorAlgebra.koszulComplex A r f
  let T := tilde.functor (.of A)
  let : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let F := SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) U
  have hpos (n : ℤ) (hn : 0 < n) :
      IsZero (F.obj (T.obj ((L.extend ComplexShape.embeddingDownNat).X n))) := by
    apply F.map_isZero
    apply T.map_isZero
    apply L.isZero_extend_X
    intro q
    change -(q : ℤ) ≠ n
    omega
  have hneg (n : ℤ) (hn : n ≤ 0) : ∃ q : ℕ, -(q : ℤ) = n := by
    exact ⟨(-n).toNat, by omega⟩
  refine ⟨⟨-(r : ℤ), 0, ?_⟩, ?_⟩
  · intro n hn
    change IsZero (F.obj (T.obj ((L.extend ComplexShape.embeddingDownNat).X n)))
    by_cases hp : 0 < n
    · exact hpos n hp
    · obtain ⟨q, hq⟩ := hneg n (by omega)
      have hrq : r < q := by omega
      exact (F.map_isZero (T.map_isZero (isZero_exteriorPower_finsupp_of_lt A r q hrq))).of_iso
        (F.mapIso (T.mapIso (L.extendXIso ComplexShape.embeddingDownNat hq)))
  · intro n
    change ∃ m : ℕ, ∃ (ι : F.obj (T.obj
        ((L.extend ComplexShape.embeddingDownNat).X n)) ⟶ _)
      (π : _ ⟶ F.obj (T.obj ((L.extend ComplexShape.embeddingDownNat).X n))),
        ι ≫ π = 𝟙 _
    by_cases hp : 0 < n
    · exact ⟨0, 0, 0, (hpos n hp).eq_of_src _ _⟩
    · obtain ⟨q, hq⟩ := hneg n (by omega)
      obtain ⟨m, ⟨e⟩⟩ := exists_tilde_exteriorPower_iso_free A r q U
      let e' := F.mapIso (T.mapIso (L.extendXIso ComplexShape.embeddingDownNat hq)) ≪≫ e
      exact ⟨m, e'.hom, e'.inv, e'.hom_inv_id⟩

private theorem stalk_subsingleton_of_zero_over (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hM : IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj M))
    (x : X) (hx : x ∈ U) :
    Subsingleton (↑(TopCat.Presheaf.stalk M.val.presheaf x)) := by
  have hz (a : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) : a = 0 := by
    obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf a
    have hres : M.val.presheaf.map
        (homOfLE inf_le_left : V ⊓ U ⟶ V).op s = 0 := by
      have hid := (IsZero.iff_id_eq_zero _).mp hM
      have he := congrArg (fun g ↦ g.val.app
        (Opposite.op (Over.mk
          (homOfLE inf_le_right : V ⊓ U ⟶ U)))
        (M.val.presheaf.map
          (homOfLE inf_le_left : V ⊓ U ⟶ V).op s)) hid
      exact he
    rw [← TopCat.Presheaf.germ_res_apply M.val.presheaf
      (homOfLE inf_le_left : V ⊓ U ⟶ V) x ⟨hxV, hx⟩ s, hres]
    exact map_zero _
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

/-- The actual sheafified finite Koszul complex is perfect and acyclic
where one of its defining functions is invertible.
Source: Stacks Project, Tag 0A9A, affine paragraph, and Tag 0663.
(blueprint: lem-pc-affine-koszul-geometric-properties).

Proof: In cochain degree -q the complex is the sheaf associated to the q-th exterior
power of the free module on Fin r; these are finite free and vanish for q > r.
On every principal affine neighbourhood, restriction identifies these sheaves with
finite free modules over the restricted structure sheaf. Thus the displayed complex
is locally strictly perfect, with bounds -r and 0. For a point not containing f i,
multiplication by f i is a unit in
its local ring. Exterior multiplication by the i-th basis vector is a homotopy
between multiplication by f i and zero (Tag 0663); after localization this contracts
the complex. All its homology stalks therefore vanish at that point.
For r = 0 the support assertion has no hypotheses satisfied, and the complex is the
structure sheaf in degree zero. The zero ring has no points and causes no exception. -/
theorem affine_koszul_geometric_properties
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))] :
    let Q := DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        _ _ _ _ (tilde.functor (.of A))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat))
    Scheme.IsPerfect (Spec (.of A)) Q ∧
      ∀ (n : ℤ) (x : PrimeSpectrum A), (∃ i, f i ∉ x.asIdeal) →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj
            Q).val.presheaf x)) := by
  classical
  let C := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let K := ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A) C
    _ _ _ _ (tilde.functor (.of A))
    ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
    ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat))
  change Scheme.IsPerfect (Spec (.of A)) (DerivedCategory.Q.obj K) ∧ _
  constructor
  · intro x
    let F := SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) ⊤
    refine ⟨⊤, trivial, (F.mapHomologicalComplex (.up ℤ)).obj K,
      koszul_strictly_perfect A r f ⊤, ⟨F.mapDerivedCategoryFactors.app K⟩⟩
  · intro n x hx
    let U : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    let F := SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U
    have hxU : x ∈ U := by
      obtain ⟨i, hi⟩ := hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
    have hzshift := isZero_restrict_shift_koszul A r f U rfl (0 : ℤ)
    have hz : IsZero (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) :=
      hzshift.of_iso (F.mapDerivedCategory.mapIso
        ((CategoryTheory.shiftFunctorZero (DerivedCategory C) ℤ).app
          (DerivedCategory.Q.obj K)).symm)
    let e : (DerivedCategory.homologyFunctor _ n).obj
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≅
        F.obj ((DerivedCategory.homologyFunctor C n).obj (DerivedCategory.Q.obj K)) :=
      (DerivedCategory.homologyFunctor _ n).mapIso (F.mapDerivedCategoryFactors.app K) ≪≫
        (DerivedCategory.homologyFunctorFactors _ n).app _ ≪≫
        (F.mapHomologicalComplexHomologyIso (.up ℤ) n).app K ≪≫
        F.mapIso ((DerivedCategory.homologyFunctorFactors C n).symm.app K)
    exact stalk_subsingleton_of_zero_over (Spec (.of A)) U _
      (((DerivedCategory.homologyFunctor _ n).map_isZero hz).of_iso e.symm) x hxU

end AlgebraicGeometry
