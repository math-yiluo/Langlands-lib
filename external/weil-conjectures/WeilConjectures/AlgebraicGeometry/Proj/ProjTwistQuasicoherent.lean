/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
import WeilConjectures.AlgebraicGeometry.ProjTwistBasicOpenFractions
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing

/-! # Quasi-coherence of the concrete twisting sheaf

## References

* Stacks Project, Constructions, Lemma 01MB and Definition 01MN
* Stacks Project, definition-twist (Tag 01MN)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open scoped DirectSum

open CategoryTheory Opposite TopologicalSpace LocalizedModule HomogeneousLocalization

namespace AlgebraicGeometry.Proj

private def shiftPiece
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) (j z : ℤ) : AddSubgroup A :=
  if 0 ≤ j + z then
    { carrier := 𝒜 (j + z).toNat
      zero_mem' := zero_mem _
      add_mem' := fun ha hb ↦ add_mem ha hb
      neg_mem' := fun ha ↦ neg_mem ha }
  else ⊥

private theorem shiftPiece_internal
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (j : ℤ) :
    DirectSum.IsInternal (shiftPiece 𝒜 j) := by
  classical
  let inc (n : ℕ) : 𝒜 n →+ shiftPiece 𝒜 j ((n : ℤ) - j) :=
    { toFun := fun a ↦ ⟨a, by simp [shiftPiece]⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let D : A →+ ⨁ z, shiftPiece 𝒜 j z :=
    (DirectSum.toAddMonoid (fun n : ℕ ↦
      (DirectSum.of _ ((n : ℤ) - j)).comp (inc n))).comp
        (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom
  have hD (z : ℤ) (a : shiftPiece 𝒜 j z) : D a = DirectSum.of _ z a := by
    by_cases hz : 0 ≤ j + z
    · have ha : (a : A) ∈ 𝒜 (j + z).toNat := by
        simpa [shiftPiece, hz] using a.property
      have he : ((j + z).toNat : ℤ) - j = z := by omega
      dsimp [D]
      change (DirectSum.toAddMonoid (fun n : ℕ ↦
        (DirectSum.of (fun z ↦ ↥(shiftPiece 𝒜 j z)) ((n : ℤ) - j)).comp (inc n)))
          (DirectSum.decompose 𝒜 (a : A)) = _
      rw [DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toAddMonoid_of]
      dsimp only [AddMonoidHom.comp_apply]
      generalize hn : (j + z).toNat = n at *
      obtain rfl : z = (n : ℤ) - j := he.symm
      rfl
    · have ha : a = 0 := by
        apply Subtype.ext
        simpa [shiftPiece, hz] using a.property
      subst a
      simp
  have hleft : Function.LeftInverse D (DirectSum.coeAddMonoidHom (shiftPiece 𝒜 j)) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of z a => simpa using hD z a
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨hleft.injective, ?_⟩
  intro a
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => exact ⟨0, map_zero _⟩
  | homogeneous a =>
    exact ⟨DirectSum.of _ _ (inc _ a), by simp [inc]⟩
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add _ _ _⟩

private theorem shiftPiece_smul
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (j : ℤ)
    (n : ℕ) (z : ℤ) (a y : A) (ha : a ∈ 𝒜 n)
    (hy : y ∈ shiftPiece 𝒜 j z) : a • y ∈ shiftPiece 𝒜 j (n + z) := by
  by_cases hz : 0 ≤ j + z
  · have hy' : y ∈ 𝒜 (j + z).toNat := by simpa [shiftPiece, hz] using hy
    have hpos : 0 ≤ j + (n + z) := by omega
    have he : (j + (n + z)).toNat = n + (j + z).toNat := by omega
    simpa [shiftPiece, hpos, he, smul_eq_mul] using SetLike.mul_mem_graded ha hy'
  · have hy' : y = 0 := by simpa [shiftPiece, hz] using hy
    subst y
    simp

private theorem isQuasicoherent_twist_addSubgroup
    {A : Type u} [CommRing A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (j : ℤ) :
    (twist 𝒜 j).IsQuasicoherent := by
  classical
  let (T : Submonoid A) : Module (HomogeneousLocalization 𝒜 T) (LocalizedModule T A) :=
    Module.compHom _ (algebraMap (HomogeneousLocalization 𝒜 T) (Localization T))
  let I := {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
  obtain ⟨Z, hZ, rhoS, rho, hlaw, hid, hcomp, hbij, F, alpha,
    hscalar, hres, hring, hunique, hqc, _⟩ :=
    gradedModuleSheaf_exists 𝒜 (shiftPiece 𝒜 j) (shiftPiece_internal 𝒜 j)
      (shiftPiece_smul 𝒜 j)
  obtain ⟨b, hb, hbscalar, hbres⟩ := single_twist_basicOpen_fractions 𝒜
  have hbrange (f : I) : Set.range (b j f.val.1 f.val.2 f.property.1 f.property.2) =
      (Z f : Set (LocalizedModule.Away f.val.1 A)) := by
    rw [(hb j f.val.1 f.val.2 f.property.1 f.property.2).2, hZ]
    congr 2
    funext n
    ext y
    by_cases h : 0 ≤ j + n <;> simp [shiftPiece, h]
  let beta (f : I) : (twist 𝒜 j).val.obj (op (basicOpen 𝒜 f.val.1)) ≃+ Z f :=
    AddEquiv.ofBijective
      ((b j f.val.1 f.val.2 f.property.1 f.property.2).codRestrict (Z f).toAddSubgroup
        (fun s ↦ by
          change b j f.val.1 f.val.2 f.property.1 f.property.2 s ∈ (Z f : Set _)
          rw [← hbrange f]
          exact ⟨s, rfl⟩))
      ⟨fun s t h ↦ (hb j f.val.1 f.val.2 f.property.1 f.property.2).1
          (congrArg Subtype.val h),
        fun q ↦ by
          have hq : (q : LocalizedModule.Away f.val.1 A) ∈
              Set.range (b j f.val.1 f.val.2 f.property.1 f.property.2) := by
            rw [hbrange f]
            exact q.property
          obtain ⟨s, hs⟩ := hq
          exact ⟨s, Subtype.ext hs⟩⟩
  have hbeta (f : I) (s : (twist 𝒜 j).val.obj (op (basicOpen 𝒜 f.val.1))) :
      (beta f s : LocalizedModule.Away f.val.1 A) =
        b j f.val.1 f.val.2 f.property.1 f.property.2 s := rfl
  obtain ⟨phi, hphi, _⟩ := hunique (twist 𝒜 j) beta (by
    intro f r s
    apply Subtype.ext
    exact hbscalar j f.val.1 f.val.2 f.property.1 f.property.2 r s) (by
    intro f g inc s
    obtain ⟨e, k, a, he, ha, heq⟩ := (hlaw f g inc).1
    have hrep : ∃ (y : A) (m : ℕ),
        (beta f s : LocalizedModule.Away f.val.1 A) =
          mk y (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) := by
      induction (beta f s : LocalizedModule.Away f.val.1 A)
          using LocalizedModule.induction_on with
      | h y t =>
        obtain ⟨m, hm⟩ := t.property
        exact ⟨y, m, by congr 1; exact Subtype.ext hm.symm⟩
    obtain ⟨y, m, hs⟩ := hrep
    apply Subtype.ext
    exact (hbres j f.val.1 g.val.1 f.val.2 g.val.2 f.property.1 g.property.1
      f.property.2 g.property.2 inc e k a he ha heq m y s hs).trans
        ((hlaw f g inc).2.2 e k a he ha heq m y (beta f s) hs).symm)
  have : IsIso phi := hphi.1
  exact (SheafOfModules.isQuasicoherent ((Proj 𝒜).ringCatSheaf)).prop_of_iso (asIso phi) hqc

private def regradeHom
    {A σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (h : ∀ n x, x ∈ 𝒜 n ↔ x ∈ ℬ n) : 𝒜 →+*ᵍ ℬ :=
  ⟨RingHom.id A, fun hx ↦ (h _ _).mp hx⟩

private theorem regrade_irrelevant
    {A σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (h : ∀ n x, x ∈ 𝒜 n ↔ x ∈ ℬ n) :
    HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒜).map (regradeHom 𝒜 ℬ h) := by
  apply toIdeal_le_toIdeal_iff.mp
  rw [HomogeneousIdeal.toIdeal_map]
  change (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (RingHom.id A)
  rw [Ideal.map_id, HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn a ha
  exact HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn ((h n a).mpr ha)

private noncomputable def regradeIso
    {A σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (h : ∀ n x, x ∈ 𝒜 n ↔ x ∈ ℬ n) : Proj ℬ ≅ Proj 𝒜 where
  hom := map (regradeHom 𝒜 ℬ h) (regrade_irrelevant 𝒜 ℬ h)
  inv := map (regradeHom ℬ 𝒜 (fun n x ↦ (h n x).symm))
    (regrade_irrelevant ℬ 𝒜 (fun n x ↦ (h n x).symm))
  hom_inv_id := by
    rw [← map_comp]
    have he : (regradeHom 𝒜 ℬ h).comp (regradeHom ℬ 𝒜 (fun n x ↦ (h n x).symm)) =
        GradedRingHom.id ℬ := by ext; rfl
    simp only [he, map_id]
  inv_hom_id := by
    rw [← map_comp]
    have he : (regradeHom ℬ 𝒜 (fun n x ↦ (h n x).symm)).comp (regradeHom 𝒜 ℬ h) =
        GradedRingHom.id 𝒜 := by ext; rfl
    simp only [he, map_id]

private noncomputable def regradeTwistMap
    {A σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (h : ∀ n x, x ∈ 𝒜 n ↔ x ∈ ℬ n) (j : ℤ) :
    twist 𝒜 j ⟶ (Scheme.Modules.pushforward (regradeIso 𝒜 ℬ h).hom).obj (twist ℬ j) := by
  let app (U : (Proj 𝒜).Opens) (s : (twist 𝒜 j).val.obj (op U)) :
      (twist ℬ j).val.obj (op ((regradeIso 𝒜 ℬ h).hom ⁻¹ᵁ U)) :=
    ⟨fun x ↦ ⟨(s.1 ⟨(regradeIso 𝒜 ℬ h).hom x.1, x.2⟩).1, by
      rcases (s.1 ⟨(regradeIso 𝒜 ℬ h).hom x.1, x.2⟩).2 with hz | hz
      · exact Or.inl hz
      · obtain ⟨i, k, a, b, hb, ha, hb', hik, he⟩ := hz
        exact Or.inr ⟨i, k, a, b, hb, (h i a).mp ha, (h k b).mp hb', hik, he⟩⟩, by
      intro x
      obtain ⟨V, hx, inc, i, k, hik, a, b, hb, he⟩ :=
        s.2 ⟨(regradeIso 𝒜 ℬ h).hom x.1, x.2⟩
      refine ⟨(regradeIso 𝒜 ℬ h).hom ⁻¹ᵁ V, hx,
        homOfLE (fun y hy ↦ inc.le hy), i, k, hik,
        ⟨a, (h i a).mp a.property⟩, ⟨b, (h k b).mp b.property⟩,
        (fun y ↦ hb ⟨(regradeIso 𝒜 ℬ h).hom y.1, y.2⟩), ?_⟩
      intro y
      apply Subtype.ext
      have he' := congrArg Subtype.val (he ⟨(regradeIso 𝒜 ℬ h).hom y.1, y.2⟩)
      exact he' ⟩
  exact ⟨PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := app U.unop
          map_zero' := by rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := by intros; rfl }
    (by
      intro U r s
      apply Subtype.ext
      funext x
      apply Subtype.ext
      change _ =
        (HomogeneousLocalization.localRingHom (regradeHom 𝒜 ℬ h) _ _ rfl
          (r.1 ⟨(regradeIso 𝒜 ℬ h).hom x.1, x.2⟩)).val * _
      rw [HomogeneousLocalization.val_localRingHom]
      have hid (p : Proj ℬ) :
          Localization.localRingHom
            ((regradeIso 𝒜 ℬ h).hom p).asHomogeneousIdeal.toIdeal
            p.asHomogeneousIdeal.toIdeal (RingHom.id A) rfl =
          RingHom.id (Localization.AtPrime p.asHomogeneousIdeal.toIdeal) :=
        Localization.localRingHom_id _
      exact congrArg (fun v ↦ v *
        (s.1 ⟨(regradeIso 𝒜 ℬ h).hom x.1, x.2⟩).1)
        (RingHom.congr_fun (hid x.1) _).symm)⟩

private theorem regradeTwistMap_injective
    {A σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (h : ∀ n x, x ∈ 𝒜 n ↔ x ∈ ℬ n) (j : ℤ) (U : (Proj 𝒜).Opens) :
    Function.Injective ((regradeTwistMap 𝒜 ℬ h j).app U) := by
  intro s t he
  apply Subtype.ext
  funext x
  apply Subtype.ext
  let y := (regradeIso 𝒜 ℬ h).inv x.1
  have hy : (regradeIso 𝒜 ℬ h).hom y = x.1 := by
    exact congrArg (fun f : Proj 𝒜 ⟶ Proj 𝒜 ↦ f x.1)
      (regradeIso 𝒜 ℬ h).inv_hom_id
  have hyU : y ∈ (regradeIso 𝒜 ℬ h).hom ⁻¹ᵁ U := by
    change (regradeIso 𝒜 ℬ h).hom y ∈ U
    rw [hy]
    exact x.2
  have he' := congrArg (fun v ↦ (v.1 ⟨y, hyU⟩).1) he
  change (s.1 ⟨(regradeIso 𝒜 ℬ h).hom y, hyU⟩).1 =
    (t.1 ⟨(regradeIso 𝒜 ℬ h).hom y, hyU⟩).1 at he'
  have hxy : (⟨(regradeIso 𝒜 ℬ h).hom y, hyU⟩ : U) = x := Subtype.ext hy
  have he'' : s.1 ⟨(regradeIso 𝒜 ℬ h).hom y, hyU⟩ =
      t.1 ⟨(regradeIso 𝒜 ℬ h).hom y, hyU⟩ := Subtype.ext he'
  exact congrArg Subtype.val (hxy ▸ he'')

private theorem regradeTwistMap_surjective
    {A σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (h : ∀ n x, x ∈ 𝒜 n ↔ x ∈ ℬ n) (j : ℤ) (U : (Proj 𝒜).Opens) :
    Function.Surjective ((regradeTwistMap 𝒜 ℬ h j).app U) := by
  let e := regradeIso 𝒜 ℬ h
  let g := (Scheme.Modules.pushforward e.hom).map
    (regradeTwistMap ℬ 𝒜 (fun n x ↦ (h n x).symm) j) ≫
      (Scheme.Modules.pushforwardComp e.inv e.hom).hom.app (twist 𝒜 j) ≫
      (Scheme.Modules.pushforwardCongr e.inv_hom_id).hom.app (twist 𝒜 j) ≫
      (Scheme.Modules.pushforwardId (Proj 𝒜)).hom.app (twist 𝒜 j)
  intro s
  refine ⟨g.app U s, ?_⟩
  apply Subtype.ext
  funext x
  apply Subtype.ext
  have hx : e.inv (e.hom x.1) = x.1 :=
    congrArg (fun f : Proj ℬ ⟶ Proj ℬ ↦ f x.1) e.hom_inv_id
  have hxU : e.inv (e.hom x.1) ∈ e.hom ⁻¹ᵁ U := by
    rw [hx]
    exact x.2
  change (s.1 ⟨e.inv (e.hom x.1), hxU⟩).1 = (s.1 x).1
  have hp : (⟨e.inv (e.hom x.1), hxU⟩ : e.hom ⁻¹ᵁ U) = x := Subtype.ext hx
  exact eq_of_heq (show HEq (s.1 ⟨e.inv (e.hom x.1), hxU⟩).1 (s.1 x).1 from
    by generalize (⟨e.inv (e.hom x.1), hxU⟩ : e.hom ⁻¹ᵁ U) = y at hp ⊢
       subst y
       rfl)

/-- Every integer twisting sheaf is quasi-coherent, without generation in degree one. -/
theorem isQuasicoherent_twist
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (j : ℤ) :
    (twist 𝒜 j).IsQuasicoherent := by
  let ℬ : ℕ → AddSubgroup A := fun n ↦
    { carrier := 𝒜 n
      zero_mem' := zero_mem _
      add_mem' := fun ha hb ↦ add_mem ha hb
      neg_mem' := fun ha ↦ neg_mem ha }
  let : SetLike.GradedMonoid ℬ :=
    { one_mem := SetLike.one_mem_graded 𝒜
      mul_mem := fun _ _ _ _ ha hb ↦ SetLike.mul_mem_graded (A := 𝒜) ha hb }
  let : GradedRing ℬ :=
    {
      decompose' := DirectSum.decompose 𝒜
      left_inv := (DirectSum.decompose 𝒜).left_inv
      right_inv := (DirectSum.decompose 𝒜).right_inv }
  have h : ∀ n x, x ∈ 𝒜 n ↔ x ∈ ℬ n := fun _ _ ↦ Iff.rfl
  let e := regradeIso 𝒜 ℬ h
  let f := regradeTwistMap 𝒜 ℬ h j
  have : (twist ℬ j).IsQuasicoherent := isQuasicoherent_twist_addSubgroup ℬ j
  have hqc := Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom e.hom (twist ℬ j)
  have : IsIso f := Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨regradeTwistMap_injective 𝒜 ℬ h j U, regradeTwistMap_surjective 𝒜 ℬ h j U⟩
  exact (SheafOfModules.isQuasicoherent ((Proj 𝒜).ringCatSheaf)).prop_of_iso
    (asIso f).symm hqc

end AlgebraicGeometry.Proj
