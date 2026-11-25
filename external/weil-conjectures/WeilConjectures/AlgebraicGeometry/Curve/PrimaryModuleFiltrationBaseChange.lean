/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.PrimaryModuleFiltrationFixedFieldComparison
import WeilConjectures.AlgebraicGeometry.Curve.PullbackStalkGermAction
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits ZeroObject Opposite
namespace AlgebraicGeometry.Scheme

private theorem discreteRep_iso_of_additive_iso
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A B : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ G)
    (k : AddCommGrpCat.of A.obj.V ≅ AddCommGrpCat.of B.obj.V)
    (hk : ∀ (g : G) (v : A.obj.V), k.hom (A.obj.ρ g v) = B.obj.ρ g (k.hom v)) :
    Nonempty (A ≅ B) := by
  let instA : Module ℤ A.obj.V := A.obj.hV2
  let instB : Module ℤ B.obj.V := B.obj.hV2
  let ℓ : A.obj.V →ₗ[ℤ] B.obj.V :=
    { toFun := k.hom
      map_add' := k.hom.hom.map_add
      map_smul' := fun n x ↦ map_intCast_smul k.hom.hom ℤ ℤ n x }
  let q : A.obj ⟶ B.obj := Rep.ofHom ⟨ℓ, fun g ↦ by
    ext v
    exact hk g v⟩
  have : Mono q := (Rep.mono_iff_injective q).mpr (by
    change Function.Injective k.hom
    exact (ConcreteCategory.bijective_of_isIso k.hom).1)
  have : Epi q := (Rep.epi_iff_surjective q).mpr (by
    change Function.Surjective k.hom
    exact (ConcreteCategory.bijective_of_isIso k.hom).2)
  have : IsIso q := isIso_of_mono_of_epi q
  exact ⟨ObjectProperty.isoMk _ (asIso q)⟩

/-- The stalk comparison and the supplied action formula identify the pullback along the
fixed-field inclusion with the sheaf transported by the fixed-field equivalence.  This is the
first (before transport along `e`) part of the inverse-image comparison; its proof is the
represented-germ construction from Stacks, Tags 03QT, 03QW and 04JQ.
(blueprint: lem-sc-primary-fixed-field-pullback-iso)

Proof: identify stalks by the pullback stalk theorem, use the supplied germ-action formula and
extensions of Galois automorphisms to obtain equivariance, then apply the full faithful
fixed-field equivalence and its unit/counit. -/
theorem primary_fixedField_pullback_iso
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (i : AddCommGrpCat.of R.obj.V ≅
      ((pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj M)
    (haction : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (_hτ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale)
      (x x' : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
      (_hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : M.obj.obj (op X)),
      i.hom (R.obj.ρ g (i.inv ((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x M.obj z))) =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' M.obj z)
    (H : OpenSubgroup (Gal(Ks/K)))
    [FiniteDimensional K (IntermediateField.fixedField H.toSubgroup)]
    (C : PrimaryFixedFieldEquivalence K Ks H)
    (hC : PrimaryFixedFieldComparison K Ks H Ω C)
    : Nonempty ((Etale.upperStar AddCommGrpCat.{u + 1}
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (IntermediateField.fixedField H.toSubgroup))))).obj M ≅
      C.inverse.obj (primaryRestrictedModule K Ks H R)) := by
  classical
  obtain ⟨fiberIso, hfiber⟩ := hC
  let L := IntermediateField.fixedField H.toSubgroup
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let s := Spec.map (CommRingCat.ofHom
    ((algebraMap Ks Ω).comp (algebraMap L Ks)))
  let t := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have hst : s ≫ f = t := by
    simp only [s, f, t, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply K L Ks,
      ← IsScalarTower.algebraMap_apply K Ks Ω]
  let F := (Etale.upperStar AddCommGrpCat.{u + 1} f).obj M
  let V := C.functor.obj F
  obtain ⟨j, hj⟩ := exists_etale_pullback_stalk_germ_action f s t hst M
  let k : AddCommGrpCat.of R.obj.V ≅ AddCommGrpCat.of V.obj.V :=
    i ≪≫ j.symm ≪≫ (fiberIso.app F).symm
  have hk (g : H.toSubgroup) (v : R.obj.V) :
      k.hom (R.obj.ρ (g : Gal(Ks/K)) v) = V.obj.ρ g (k.hom v) := by
    obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K Ks Ω g.val
    let τs := Spec.map (CommRingCat.ofHom τ.toRingHom)
    have hτs : τs ≫ s = s := by
      simp only [τs, s, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      have h := DFunLike.congr_fun hτ (algebraMap L Ks x)
      change algebraMap Ks Ω ((g : Gal(Ks/K)) (algebraMap L Ks x)) =
        τ (algebraMap Ks Ω (algebraMap L Ks x)) at h
      change τ (algebraMap Ks Ω (algebraMap L Ks x)) =
        algebraMap Ks Ω (algebraMap L Ks x)
      exact h.symm.trans (congrArg (algebraMap Ks Ω) (x.property g))
    let a := (fiberIso.inv.app F) ≫
      AddCommGrpCat.ofHom (V.obj.ρ g).toAddMonoidHom ≫ (fiberIso.hom.app F)
    let b := i.inv ≫ AddCommGrpCat.ofHom
      (R.obj.ρ (g : Gal(Ks/K))).toAddMonoidHom ≫ i.hom
    have hcomm := hj τs hτs a b
      (fun U x x' hx z ↦ hfiber F g τ hτ U x x' hx z)
      (fun U x x' hx z ↦ haction g.val τ hτ U x x' hx z)
    have h := ConcreteCategory.congr_hom hcomm (j.inv (i.hom v))
    change b (j.hom (j.inv (i.hom v))) = j.hom (a (j.inv (i.hom v))) at h
    have h' := congrArg (fun z ↦ (fiberIso.app F).inv (j.inv z)) h
    change (fiberIso.app F).inv (j.inv (i.hom (R.obj.ρ g.val v))) =
      V.obj.ρ g ((fiberIso.app F).inv (j.inv (i.hom v)))
    simp only [a, b, ConcreteCategory.comp_apply] at h'
    change (fiberIso.app F).inv
        (j.inv (i.hom (R.obj.ρ g.val (i.inv (j.hom (j.inv (i.hom v))))))) =
      (fiberIso.app F).inv (j.inv (j.hom ((fiberIso.app F).hom
        (V.obj.ρ g ((fiberIso.app F).inv (j.inv (i.hom v))))))) at h'
    simpa only [Iso.inv_hom_id_apply, Iso.hom_inv_id_apply] using h'
  obtain ⟨e⟩ := discreteRep_iso_of_additive_iso
    (primaryRestrictedModule K Ks H R) V k hk
  exact ⟨(C.unitIso.app F) ≪≫ C.inverse.mapIso e.symm⟩

end AlgebraicGeometry.Scheme
