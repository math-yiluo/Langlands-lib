/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension
import WeilConjectures.AlgebraicGeometry.FieldEquivariantGermsOnePoint

/-!
# Global sections under the abelian Galois stalk equivalence

Source: Stacks Project, Etale Cohomology, Tag 04JM, lemma-global-sections-point.
(blueprint: lem-sc-etale-global-sections-galois-invariants).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The image of the canonical terminal germ map is precisely the invariant subgroup.

Source: Stacks Project, Tags 04JM and 04JQ.
(blueprint: aux-etale-global-sections-image).

Proof: A terminal section has the same germ after any change of lift, because
there is only one lift to a terminal object. Extend each Galois automorphism to
Omega and apply the action compatibility hypothesis to obtain invariance.
Conversely, represent an invariant germ on a finite separable extension inside
Ks: shrink an etale neighbourhood to the finite connected component containing
the geometric point. Enlarge to a finite Galois extension L/K. Restriction on
connected pointed neighbourhoods is injective by sheaf separatedness, since a
further nonempty etale neighbourhood covers the connected field spectrum.
Thus invariance of the germ implies that its representative over L is fixed
by Gal(L/K). The sheaf equalizer for the finite Galois cover Spec L of Spec K
then descends that representative to a terminal section. Its germ is the given
one. This argument only uses finite separable subextensions, so it also applies
when Omega contains transcendental elements. -/
theorem etaleGlobalSections_galoisInvariants_image
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (T : (Spec (.of K)).Etale) (hT : Limits.IsTerminal T)
    (E : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (i : E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ (Gal(Ks/K)) ⋙
      Action.forget (ModuleCat.{u + 1} ℤ) (Gal(Ks/K)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber)
    (hi : ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
      (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω) →
      ∀ (X : (Spec (.of K)).Etale)
      (x x' : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X),
      x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left →
      ∀ (z : F.obj.obj (op X)),
      (i.hom.app F) ((E.functor.obj F).obj.ρ g
        ((i.inv.app F) ((pointSmallEtale
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x F.obj z))) =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' F.obj z)
    (x : (pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj T)
    : ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (v : (E.functor.obj F).obj.V),
      v ∈ (@Representation.invariants ℤ _ (E.functor.obj F).obj.V _ _
        (E.functor.obj F).obj.hV1 (E.functor.obj F).obj.hV2 (E.functor.obj F).obj.ρ) ↔
      ∃ z : F.obj.obj (op T),
      (i.inv.app F) ((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber T x F.obj z) = v := by
  classical
  intro F v
  let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  let U : (Spec (.of K)).Etale :=
    MorphismProperty.Over.mk ⊤ (𝟙 (Spec (.of K))) (by infer_instance)
  let r : T ⟶ U := MorphismProperty.Over.homMk T.hom
  let j := hT.from U
  have hj : T.hom ≫ j.left = 𝟙 T.left :=
    congrArg (fun q : T ⟶ T ↦ q.left) (hT.hom_ext (r ≫ j) (𝟙 T))
  constructor
  · intro hv
    have : Limits.PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
      Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    let Fset : Sheaf (Spec (.of K)).smallEtaleTopology (Type (u + 1)) :=
      ⟨F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1},
        (Presheaf.isSheaf_iff_isSheaf_forget _ _ _).mp F.property⟩
    let c := (p.sheafFiberCompIso (CategoryTheory.forget AddCommGrpCat.{u + 1})).hom.app F
    let e : p.sheafFiber.obj Fset ≃
        (p.sheafFiber (A := AddCommGrpCat.{u + 1})).obj F :=
      Equiv.ofBijective c (ConcreteCategory.bijective_of_isIso c)
    have he (X : (Spec (.of K)).Etale) (y : p.fiber.obj X)
        (z : F.obj.obj (op X)) :
        e (p.toPresheafFiber X y Fset.obj z) = p.toPresheafFiber X y F.obj z := by
      have h := p.toPresheafFiber_presheafFiberCompIso_hom_app
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) X y F.obj
      exact congrArg (fun q ↦ q z) h
    let ρ : Gal(Ks/K) → p.sheafFiber.obj Fset → p.sheafFiber.obj Fset :=
      fun g a ↦ e.symm ((i.hom.app F) ((E.functor.obj F).obj.ρ g ((i.inv.app F) (e a))))
    have hρ : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
        (hτ : (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω))
        (X : (Spec (.of K)).Etale) (y y' : p.fiber.obj X)
        (hy : y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left)
        (z : Fset.obj.obj (op X)),
        ρ g (p.toPresheafFiber X y Fset.obj z) =
          p.toPresheafFiber X y' Fset.obj z := by
      intro g τ hτ X y y' hy z
      apply e.injective
      change e (e.symm ((i.hom.app F) ((E.functor.obj F).obj.ρ g
        ((i.inv.app F) (e (p.toPresheafFiber X y Fset.obj z)))))) = _
      rw [e.apply_symm_apply, he, he]
      exact hi F g τ hτ X y y' hy z
    have hv' : ∀ g, (E.functor.obj F).obj.ρ g v = v := hv
    have hsub : Subsingleton T.left := ⟨fun c d ↦ by
      have hc := congrArg (fun q : T.left ⟶ T.left ↦ q c) hj
      have hd := congrArg (fun q : T.left ⟶ T.left ↦ q d) hj
      have hb : T.hom c = T.hom d := by
        exact @Subsingleton.elim (Spec (.of K)) _ _ _
      exact hc.symm.trans ((congrArg j.left hb).trans hd)⟩
    let : Subsingleton T.left := hsub
    let : Nonempty T.left := ⟨x.left (default : Spec (.of Ω))⟩
    obtain ⟨z, hz⟩ := onePoint_selected_lift_section.{u, u + 1} K Ks Ω Fset T x ρ hρ
      (fun _ ↦ e.symm ((i.hom.app F) v)) (by
        intro g τ hτ y y' hy
        change e.symm ((i.hom.app F) v) =
          e.symm ((i.hom.app F) ((E.functor.obj F).obj.ρ g
            ((i.inv.app F) (e (e.symm ((i.hom.app F) v))))))
        rw [e.apply_symm_apply, ← ConcreteCategory.comp_apply, i.hom_inv_id_app]
        change e.symm ((i.hom.app F) v) =
          e.symm ((i.hom.app F) ((E.functor.obj F).obj.ρ g v))
        rw [hv' g])
    refine ⟨z, ?_⟩
    have hz' := congrArg e hz
    rw [he, e.apply_symm_apply] at hz'
    rw [hz', ← ConcreteCategory.comp_apply, i.hom_inv_id_app]
    rfl
  · rintro ⟨z, rfl⟩
    change ∀ g, (E.functor.obj F).obj.ρ g ((i.inv.app F)
      (p.toPresheafFiber T x F.obj z)) = (i.inv.app F) (p.toPresheafFiber T x F.obj z)
    intro g
    obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K Ks Ω g
    have hbase : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      rw [← Spec.map_comp]
      congr 1
      ext a
      exact τ.commutes a
    have hx : x.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left := by
      have hxj : x.left =
          Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ j.left := by
        calc
          x.left = x.left ≫ (T.hom ≫ j.left) := by
            rw [hj]
            exact (Category.comp_id x.left).symm
          _ = _ := (Category.assoc _ _ _).symm.trans
            (congrArg (fun q : Spec (.of Ω) ⟶ Spec (.of K) ↦ q ≫ j.left) (Over.w x))
      rw [hxj, ← Category.assoc, hbase]
    apply (ConcreteCategory.bijective_of_isIso (i.hom.app F)).1
    change (i.hom.app F) ((E.functor.obj F).obj.ρ g ((i.inv.app F)
      (p.toPresheafFiber T x F.obj z))) =
      (i.hom.app F) ((i.inv.app F) (p.toPresheafFiber T x F.obj z))
    rw [← ConcreteCategory.comp_apply, i.inv_hom_id_app]
    exact hi F g τ hτ T x x hx z

end AlgebraicGeometry.Scheme
