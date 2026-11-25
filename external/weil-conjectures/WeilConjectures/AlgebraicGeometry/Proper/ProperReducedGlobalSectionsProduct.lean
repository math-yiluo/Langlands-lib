/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Clopen
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Global functions on a proper reduced scheme over an algebraically closed field

## References

* Stacks Project, Varieties, Tag 0BUG, clauses (1)--(3)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Global functions are the product of the scalars indexed by connected components.
The ring equivalence commutes with the actual scalar structure map, making it a
`k`-algebra equivalence. Its germ formula specifies the canonical constant-on-components map. -/
theorem proper_reduced_globalSections_product
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))] [IsReduced X] :
    Finite (ConnectedComponents X) ∧
      (∀ x : X, IsClopen (connectedComponent x)) ∧
      (∃ e : (ConnectedComponents X → k) ≃+* Γ(X, ⊤),
        (∀ a : k, e (fun _ ↦ a) =
          (X ↘ Spec (CommRingCat.of k)).appTop
            ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)) ∧
        ∀ (a : ConnectedComponents X → k) (x : X),
          X.presheaf.germ ⊤ x trivial (e a) =
            X.presheaf.germ ⊤ x trivial
              ((X ↘ Spec (CommRingCat.of k)).appTop
                ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (a (ConnectedComponents.mk x))))) ∧
      (IsEmpty X → IsEmpty (ConnectedComponents X) ∧
        Subsingleton (ConnectedComponents X → k) ∧ Subsingleton Γ(X, ⊤)) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of k))
  have : IsNoetherian X := {}
  have hcl : ∀ x : X, IsClopen (connectedComponent x) := fun _ ↦
    isClopen_connectedComponent
  refine ⟨inferInstance, hcl, ?_, ?_⟩
  · let C := ConnectedComponents X
    let p : C → X := fun c ↦ (ConnectedComponents.surjective_coe c).choose
    have hp (c : C) : ConnectedComponents.mk (p c) = c :=
      (ConnectedComponents.surjective_coe c).choose_spec
    let U : C → X.Opens := fun c ↦ ⟨connectedComponent (p c), (hcl (p c)).isOpen⟩
    have hmem (x : X) (c : C) : x ∈ U c ↔ ConnectedComponents.mk x = c := by
      change x ∈ connectedComponent (p c) ↔ _
      rw [← ConnectedComponents.coe_eq_coe', hp]
    have hU (c : C) : IsClosed (U c : Set X) := (hcl (p c)).isClosed
    have hbij (c : C) : Function.Bijective
        ((U c).topIso.hom.hom.comp (globalSectionsRingHom k (X := (U c).toScheme))) := by
      have : IsClosedImmersion (U c).ι :=
        IsClosedImmersion.of_isPreimmersion _ (by simpa using hU c)
      have : IsProper ((U c).toScheme ↘ Spec (CommRingCat.of k)) :=
        inferInstanceAs (IsProper ((U c).ι ≫ X ↘ Spec (CommRingCat.of k)))
      have : ConnectedSpace (U c).toScheme :=
        isConnected_iff_connectedSpace.mp isConnected_connectedComponent
      exact (ConcreteCategory.bijective_of_isIso (U c).topIso.hom).comp
        (GlobalSectionsBijective.bijective_globalSectionsRingHom (k := k))
    let E (c : C) : k ≃+* Γ(X, U c) := RingEquiv.ofBijective _ (hbij c)
    let res (c : C) : Γ(X, ⊤) →+* Γ(X, U c) :=
      (X.presheaf.map (homOfLE le_top : U c ⟶ ⊤).op).hom
    have hE (c : C) (a : k) : E c a = res c (globalSectionsRingHom k a) := by
      change (U c).topIso.hom
        (globalSectionsRingHom k (X := (U c).toScheme) a) = _
      change (U c).topIso.hom
        (((ΓSpecIso (CommRingCat.of k)).inv ≫
          ((U c).ι ≫ X ↘ Spec (CommRingCat.of k)).appTop) a) = _
      rw [Hom.comp_appTop]
      change ((U c).ι.appTop ≫ (U c).topIso.hom) (globalSectionsRingHom k a) = _
      simp only [Opens.ι_appTop, Opens.topIso_hom, ← Functor.map_comp]
      rfl
    let R : Γ(X, ⊤) →+* (∀ c : C, Γ(X, U c)) := RingHom.pi res
    have hinj : Function.Injective R := by
      intro a b hab
      apply TopCat.Presheaf.section_ext X.sheaf ⊤ a b
      intro x _
      change X.presheaf.germ ⊤ x trivial a = X.presheaf.germ ⊤ x trivial b
      let c : C := ConnectedComponents.mk x
      have hx : x ∈ U c := (hmem x c).mpr rfl
      have heq := congrFun hab c
      have hg := congrArg (X.presheaf.germ (U c) x hx) heq
      simpa only [R, RingHom.pi_apply, res,
        TopCat.Presheaf.germ_res_apply] using hg
    have hsurj : Function.Surjective R := by
      intro a
      have hcover : (⊤ : X.Opens) ≤ ⨆ c, U c := by
        intro x _
        exact TopologicalSpace.Opens.mem_iSup.mpr
          ⟨ConnectedComponents.mk x, (hmem x _).mpr rfl⟩
      have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U a := by
        intro c d
        by_cases hcd : c = d
        · subst d
          rfl
        · apply TopCat.Presheaf.section_ext X.sheaf _ _ _
          intro x hx
          exact (hcd ((hmem x c).mp hx.1 |>.symm.trans ((hmem x d).mp hx.2))).elim
      obtain ⟨s, hs, _⟩ := X.sheaf.existsUnique_gluing' U ⊤
        (fun c ↦ homOfLE le_top) hcover a hcompat
      exact ⟨s, funext hs⟩
    let e : (C → k) ≃+* Γ(X, ⊤) :=
      (RingEquiv.piCongrRight E).trans (RingEquiv.ofBijective R ⟨hinj, hsurj⟩).symm
    have he (a : C → k) (c : C) : res c (e a) = E c (a c) := by
      exact congrFun ((RingEquiv.ofBijective R ⟨hinj, hsurj⟩).apply_symm_apply
        ((RingEquiv.piCongrRight E) a)) c
    refine ⟨e, ?_, ?_⟩
    · intro a
      apply hinj
      funext c
      exact (he (fun _ ↦ a) c).trans (hE c a)
    · intro a x
      let c : C := ConnectedComponents.mk x
      have hx : x ∈ U c := (hmem x c).mpr rfl
      have h := congrArg (X.presheaf.germ (U c) x hx) ((he a c).trans (hE c (a c)))
      change X.presheaf.germ ⊤ x trivial (e a) =
        X.presheaf.germ ⊤ x trivial (globalSectionsRingHom k (a c))
      simpa only [res, TopCat.Presheaf.germ_res_apply] using h
  · intro hX
    have : IsEmpty X := hX
    have : IsEmpty (ConnectedComponents X) :=
      ⟨fun c ↦ isEmptyElim (ConnectedComponents.surjective_coe c).choose⟩
    exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
