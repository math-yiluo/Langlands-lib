/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # Normalized transport of tensor-pullback sections

Source: Stacks Project, Tag 03DR, equation-quasi-coherent-presheaf.
(blueprint: lem-sc-etale-tensor-sections-transport) -/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private noncomputable def sectionsEquiv {Y : Scheme.{u}} {M N : Y.Modules} (k : M ≅ N) :
    Γ(M, ⊤) ≃+ Γ(N, ⊤) where
  toFun := k.hom.app ⊤
  invFun := k.inv.app ⊤
  map_add' := (k.hom.app ⊤).hom.map_add
  left_inv s := by
    change (k.hom ≫ k.inv).app ⊤ s = s
    rw [k.hom_inv_id]
    rfl
  right_inv s := by
    change (k.inv ≫ k.hom).app ⊤ s = s
    rw [k.inv_hom_id]
    rfl

private theorem sectionsEquiv_apply {Y : Scheme.{u}} {M N : Y.Modules} (k : M ≅ N)
    (s : Γ(M, ⊤)) : sectionsEquiv k s = k.hom.app ⊤ s := rfl

private theorem sectionsEquiv_smul {Y : Scheme.{u}} {M N : Y.Modules} (k : M ≅ N)
    (b : Γ(Y, ⊤)) (s : Γ(M, ⊤)) : sectionsEquiv k (b • s) = b • sectionsEquiv k s :=
  Hom.app_smul k.hom b s

attribute [local irreducible] sectionsEquiv

private theorem transportForFamily
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (c : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      L b ⋙ L a ≅ L (a ≫ b))
    (η : ∀ {A B : Scheme.{u}} (a : A ⟶ B) (G : B.Modules),
      Γ(G, ⊤) ⟶ Γ((L a).obj G, ⊤))
    {X : Scheme.{u}} (F : X.Modules) {U V : X.Etale} (a : V ⟶ U) :
    ∃ e : Γ((L a.left).obj ((L U.hom).obj F), ⊤) ≃+
      Γ((L V.hom).obj F, ⊤),
      ∀ (m : Γ((L U.hom).obj F, ⊤)) (b : Γ(V.left, ⊤)),
        e (b • η a.left ((L U.hom).obj F) m) =
          b • (η a.left ((L U.hom).obj F) ≫
            ((c a.left U.hom).hom.app F).app ⊤ ≫
            (eqToHom (congrArg (fun f ↦ (L f).obj F) a.w)).app ⊤) m := by
  let k : (L a.left).obj ((L U.hom).obj F) ≅ (L V.hom).obj F :=
    (c a.left U.hom).app F ≪≫ eqToIso (congrArg (fun f ↦ (L f).obj F) a.w)
  refine ⟨sectionsEquiv k, ?_⟩
  intro m b
  rw [sectionsEquiv_smul, sectionsEquiv_apply]
  congr 1

private theorem restriction_eq {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (a : V ⟶ U) :
    etaleTensorSectionsRestriction F a =
      tensorSectionsUnit a.left ((tensorPullback U.hom).obj F) ≫
        ((tensorSectionsComp a.left U.hom).hom.app F).app ⊤ ≫
        (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) a.w)).app ⊤ := rfl

/-- Transport from an iterated tensor pullback to the pullback of an etale object,
with the normalized unit equation on global sections.
Source: Stacks Project, Tag 03DR, equation-quasi-coherent-presheaf.
(blueprint: lem-sc-etale-tensor-sections-transport)

Proof: let k be the component at F of tensorSectionsComp a.left U.hom followed
by equality transport along a.w. Both factors are module isomorphisms on V.left.
Taking global sections therefore gives an additive equivalence e; its inverse is
obtained by taking sections of the inverse module isomorphism. Module-linearity
of k gives e(b times s) = b times e(s) for every section s. By the definition of
etaleTensorSectionsRestriction, e applied to tensorSectionsUnit a.left applied to m
is exactly the restriction of m: evaluation of the composite of module morphisms
is composition of their section maps. Set s equal to this unit section and combine
these two equations. Neither quasi-coherence nor affineness nor nonemptiness is used.
The construction is valid for the zero module and empty schemes. -/
theorem exists_etaleTensorSectionsTransport {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (a : V ⟶ U) :
    ∃ e : Γ((tensorPullback a.left).obj ((tensorPullback U.hom).obj F), ⊤) ≃+
      Γ((tensorPullback V.hom).obj F, ⊤),
      ∀ (m : Γ((tensorPullback U.hom).obj F, ⊤)) (b : Γ(V.left, ⊤)),
        e (b • tensorSectionsUnit a.left ((tensorPullback U.hom).obj F) m) =
          b • etaleTensorSectionsRestriction F a m  := by
  have h := transportForFamily (@tensorPullback) (@tensorSectionsComp) (@tensorSectionsUnit) F a
  rw [← restriction_eq F a] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
