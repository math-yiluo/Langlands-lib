/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Existence part of the affine Hom comparison

The chart functor and its rank-one identification are parameters with equations
fixing them to the standard constructions, so this module does not depend on the
unique-existence theorem it supports. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem extend_balanced {A : Type u} [CommRing A]
    {D : Type (u + 1)} [Category.{u} D] [Preadditive D]
    (T : ModuleCat.{u} A ⥤ D) [T.Additive]
    (S : D ⥤ ModuleCat.{u} A) (adj : T ⊣ S)
    (H : ModuleCat.{u} A) (F : D)
    (α : H → (T.obj (ModuleCat.of A A) ⟶ F))
    (hadd : ∀ x y, α (x + y) = α x + α y)
    (hsmul : ∀ (r : A) x,
      α (r • x) = T.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A r)) ≫ α x) :
    ∃ c : T.obj H ⟶ F, ∀ x : H,
      T.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A H x)) ≫ c = α x := by
  let β (x : H) := adj.homEquiv (ModuleCat.of A A) F (α x)
  let L : H →ₗ[A] S.obj F :=
    { toFun := fun x ↦ (β x).hom 1
      map_add' := by
        intro x y
        dsimp [β]
        rw [hadd, adj.homAddEquiv_add]
        rfl
      map_smul' := by
        intro r x
        dsimp [β]
        rw [hsmul, adj.homEquiv_naturality_left]
        simpa [ModuleCat.hom_comp, LinearMap.toSpanSingleton_apply, β] using
          (β x).hom.map_smul r (1 : A) }
  refine ⟨(adj.homEquiv H F).symm (ModuleCat.ofHom L), fun x ↦ ?_⟩
  apply (adj.homEquiv (ModuleCat.of A A) F).injective
  rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp [ModuleCat.hom_comp, LinearMap.toSpanSingleton_apply, L, β]

private theorem hom_section_add {X : Scheme.{u}} (M N : X.Modules)
    (f g : M ⟶ N) :
    (SheafOfModules.homObj (R := X.toRingedSpace.sheaf) M N).unitHomEquiv.symm
      ((SheafOfModules.homObjSectionsEquiv M N).symm (f + g)) =
    (SheafOfModules.homObj (R := X.toRingedSpace.sheaf) M N).unitHomEquiv.symm
      ((SheafOfModules.homObjSectionsEquiv M N).symm f) +
    (SheafOfModules.homObj (R := X.toRingedSpace.sheaf) M N).unitHomEquiv.symm
      ((SheafOfModules.homObjSectionsEquiv M N).symm g) := by
  suffices h : ∀ V,
      (PresheafOfModules.restrictOver X.sheaf.obj V).map (f + g).val =
        (PresheafOfModules.restrictOver X.sheaf.obj V).map f.val +
        (PresheafOfModules.restrictOver X.sheaf.obj V).map g.val by
    ext V
    simpa [SheafOfModules.unitHomEquiv, PresheafOfModules.unitHomEquiv,
      SheafOfModules.homObjSectionsEquiv, PresheafOfModules.homObjSectionsEquiv,
      Functor.FullyFaithful.homEquiv] using h V.unop
  intro V
  apply PresheafOfModules.hom_ext
  intro W
  rfl

private theorem hom_section_app {X : Scheme.{u}} (M N : X.Modules)
    (h : M ⟶ N) (V : (TopologicalSpace.Opens X)ᵒᵖ) (r : X.sheaf.obj.obj V)
    (W : (Over V.unop)ᵒᵖ) (x : M.val.obj (Opposite.op W.unop.left)) :
    (((SheafOfModules.homObj (R := X.sheaf) M N).unitHomEquiv.symm
      ((SheafOfModules.homObjSectionsEquiv M N).symm h)).val.app V r).app W x =
    X.sheaf.obj.map W.unop.hom.op r • h.val.app (Opposite.op W.unop.left) x := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem tilde_map_smul_app {R : CommRingCat.{u}} (M N : ModuleCat.{u} R)
    (r : R) (h : M ⟶ N) (V : (Spec R).Opens)
    (x : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (Opposite.op V)) :
    (modulesSpecToSheaf.map (tilde.map (r • h))).hom.app (Opposite.op V) x =
      r • (modulesSpecToSheaf.map (tilde.map h)).hom.app (Opposite.op V) x := by
  apply ((tilde.modulesSpecToSheafIso N).app (Opposite.op V)).toLinearEquiv.injective
  simp only [map_smul, tilde.map, Functor.FullyFaithful.map_preimage,
    NatTrans.comp_app, ModuleCat.comp_apply]
  apply Subtype.ext
  funext p
  change StructureSheaf.Localizations.comapFun (r • h.hom) p.1 _ =
    r • StructureSheaf.Localizations.comapFun h.hom p.1 _
  suffices haux : ∀ z, StructureSheaf.Localizations.comapFun (r • h.hom) p.1 z =
      r • StructureSheaf.Localizations.comapFun h.hom p.1 z from haux _
  intro z
  induction z using LocalizedModule.induction_on with
  | h m t =>
    simp only [StructureSheaf.Localizations.comapFun_mk, LinearMap.smul_apply,
      LocalizedModule.smul'_mk]

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_tilde_map_smul_app {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsOpenImmersion f] (M N : ModuleCat.{u} R)
    (r : R) (h : M ⟶ N) (V : X.Opens)
    (x : ((Scheme.Modules.restrictFunctor f).obj (tilde M)).val.obj (Opposite.op V)) :
    ((Scheme.Modules.restrictFunctor f).map (tilde.map (r • h))).val.app (Opposite.op V) x =
      (f.appIso V).hom
        ((Spec R).presheaf.map (f ''ᵁ V).leTop.op ((Scheme.ΓSpecIso R).inv r)) •
      ((Scheme.Modules.restrictFunctor f).map (tilde.map h)).val.app (Opposite.op V) x := by
  have hs := tilde_map_smul_app M N r h (f ''ᵁ V) x
  change (tilde.map (r • h)).val.app (Opposite.op (f ''ᵁ V)) x =
    r • (show Γ(tilde N, f ''ᵁ V) from
      (tilde.map h).val.app (Opposite.op (f ''ᵁ V)) x) at hs
  rw [Scheme.Modules.smul_Spec_def (M := tilde N)] at hs
  change (tilde.map (r • h)).val.app (Opposite.op (f ''ᵁ V)) x =
    (f.appIso V).inv ((f.appIso V).hom
      ((Spec R).presheaf.map (f ''ᵁ V).leTop.op ((Scheme.ΓSpecIso R).inv r))) •
      (tilde.map h).val.app (Opposite.op (f ''ᵁ V)) x
  simpa only [Iso.hom_inv_id_apply] using hs

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_scalar_naturality {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsOpenImmersion f] (r : R) {V Z : X.Opens} (i : V ⟶ Z) :
    X.sheaf.obj.map i.op ((f.appIso Z).hom
      ((Spec R).presheaf.map (f ''ᵁ Z).leTop.op ((Scheme.ΓSpecIso R).inv r))) =
    (f.appIso V).hom
      ((Spec R).presheaf.map (f ''ᵁ V).leTop.op ((Scheme.ΓSpecIso R).inv r)) := by
  have h := f.appIso_hom_naturality i.op
  have hh : (Spec R).presheaf.map (f ''ᵁ Z).leTop.op ≫
      ((f.appIso Z).hom ≫ X.presheaf.map i.op) =
    (Spec R).presheaf.map (f ''ᵁ V).leTop.op ≫ (f.appIso V).hom := by
    rw [← h, ← Category.assoc, ← Functor.map_comp]
    rfl
  exact congrArg (fun k ↦ k ((Scheme.ΓSpecIso R).inv r)) hh

set_option backward.isDefEq.respectTransparency false in
/-- Global linear maps extend to a morphism into the internal Hom sheaf.
Source: Stacks Project, Tag 01I7 (mapping property) and Tag 01HV (4)-(5).
(blueprint: new-affine-hom-generator-extension-existence).

Proof: Substitute the equation fixing the chart functor T. Compose the tilde
adjunction with the restriction adjunction along the affine chart. This composite
is additive since it preserves colimits. Send h to its internal-Hom section,
precomposed with e.hom. This assignment is additive by the section equivalences.
For scalar multiplication, tilde(r*h) sends each localized m/s to r*h(m)/s;
this follows by induction on localized-module fractions. Transport this identity
through the chart's ring isomorphisms. Their naturality shows that the local
scalars restrict compatibly. Linearity of e and commutativity of the local rings
then give alpha(r*h) = T(a |-> a*r) followed by alpha(h). This works for any
linear rank-one isomorphism e, so its additional normalization is not needed.
Apply the adjunction to alpha(h), obtaining a map A -> S(internalHom), and evaluate
it at one. The additive adjunction equivalence and its naturality under
multiplication by r show that these values form an A-linear map from Hom_A(M,N).
Its adjoint is c. Naturality under a |-> a*h proves the generator equation after
precomposition with e.hom; cancellation with e.inv gives the displayed formula.
No finite presentation or quasi-coherence of internal Hom is needed. The same
construction includes the zero ring and zero coefficient modules.
Only existence is asserted here; uniqueness is proved separately by adjunction. -/
theorem exists_affineHom_generator_extension {Y : Scheme.{u}} (U : Y.affineOpens)
    (M N : ModuleCat.{u} Γ(Y, U.1)) :
    ∀ (T : ModuleCat.{u} Γ(Y, U.1) ⥤ U.1.toScheme.Modules)
      (e : T.obj (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) ≅
        SheafOfModules.unit U.1.toScheme.ringCatSheaf),
      T = tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom →
      HEq e ((Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso tildeSelf ≪≫
        Scheme.Modules.restrictUnitIso U.2.isoSpec.hom) →
    ∃ c : T.obj (ModuleCat.of Γ(Y, U.1) (M ⟶ N)) ⟶
        SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf) (T.obj M) (T.obj N),
      ∀ h : M ⟶ N,
        (e.inv ≫ T.map (ModuleCat.ofHom
          (LinearMap.toSpanSingleton Γ(Y, U.1) (ModuleCat.of Γ(Y, U.1) (M ⟶ N)) h))) ≫ c =
          (SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
            (T.obj M) (T.obj N)).unitHomEquiv.symm
              ((SheafOfModules.homObjSectionsEquiv (T.obj M) (T.obj N)).symm (T.map h)) := by
  intro T e hT _
  subst T
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let F := SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
    (T.obj M) (T.obj N)
  let α (h : M ⟶ N) : T.obj (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) ⟶ F :=
    e.hom ≫ F.unitHomEquiv.symm
      ((SheafOfModules.homObjSectionsEquiv (T.obj M) (T.obj N)).symm (T.map h))
  have hLeft : T.IsLeftAdjoint := by
    dsimp [T]
    infer_instance
  have hAdd : T.Additive := by
    have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
    exact Functor.additive_of_preservesBinaryBiproducts T
  have hadd : ∀ h k : M ⟶ N, α (h + k) = α h + α k := by
    intro h k
    simp only [α, F, T.map_add, hom_section_add, Preadditive.comp_add]
  have hsmul : ∀ (r : Γ(Y, U.1)) (h : M ⟶ N),
      α (r • h) =
        T.map (ModuleCat.ofHom (LinearMap.toSpanSingleton Γ(Y, U.1) Γ(Y, U.1) r)) ≫
          α h := by
    intro r h
    let q (Z : U.1.toScheme.Opens) : Γ(U.1.toScheme, Z) :=
      (U.2.isoSpec.hom.appIso Z).hom
        ((Spec Γ(Y, U.1)).presheaf.map (U.2.isoSpec.hom ''ᵁ Z).leTop.op
          ((Scheme.ΓSpecIso Γ(Y, U.1)).inv r))
    have hs (P Q : ModuleCat.{u} Γ(Y, U.1)) (k : P ⟶ Q)
        (Z : U.1.toScheme.Opens) (z : (T.obj P).val.obj (Opposite.op Z)) :
        (T.map (r • k)).val.app (Opposite.op Z) z =
          q Z • (T.map k).val.app (Opposite.op Z) z :=
      restrict_tilde_map_smul_app U.2.isoSpec.hom P Q r k Z z
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    ext x
    change (F.unitHomEquiv.symm
      ((SheafOfModules.homObjSectionsEquiv (T.obj M) (T.obj N)).symm
        (T.map (r • h)))).val.app V (e.hom.val.app V x) =
      (F.unitHomEquiv.symm
        ((SheafOfModules.homObjSectionsEquiv (T.obj M) (T.obj N)).symm
          (T.map h))).val.app V
        (e.hom.val.app V ((T.map (ModuleCat.ofHom
          (LinearMap.toSpanSingleton Γ(Y, U.1) Γ(Y, U.1) r))).val.app V x))
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    ext m
    change U.1.toScheme.sheaf.obj.map W.unop.hom.op (e.hom.val.app V x) •
        (T.map (r • h)).val.app (Opposite.op W.unop.left) m =
      U.1.toScheme.sheaf.obj.map W.unop.hom.op
        (e.hom.val.app V ((T.map (ModuleCat.ofHom
          (LinearMap.toSpanSingleton Γ(Y, U.1) Γ(Y, U.1) r))).val.app V x)) •
        (T.map h).val.app (Opposite.op W.unop.left) m
    rw [hs M N h W.unop.left m]
    have hmul : ModuleCat.ofHom (LinearMap.toSpanSingleton Γ(Y, U.1) Γ(Y, U.1) r) =
        r • 𝟙 (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simp [LinearMap.toSpanSingleton_apply]
    have hx : (T.map (ModuleCat.ofHom
        (LinearMap.toSpanSingleton Γ(Y, U.1) Γ(Y, U.1) r))).val.app V x =
        q V.unop • x := by
      rw [hmul, hs, T.map_id]
      change q V.unop • x = q V.unop • x
      rfl
    rw [hx, (e.hom.val.app V).hom.map_smul]
    change _ = U.1.toScheme.sheaf.obj.map W.unop.hom.op
      (q V.unop * (show Γ(U.1.toScheme, V.unop) from e.hom.val.app V x)) • _
    rw [map_mul, restrict_scalar_naturality U.2.isoSpec.hom r W.unop.hom]
    let a : Γ(U.1.toScheme, W.unop.left) :=
      U.1.toScheme.sheaf.obj.map W.unop.hom.op (e.hom.val.app V x)
    let z : (T.obj N).val.obj (Opposite.op W.unop.left) :=
      (T.map h).val.app (Opposite.op W.unop.left) m
    change a • (q W.unop.left • z) = (q W.unop.left * a) • z
    rw [mul_smul]
    exact smul_comm a (q W.unop.left) z
  obtain ⟨c, hc⟩ := extend_balanced T T.rightAdjoint (Adjunction.ofIsLeftAdjoint T)
    (ModuleCat.of Γ(Y, U.1) (M ⟶ N)) F α hadd hsmul
  refine ⟨c, fun h ↦ ?_⟩
  rw [Category.assoc, hc]
  change e.inv ≫ (e.hom ≫ _) = _
  rw [Iso.inv_hom_id_assoc]

end AlgebraicGeometry
