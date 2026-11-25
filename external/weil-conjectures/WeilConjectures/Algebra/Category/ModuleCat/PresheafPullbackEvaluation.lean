/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension

/-! # Evaluation of identity-site presheaf scalar extension

Source: Stacks Project, Sheaves on Spaces, Tag 006R,
lemma-adjointness-tensor-restrict-presheaves; balanced tensor scalar extension.
-/

@[expose] public section
universe u v
open CategoryTheory Opposite
namespace PresheafOfModules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section
variable {C : Type u} [SmallCategory C] {k : Type u} [Ring k]
variable (R : Cᵒᵖ ⥤ RingCat.{u})
variable (φ : (Functor.const Cᵒᵖ).obj (RingCat.of k) ⟶ (𝟭 C).op ⋙ R)
variable (M : PresheafOfModules.{max u v} ((Functor.const Cᵒᵖ).obj (RingCat.of k)))
private abbrev L (U : Cᵒᵖ) := ModuleCat.ringExtendScalars.{u, v} (φ.app U).hom
private abbrev adj (U : Cᵒᵖ) := ModuleCat.ringExtendScalarsAdj.{u, v} (φ.app U).hom
private def eta (U : Cᵒᵖ) (m : M.obj U) : (L R φ U).obj (M.obj U) :=
  (adj R φ U).unit.app (M.obj U) m
private theorem eta_smul (U : Cᵒᵖ) (c : k) (m : M.obj U) :
    eta R φ M U (c • m) = φ.app U c • eta R φ M U m := by
  exact ((adj R φ U).unit.app (M.obj U)).hom.map_smul c m
private def extensionRestriction {U V : Cᵒᵖ} (i : U ⟶ V) :
    (L R φ U).obj (M.obj U) ⟶
      (ModuleCat.restrictScalars (R.map i).hom).obj ((L R φ V).obj (M.obj V)) := by
  let T := (ModuleCat.restrictScalars (R.map i).hom).obj ((L R φ V).obj (M.obj V))
  let h : M.obj U ⟶ (ModuleCat.restrictScalars (φ.app U).hom).obj T :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (φ.app U).hom).obj T)
      { toFun := fun m ↦ eta R φ M V (M.map i m)
        map_add' := by
          intro a b
          change ((adj R φ V).unit.app (M.obj V)).hom ((M.map i).hom (a + b)) = _
          rw [map_add, map_add]
          rfl
        map_smul' := by
          intro c m
          change eta R φ M V (M.map i (c • m)) =
            R.map i (φ.app U c) • eta R φ M V (M.map i m)
          rw [M.map_smul]
          change eta R φ M V (c • M.map i m) = _
          rw [eta_smul]
          congr 1
          exact ConcreteCategory.congr_hom (φ.naturality i) c }
  exact ((adj R φ U).homEquiv _ T).symm h
private theorem extensionRestriction_eta {U V : Cᵒᵖ} (i : U ⟶ V) (m : M.obj U) :
    extensionRestriction R φ M i (eta R φ M U m) = eta R φ M V (M.map i m) := by
  unfold extensionRestriction eta
  have h := ((adj R φ U).homEquiv _ _).apply_symm_apply
    (ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (φ.app U).hom).obj
        ((ModuleCat.restrictScalars (R.map i).hom).obj ((L R φ V).obj (M.obj V))))
      { toFun := fun m ↦ eta R φ M V (M.map i m)
        map_add' := by
          intro a b
          change ((adj R φ V).unit.app (M.obj V)).hom ((M.map i).hom (a + b)) = _
          rw [map_add, map_add]
          rfl
        map_smul' := by
          intro c m
          change eta R φ M V (M.map i (c • m)) =
            R.map i (φ.app U c) • eta R φ M V (M.map i m)
          rw [M.map_smul]
          change eta R φ M V (c • M.map i m) = _
          rw [eta_smul]
          congr 1
          exact ConcreteCategory.congr_hom (φ.naturality i) c })
  rw [Adjunction.homEquiv_unit] at h
  exact ConcreteCategory.congr_hom h m
private theorem ext_eta (U : Cᵒᵖ) {N : ModuleCat.{max u v} (R.obj U)}
    {f g : (L R φ U).obj (M.obj U) ⟶ N}
    (h : ∀ m : M.obj U, f (eta R φ M U m) = g (eta R φ M U m)) : f = g := by
  apply ((adj R φ U).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext m
  exact h m

private def Eobj : PresheafOfModules.{max u v} R where
  obj U := (L R φ U).obj (M.obj U)
  map i := extensionRestriction R φ M i
  map_id U := by
    apply ext_eta R φ M U
    intro m
    rw [extensionRestriction_eta]
    simp only [M.map_id]
    rfl
  map_comp i j := by
    apply ext_eta R φ M _
    intro m
    change extensionRestriction R φ M (i ≫ j) (eta R φ M _ m) =
      extensionRestriction R φ M j (extensionRestriction R φ M i (eta R φ M _ m))
    rw [extensionRestriction_eta, extensionRestriction_eta, extensionRestriction_eta]
    rw [M.map_comp_apply]

private theorem Lmap_eta
    {M N : PresheafOfModules.{max u v} ((Functor.const Cᵒᵖ).obj (RingCat.of k))}
    (f : M ⟶ N) (U : Cᵒᵖ) (m : M.obj U) :
    (L R φ U).map (f.app U) (eta R φ M U m) = eta R φ N U (f.app U m) := by
  exact (ConcreteCategory.congr_hom ((adj R φ U).unit.naturality (f.app U)) m).symm

private def Emap
    {M N : PresheafOfModules.{max u v} ((Functor.const Cᵒᵖ).obj (RingCat.of k))}
    (f : M ⟶ N) : Eobj R φ M ⟶ Eobj R φ N where
  app U := (L R φ U).map (f.app U)
  naturality {U V} i := by
    apply ext_eta R φ M U
    intro m
    change (L R φ V).map (f.app V) (extensionRestriction R φ M i (eta R φ M U m)) =
      extensionRestriction R φ N i ((L R φ U).map (f.app U) (eta R φ M U m))
    rw [extensionRestriction_eta, Lmap_eta, Lmap_eta, extensionRestriction_eta]
    rw [PresheafOfModules.naturality_apply]

private def E : PresheafOfModules.{max u v} ((Functor.const Cᵒᵖ).obj (RingCat.of k)) ⥤
    PresheafOfModules.{max u v} R where
  obj M := Eobj R φ M
  map f := Emap R φ f
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (L R φ U).map_id (M.obj U)
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (L R φ U).map_comp (f.app U) (g.app U)

private theorem transpose_eta (U : Cᵒᵖ) (N : ModuleCat.{max u v} (R.obj U))
    (h : M.obj U ⟶ (ModuleCat.restrictScalars (φ.app U).hom).obj N) (m : M.obj U) :
    ((adj R φ U).homEquiv _ N).symm h (eta R φ M U m) = h m := by
  have H := ((adj R φ U).homEquiv _ N).apply_symm_apply h
  rw [Adjunction.homEquiv_unit] at H
  exact ConcreteCategory.congr_hom H m

private def toRestrict (N : PresheafOfModules.{max u v} R) (f : Eobj R φ M ⟶ N) :
    M ⟶ (PresheafOfModules.pushforward φ).obj N where
  app U := (adj R φ U).homEquiv _ _ (f.app U)
  naturality {U V} i := by
    ext m
    change f.app V (eta R φ M V (M.map i m)) =
      N.map i (f.app U (eta R φ M U m))
    rw [← extensionRestriction_eta R φ M i m]
    exact PresheafOfModules.naturality_apply f i (eta R φ M U m)

private def fromRestrict (N : PresheafOfModules.{max u v} R)
    (h : M ⟶ (PresheafOfModules.pushforward φ).obj N) : Eobj R φ M ⟶ N where
  app U := ((adj R φ U).homEquiv _ _).symm (h.app U)
  naturality {U V} i := by
    apply ext_eta R φ M U
    intro m
    change ((adj R φ V).homEquiv _ _).symm (h.app V)
        (extensionRestriction R φ M i (eta R φ M U m)) =
      N.map i (((adj R φ U).homEquiv _ _).symm (h.app U) (eta R φ M U m))
    rw [extensionRestriction_eta]
    erw [transpose_eta, transpose_eta]
    exact PresheafOfModules.naturality_apply h i m

private def homEquiv (N : PresheafOfModules.{max u v} R) :
    (Eobj R φ M ⟶ N) ≃ (M ⟶ (PresheafOfModules.pushforward φ).obj N) where
  toFun := toRestrict R φ M N
  invFun := fromRestrict R φ M N
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    exact ((adj R φ U).homEquiv _ _).left_inv _
  right_inv h := by
    apply PresheafOfModules.hom_ext
    intro U
    exact ((adj R φ U).homEquiv _ _).right_inv _

private def Eadj : E R φ ⊣ PresheafOfModules.pushforward φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦ homEquiv R φ M N
      homEquiv_naturality_left_symm := by
        intro M N P f g
        apply PresheafOfModules.hom_ext
        intro U
        exact (adj R φ U).homEquiv_naturality_left_symm (f.app U) (g.app U)
      homEquiv_naturality_right := by
        intro M N P f g
        apply PresheafOfModules.hom_ext
        intro U
        exact (adj R φ U).homEquiv_naturality_right (f.app U) (g.app U) }

/-- Identity-site presheaf scalar extension, evaluated on an object, is ordinary
scalar extension of the evaluated module. No field or commutativity hypothesis
is needed.

Source: Stacks Project, Sheaves on Spaces, Tag 006R,
lemma-adjointness-tensor-restrict-presheaves; the balanced scalar-extension
construction of `ModuleCat.ringExtendScalars`.
(blueprint: lem-sc-field-scalar-presheaf-pullback-evaluation).

Proof: write alpha_U for the component of the ring-presheaf map. Construct a module presheaf
whose value on U is the balanced tensor R(U) tensor_k M(U), or equivalently
the left R(U)-module generated by symbols [m], with relations
[m+n]=[m]+[n] and [c*m]=alpha_U(c)*[m]. Restriction along U to V sends
r*[m] to res(r)*[res(m)]. Naturality of alpha makes this respect the relations;
identity and composition follow on the generators. On morphisms send [m] to
[f_U(m)], giving a functor. Its maps into an R-module presheaf N correspond
bijectively to k-linear presheaf maps M to scalar restriction of N: restrict a
map to [m], and extend a map h by r*[m] mapping to r*h_U(m). These operations
are inverse and natural, so this functor is left adjoint to presheaf scalar
restriction. Uniqueness of left adjoints identifies it with Mathlib pullback.
The same presentation at each fixed U is left adjoint to ordinary restriction
along alpha_U, hence identifies with `ModuleCat.ringExtendScalars alpha_U`.
The two comparisons are natural in M because both take the universal generators
to the same generators. Evaluating the first comparison and composing with the
second yields the required natural isomorphism. All presentations and quotients
have carriers in Type(max u v). For zero R(U) the presentations yield zero;
for an empty site there are no objects to evaluate.
Only adjunctions, which determine the functors up to natural isomorphism, are
used to choose data. -/
theorem nonempty_pullbackEvaluationIso
    [(PresheafOfModules.pushforward.{max u v} φ).IsRightAdjoint] (U : Cᵒᵖ) :
    Nonempty (PresheafOfModules.pullback.{max u v} φ ⋙
      PresheafOfModules.evaluation R U ≅
      PresheafOfModules.evaluation ((Functor.const Cᵒᵖ).obj (RingCat.of k)) U ⋙
        ModuleCat.ringExtendScalars.{u, v} (φ.app U).hom) := by
  let e := (Eadj R φ).leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φ)
  exact ⟨(Functor.isoWhiskerRight e (PresheafOfModules.evaluation R U)).symm⟩

end
end PresheafOfModules
