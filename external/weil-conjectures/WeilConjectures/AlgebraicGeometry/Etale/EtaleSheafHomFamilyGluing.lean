/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-! # Gluing sheaf morphisms on an étale covering family

Source: Stacks Project, Modules on Sites, Lemma 03EM and Sites Lemma 04TQ.
(blueprint: lem-amb-etale-sheaf-hom-family-gluing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Compatible morphisms of restrictions to an étale covering family glue uniquely.
Compatibility is equality on any étale object admitting two lifts to cover members.
Source: Stacks Project, Tags 03EM and 04TQ.
(blueprint: lem-amb-etale-sheaf-hom-family-gluing).

Proof: the presheaf of morphisms on slice sites is a sheaf. Each local morphism gives
its section over the corresponding cover member, by evaluation on lifts. Compatibility
makes these a matching family. Glue at the terminal étale object and evaluate on every
object over it. The sheaf axiom gives a morphism with the prescribed restrictions.
Restrictions jointly reflect isomorphisms and preserve equalizers, so they are jointly
faithful, proving uniqueness. The empty cover is included. -/
theorem existsUnique_etaleSheafHom_of_family
    (B : Type (u + 1)) [CommRing B]
    {X : Scheme.{u}} {I : Type u} {U : I → Scheme.{u}}
    (a : ∀ i, U i ⟶ X) [∀ i, Etale (a i)]
    (ha : ∀ x : X, ∃ (i : I) (y : U i), (a i).base y = x)
    (P Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (ψ : ∀ i, (localizationRestriction (ModuleCat.{u + 1} B) (a i) inferInstance).obj P ⟶
      (localizationRestriction (ModuleCat.{u + 1} B) (a i) inferInstance).obj Q)
    (hψ : ∀ (W : X.Etale) (i j : I)
      (q₁ : W ⟶ Scheme.Etale.mk (a i)) (q₂ : W ⟶ Scheme.Etale.mk (a j)),
      descentComponent (a i) (ψ i) q₁ = descentComponent (a j) (ψ j) q₂) :
    ∃! φ : P ⟶ Q,
      ∀ i, (localizationRestriction (ModuleCat.{u + 1} B) (a i) inferInstance).map φ = ψ i := by
  classical
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let Y : I → X.Etale := fun i ↦ Scheme.Etale.mk (a i)
  let f : ∀ i, Y i ⟶ T := fun i ↦ MorphismProperty.Over.homMk (a i)
  let toT (W : X.Etale) : W ⟶ T := MorphismProperty.Over.homMk W.hom
  have toT_uniq {W : X.Etale} (b : W ⟶ T) : b = toT W :=
    MorphismProperty.Over.Hom.ext ((Category.comp_id _).symm.trans
      (MorphismProperty.Over.w b))
  let H := presheafHom P.obj Q.obj
  have hH : Presieve.IsSheaf X.smallEtaleTopology H :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.IsSheaf.hom _ _ Q.property)
  have hcov : Sieve.generate (Presieve.ofArrows Y f) ∈ X.smallEtaleTopology T := by
    rw [Scheme.mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨i, y, hy⟩ := ha x
    exact ⟨Y i, f i, Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i), y, hy⟩
  let x : ∀ i, H.obj (op (Y i)) := fun i ↦
    { app W := descentComponent (a i) (ψ i) W.unop.hom
      naturality W W' g := by
        have h := descentComponent_naturality (a i) (ψ i) g.unop.left W.unop.hom
        rw [CategoryTheory.Over.w g.unop] at h
        exact h }
  have hx : Presieve.Arrows.Compatible H f x := by
    intro i j W b c _
    exact NatTrans.ext (funext fun Z ↦ hψ _ i j _ _)
  have hsf : (Presieve.ofArrows Y f).IsSheafFor H :=
    (Presieve.isSheafFor_iff_generate _).2 (hH _ hcov)
  obtain ⟨y, hy, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf x hx
  let φ : P ⟶ Q := ⟨{
    app W := y.app (op (CategoryTheory.Over.mk (toT W.unop)))
    naturality W W' g := y.naturality (CategoryTheory.Over.homMk
      (U := CategoryTheory.Over.mk (toT W'.unop))
      (V := CategoryTheory.Over.mk (toT W.unop)) g.unop (toT_uniq _)).op }⟩
  have hφ :
      ∀ i, (localizationRestriction (ModuleCat.{u + 1} B) (a i) inferInstance).map φ = ψ i := by
    intro i
    apply Sheaf.hom_ext
    ext ⟨W⟩ : 2
    let b : (MorphismProperty.Over.map ⊤ (inferInstance : Etale (a i))).obj W ⟶
        Scheme.Etale.mk (a i) := MorphismProperty.Over.homMk W.hom
    have h := congrArg (fun z ↦ z.app (op (CategoryTheory.Over.mk b))) (hy i)
    rw [presheafHom_map_app b (f i) _ (toT_uniq _)] at h
    have hb : (liftEtaleIso (a i) b).hom = 𝟙 _ :=
      MorphismProperty.Over.Hom.ext (by simp)
    have hb' : (liftEtaleIso (a i) b).inv = 𝟙 _ :=
      MorphismProperty.Over.Hom.ext (by simp)
    change _ = descentComponent (a i) (ψ i) b at h
    rw [descentComponent, hb, hb', op_id, op_id] at h
    erw [P.obj.map_id, Q.obj.map_id, Category.id_comp, Category.comp_id] at h
    exact h
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  have hf : JointlyFaithful (fun i ↦ upperStar (ModuleCat.{u + 1} B) (a i)) := by
    apply JointlyReflectIsomorphisms.jointlyFaithful
    constructor
    intro M N z hz
    exact isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} B) a ha z hz
  apply hf.map_injective
  intro i
  rw [← NatIso.naturality_2 (upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} B) (a i) inferInstance) φ',
    ← NatIso.naturality_2 (upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} B) (a i) inferInstance) φ, hφ' i, hφ i]

/-- A glued map has any further local restriction compatible with its covering family.
Source: Stacks Project, Tags 03EM and 04TQ.
(blueprint: lem-amb-etale-sheaf-hom-family-gluing).

Proof: add the further étale object to the covering family and glue again. The old
cover still covers the base, so its uniqueness identifies the new glued map with the
old one. The restriction at the added member is the required equation. This works
also for an empty base or a repeated cover member. -/
theorem etaleSheafHom_restriction_eq_of_compatible
    (B : Type (u + 1)) [CommRing B]
    {X : Scheme.{u}} {I : Type u} {U : I → Scheme.{u}}
    (a : ∀ i, U i ⟶ X) [∀ i, Etale (a i)]
    (ha : ∀ x : X, ∃ (i : I) (y : U i), (a i).base y = x)
    (P Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (ψ : ∀ i, (localizationRestriction (ModuleCat.{u + 1} B) (a i) inferInstance).obj P ⟶
      (localizationRestriction (ModuleCat.{u + 1} B) (a i) inferInstance).obj Q)
    (hψ : ∀ (W : X.Etale) (i j : I)
      (q : W ⟶ Scheme.Etale.mk (a i)) (q' : W ⟶ Scheme.Etale.mk (a j)),
      descentComponent (a i) (ψ i) q = descentComponent (a j) (ψ j) q')
    (φ : P ⟶ Q)
    (hφ : ∀ i, (localizationRestriction (ModuleCat.{u + 1} B) (a i) inferInstance).map φ = ψ i)
    {V : Scheme.{u}} (b : V ⟶ X) [Etale b]
    (θ : (localizationRestriction (ModuleCat.{u + 1} B) b inferInstance).obj P ⟶
      (localizationRestriction (ModuleCat.{u + 1} B) b inferInstance).obj Q)
    (hcross : ∀ (W : X.Etale) (i : I)
      (q : W ⟶ Scheme.Etale.mk (a i)) (q' : W ⟶ Scheme.Etale.mk b),
      descentComponent (a i) (ψ i) q = descentComponent b θ q')
    (hself : ∀ (W : X.Etale) (q q' : W ⟶ Scheme.Etale.mk b),
      descentComponent b θ q = descentComponent b θ q') :
    (localizationRestriction (ModuleCat.{u + 1} B) b inferInstance).map φ = θ := by
  let J : I ⊕ PUnit.{u + 1} → X.Etale :=
    Sum.elim (fun i ↦ Scheme.Etale.mk (a i)) (fun _ ↦ Scheme.Etale.mk b)
  let Ψ : ∀ j : I ⊕ PUnit.{u + 1},
      (localizationRestriction (ModuleCat.{u + 1} B) (J j).hom (J j).prop).obj P ⟶
        (localizationRestriction (ModuleCat.{u + 1} B) (J j).hom (J j).prop).obj Q :=
    fun j ↦ match j with
    | .inl i => ψ i
    | .inr _ => θ
  have hm : ∀ (W : X.Etale) (i j : I ⊕ PUnit.{u + 1})
      (q : W ⟶ Scheme.Etale.mk (J i).hom) (q' : W ⟶ Scheme.Etale.mk (J j).hom),
      descentComponent (J i).hom (Ψ i) q = descentComponent (J j).hom (Ψ j) q' := by
    intro W i j q q'
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hψ W i j q q'
      | inr _ => exact hcross W i q q'
    | inr _ =>
      cases j with
      | inl j => exact (hcross W j q' q).symm
      | inr _ => exact hself W q q'
  obtain ⟨β, hβ, _⟩ := existsUnique_etaleSheafHom_of_family B
    (fun j : I ⊕ PUnit.{u + 1} ↦ (J j).hom)
    (fun x ↦ by obtain ⟨i, y, hy⟩ := ha x; exact ⟨.inl i, y, hy⟩) P Q Ψ hm
  obtain ⟨γ, _, hγ⟩ := existsUnique_etaleSheafHom_of_family B a ha P Q ψ hψ
  have heq : β = φ := (hγ β (fun i ↦ hβ (.inl i))).trans (hγ φ hφ).symm
  have hlast := hβ (.inr PUnit.unit)
  change (localizationRestriction (ModuleCat.{u + 1} B) b inferInstance).map β = θ at hlast
  simpa only [heq] using hlast

/-- A local map over a monomorphism automatically satisfies its self-overlap equation.
Source: uniqueness of lifts through a monomorphism, in étale sheaf descent.
(blueprint: lem-amb-etale-sheaf-hom-family-gluing).

Proof: the two lifts have the same composite to the base. Cancel the monomorphism,
apply extensionality for morphisms over the base, and apply congruence to the component. -/
theorem descentComponent_eq_of_mono (B : Type (u + 1)) [CommRing B]
    {X V : Scheme.{u}} (b : V ⟶ X) [Etale b] [Mono b]
    {P Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (θ : (localizationRestriction (ModuleCat.{u + 1} B) b inferInstance).obj P ⟶
      (localizationRestriction (ModuleCat.{u + 1} B) b inferInstance).obj Q)
    (W : X.Etale) (q q' : W ⟶ Scheme.Etale.mk b) :
    descentComponent b θ q = descentComponent b θ q' := by
  have hq : q = q' := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono b).1
    exact q.w.trans q'.w.symm
  exact congrArg (descentComponent b θ) hq

end AlgebraicGeometry.Etale
