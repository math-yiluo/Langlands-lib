/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Ordinary pullback coherence for a refined three-step path
Source: Stacks Project, Tags 0095 and 0096. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem refinement_comp_assoc {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (ab : A ⟶ C) (bc : B ⟶ D) (t : A ⟶ D)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (ht : ab ≫ c = t) (ht' : a ≫ bc = t) (M : D.Modules) :
    ((pullbackComp a b ≪≫ pullbackCongr hab).hom.app ((pullback c).obj M)) ≫
      ((pullbackComp ab c ≪≫ pullbackCongr ht).hom.app M) =
    (pullback a).map ((pullbackComp b c ≪≫ pullbackCongr hbc).hom.app M) ≫
      ((pullbackComp a bc ≪≫ pullbackCongr ht').hom.app M) := by
  subst ab bc t
  have h := congrArg (fun n ↦ n.app M) (pseudofunctor_associativity a b c)
  dsimp at h
  simp only [Category.id_comp] at h
  have h' := congrArg (fun k ↦
    (pullback a).map ((pullbackComp b c).hom.app M) ≫
      (pullbackComp a (b ≫ c)).hom.app M ≫ k) h
  simpa [pullbackCongr, Category.assoc, ← Functor.map_comp] using h'

private theorem refinement_comp_square {A B C D E : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ D) (e : D ⟶ C)
    (c : C ⟶ E) (v : D ⟶ E)
    (hp : a ≫ b = d ≫ e) (hi : e ≫ c = v)
    (ht : a ≫ (b ≫ c) = d ≫ v) (M : E.Modules) :
    (pullback a).map ((pullbackComp b c).inv.app M) ≫
      ((pullbackComp a b ≪≫ pullbackCongr hp).hom.app ((pullback c).obj M)) ≫
      (pullbackComp d e).inv.app ((pullback c).obj M) ≫
      (pullback d).map ((pullbackComp e c ≪≫ pullbackCongr hi).hom.app M) =
    ((pullbackComp a (b ≫ c) ≪≫ pullbackCongr ht).hom.app M) ≫
      (pullbackComp d v).inv.app M := by
  have ht₁ : (d ≫ e) ≫ c = d ≫ v := by rw [Category.assoc, hi]
  have h₁ := refinement_comp_assoc a b c (d ≫ e) (b ≫ c) (d ≫ v)
    hp rfl ht₁ ht M
  have h₂ := refinement_comp_assoc d e c (d ≫ e) v (d ≫ v)
    rfl hi ht₁ rfl M
  simp only [pullbackCongr, eqToIso_refl, Iso.trans_hom, Iso.refl_hom,
    NatTrans.comp_app, Category.comp_id, Category.assoc] at h₁ h₂ ⊢
  rw [← cancel_mono ((pullbackComp d v).hom.app M)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← h₂]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [h₁]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Ordinary pullbacks of two refined three-step paths agree.
Source: Stacks Project, Tags 0095 and 0096; ordinary-pullback portion of step 2
of lem-pc-open-cover-tensor-comparison-coherence.
(blueprint: lem-pc-ordinary-pullback-refinement-coherence).
Proof: Expand rhoK and rhoL. Apply pseudofunctor_associativity to reassociate each
three-step path to the pullback of its composite. Naturality of pullbackComp moves
the first comparison through pullback z. The equations Hz, Hd identify the composite
path z then pK then sK with pL then sL; H0 identifies the path z then rK with rL.
The equations HK and HL identify each of these total paths followed by f with the
path through h. Congruence is eqToIso, so its composites depend only on the endpoint
equality, by proof irrelevance. Thus both expanded composites are the same canonical
comparison between the pullbacks of the same scheme map. Cancel inverse composition
comparisons, restore the associators, and evaluate at M. This argument uses no open
cover condition, tensor pullback or adjunction, and applies to empty schemes, zero
modules and identity refinements. -/
theorem ordinary_pullback_refinement_coherence
    {X A B C K L W : Scheme.{u}}
    (f : A ⟶ X) (sK : B ⟶ A) (sL : C ⟶ A)
    (pK : K ⟶ B) (pL : L ⟶ C) (rK : K ⟶ W) (rL : L ⟶ W) (h : W ⟶ X)
    (d : C ⟶ B) (z : L ⟶ K)
    (Hd : d ≫ sK = sL) (Hz : z ≫ pK = pL ≫ d) (H0 : z ≫ rK = rL)
    (HK : (pK ≫ sK) ≫ f = rK ≫ h) (HL : (pL ≫ sL) ≫ f = rL ≫ h)
    (M : X.Modules) :
    let S := pullback f
    let QK := pullback sK
    let QL := pullback sL
    let PK := pullback pK
    let PL := pullback pL
    let RK := pullback rK
    let RL := pullback rL
    let D := pullback d
    let Zf := pullback z
    let rhoK0 : pullback h ⋙ RK ≅ (S ⋙ QK) ⋙ PK :=
      pullbackComp rK h ≪≫ (pullbackCongr HK).symm ≪≫
      (pullbackComp (pK ≫ sK) f).symm ≪≫
      Functor.isoWhiskerLeft S (pullbackComp pK sK).symm ≪≫
      (Functor.associator S QK PK).symm
    let rhoL0 : pullback h ⋙ RL ≅ (S ⋙ QL) ⋙ PL :=
      pullbackComp rL h ≪≫ (pullbackCongr HL).symm ≪≫
      (pullbackComp (pL ≫ sL) f).symm ≪≫
      Functor.isoWhiskerLeft S (pullbackComp pL sL).symm ≪≫
      (Functor.associator S QL PL).symm
    let gamma0 : S ⋙ QL ≅ (S ⋙ QK) ⋙ D := Functor.isoWhiskerLeft S
      ((pullbackCongr Hd).symm ≪≫ (pullbackComp d sK).symm) ≪≫
      (Functor.associator S QK D).symm
    let beta0 : RK ⋙ Zf ≅ RL := pullbackComp z rK ≪≫ pullbackCongr H0
    let delta0 : PK ⋙ Zf ≅ D ⋙ PL :=
      pullbackComp z pK ≪≫ pullbackCongr Hz ≪≫ (pullbackComp pL d).symm
    ∀ (rhoK : pullback h ⋙ RK ≅ (S ⋙ QK) ⋙ PK) (_ : rhoK = rhoK0)
      (rhoL : pullback h ⋙ RL ≅ (S ⋙ QL) ⋙ PL) (_ : rhoL = rhoL0)
      (gamma : S ⋙ QL ≅ (S ⋙ QK) ⋙ D) (_ : gamma = gamma0)
      (beta : RK ⋙ Zf ≅ RL) (_ : beta = beta0)
      (delta : PK ⋙ Zf ≅ D ⋙ PL) (_ : delta = delta0),
    Zf.map (rhoK.hom.app M) ≫ delta.hom.app ((S ⋙ QK).obj M) ≫
      PL.map (gamma.inv.app M) = beta.hom.app ((pullback h).obj M) ≫
        rhoL.hom.app M := by
  dsimp only
  intro rhoK eK rhoL eL gamma eg beta eb delta ed
  subst rhoK rhoL gamma beta delta
  have HT : z ≫ (pK ≫ sK) = pL ≫ sL := by
    rw [← Category.assoc, Hz, Category.assoc, Hd]
  have hfirst := refinement_comp_square z pK pL d sK sL Hz Hd HT
    ((pullback f).obj M)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
    at hfirst
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp, Functor.map_comp, Functor.comp_obj, Category.assoc]
  rw [hfirst]
  have HU : z ≫ (rK ≫ h) = rL ≫ h := by rw [← Category.assoc, H0]
  have hsecond := refinement_comp_assoc z (pK ≫ sK) f (pL ≫ sL)
    (rK ≫ h) (rL ≫ h) HT HK HL HU M
  have hthird := refinement_comp_assoc z rK h rL (rK ≫ h) (rL ≫ h)
    H0 rfl rfl HU M
  simp only [Iso.trans_hom, NatTrans.comp_app, pullbackCongr, eqToIso_refl,
    Iso.refl_hom, Category.comp_id, Category.assoc] at hthird
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
    at hsecond
  rw [← cancel_mono ((pullbackComp pL sL).hom.app ((pullback f).obj M))]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← cancel_mono ((pullbackComp (pL ≫ sL) f ≪≫ pullbackCongr HL).hom.app M)]
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hsecond]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simpa [pullbackCongr, Category.assoc] using hthird.symm

end AlgebraicGeometry.Scheme.Modules
