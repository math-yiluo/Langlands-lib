/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # EtaleModuleRingIsoTensor

Source: Stacks Project, Tags 03D3, 03D6, 03D7.
(blueprint: lem-weil-pbc-etale-module-ring-iso-tensor). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev tensorComparisonApp (U : Scheme.{u})
    {R S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}} (c : R ≅ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (e : M ≅ (SheafOfModules.pushforward.{u + 1} (F := 𝟭 U.Etale)
      (S := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (R := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
      ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom).obj N)
    (W : U.Etaleᵒᵖ) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (c.hom.hom.app W).hom).obj (M.val.obj W) ⟶ N.val.obj W :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    (c.hom.hom.app W).hom (X := M.val.obj W) (Y := N.val.obj W)
      (e.hom.val.app W)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorComparisonApp_tmul (U : Scheme.{u})
    {R S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}} (c : R ≅ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (e : M ≅ (SheafOfModules.pushforward.{u + 1} (F := 𝟭 U.Etale)
      (S := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (R := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
      ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom).obj N)
    (W : U.Etaleᵒᵖ) (a : S.obj.obj W) (m : M.val.obj W) :
    (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      (c.hom.hom.app W).hom (X := M.val.obj W) (Y := N.val.obj W)
      (e.hom.val.app W)).hom (a ⊗ₜ[R.obj.obj W, (c.hom.hom.app W).hom] m) =
      a • (show N.val.obj W from e.hom.val.app W m) := by
  let : Module (R.obj.obj W) (S.obj.obj W) :=
    Module.compHom (S.obj.obj W) (c.hom.hom.app W).hom
  let : Module (R.obj.obj W) (N.val.obj W) :=
    Module.compHom (N.val.obj W) (c.hom.hom.app W).hom
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem tensorComparisonApp_isIso (U : Scheme.{u})
    {R S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}} (c : R ≅ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (e : M ≅ (SheafOfModules.pushforward.{u + 1} (F := 𝟭 U.Etale)
      (S := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (R := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
      ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom).obj N)
    (W : U.Etaleᵒᵖ) :
    IsIso (tensorComparisonApp U (R := R) (S := S) c M N e W) := by
  let er := ((sheafToPresheaf U.smallEtaleTopology CommRingCat).mapIso c).app W
  let : (ModuleCat.restrictScalars.{u + 1} (c.hom.hom.app W).hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv er.commRingCatIsoToRingEquiv
  let : IsIso (e.hom.val.app W) :=
    inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ W).map
      ((SheafOfModules.forget _).map e.hom)))
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (c.hom.hom.app W).hom
  have heq : tensorComparisonApp U (R := R) (S := S) c M N e W =
      (adj.homEquiv (M.val.obj W) (N.val.obj W)).symm (e.hom.val.app W) := by
    apply (adj.homEquiv (M.val.obj W) (N.val.obj W)).injective
    rw [Equiv.apply_symm_apply]
    ext m
    erw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
      (R := R.obj.obj W) (S := S.obj.obj W)]
    exact (tensorComparisonApp_tmul U (R := R) (S := S) c M N e W 1 m).trans
      (one_smul _ _)
  rw [heq, Adjunction.homEquiv_counit]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorComparisonPresheaf (U : Scheme.{u})
    {R S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}} (c : R ≅ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (e : M ≅ (SheafOfModules.pushforward.{u + 1} (F := 𝟭 U.Etale)
      (S := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (R := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
      ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom).obj N)
 :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (J := U.smallEtaleTopology) c.hom M ⟶ N.val where
  app W := tensorComparisonApp U (R := R) (S := S) c M N e W
  naturality {X Y} i := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change tensorComparisonApp U (R := R) (S := S) c M N e Y
        (SheafOfModules.changeOfRingsMap c.hom M i
          ((1 : S.obj.obj X) ⊗ₜ[R.obj.obj X, (c.hom.hom.app X).hom] m)) =
      N.val.map i (tensorComparisonApp U (R := R) (S := S) c M N e X
          ((1 : S.obj.obj X) ⊗ₜ[R.obj.obj X, (c.hom.hom.app X).hom] m))
    rw [show SheafOfModules.changeOfRingsMap c.hom M i
        ((1 : S.obj.obj X) ⊗ₜ[R.obj.obj X, (c.hom.hom.app X).hom] m) =
          S.obj.map i 1 ⊗ₜ[R.obj.obj Y, (c.hom.hom.app Y).hom]
            (show M.val.obj Y from M.val.map i m) from
      Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap c.hom M i) 1 m]
    rw [tensorComparisonApp_tmul, tensorComparisonApp_tmul]
    simp only [map_one, one_smul]
    exact PresheafOfModules.naturality_apply e.hom.val i m

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorComparisonPresheafIso (U : Scheme.{u})
    {R S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}} (c : R ≅ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (e : M ≅ (SheafOfModules.pushforward.{u + 1} (F := 𝟭 U.Etale)
      (S := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (R := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
      ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom).obj N)
 :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (J := U.smallEtaleTopology) c.hom M ≅ N.val := by
  refine PresheafOfModules.isoMk (fun W ↦ ?_) ?_
  · have := tensorComparisonApp_isIso U (R := R) (S := S) c M N e W
    exact asIso (tensorComparisonApp U (R := R) (S := S) c M N e W)
  · intro X Y i
    exact (tensorComparisonPresheaf U (R := R) (S := S) c M N e).naturality i

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorComparisonSheafIso (U : Scheme.{u})
    {R S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}} (c : R ≅ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (e : M ≅ (SheafOfModules.pushforward.{u + 1} (F := 𝟭 U.Etale)
      (S := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (R := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
      ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom).obj N)
 :
    SheafOfModules.changeOfRings.{u, u + 1, u + 1}
      (J := U.smallEtaleTopology) c.hom M ≅ N :=
  (PresheafOfModules.sheafification (𝟙 _)).mapIso
    (tensorComparisonPresheafIso U (R := R) (S := S) c M N e) ≪≫
      asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app N)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorComparisonSheafIso_unit (U : Scheme.{u})
    {R S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}} (c : R ≅ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (e : M ≅ (SheafOfModules.pushforward.{u + 1} (F := 𝟭 U.Etale)
      (S := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (R := (sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
      ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom).obj N)
 (W : U.Etaleᵒᵖ)
    (x : (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (J := U.smallEtaleTopology) c.hom M).obj W) :
    (tensorComparisonSheafIso U (R := R) (S := S) c M N e).hom.val.app W
      ((toSheafify U.smallEtaleTopology
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (J := U.smallEtaleTopology) c.hom M).presheaf).app W x) =
      tensorComparisonApp U (R := R) (S := S) c M N e W x := by
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
    (J := U.smallEtaleTopology) c.hom M
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)
  let p := tensorComparisonPresheafIso U (R := R) (S := S) c M N e
  have h := adj.homEquiv_naturality_left p.hom (adj.counit.app N)
  have hc : adj.homEquiv N.val N (adj.counit.app N) = 𝟙 _ := by
    have h := (adj.homEquiv _ N).apply_symm_apply (𝟙 _)
    rw [adj.homEquiv_symm_id] at h
    exact h
  dsimp only [Functor.id_obj] at h
  erw [hc, Category.comp_id] at h
  have h' := congrArg (fun q ↦ (q.app W).hom x) h
  exact h'

set_option backward.isDefEq.respectTransparency false in
/-- Identify extension along a ring isomorphism using a restriction comparison.
Source: Stacks Project, Definition 03D6 and Lemma 03D7; the tensor-restriction
adjunction in Tag 03CZ, specialized to an isomorphism.

Proof: at W send a pure tensor a tensor m to t.inv(G)(c.inv(a) times m).
The scalar-linearity of t.inv and the inverse-ring identities prove that this map
is RU(W)-linear and balanced over Lr(RV)(W). The tensor universal property extends
it to all tensors. Its inverse sends n to 1 tensor t.hom(G)(n). The composite on
n is n by the inverse comparison equation and the unit action. The composite on
a tensor m is itself: use c.hom(c.inv(a)) = a and the balancing relation to move
c.inv(a) from m onto the first factor. Pure tensors generate the tensor product.
Naturality of c and t proves compatibility with restriction maps. Consequently
the section maps give inverse presheaf morphisms to the underlying presheaf of
LM(G). Sheafification, whose unit is invertible on that sheaf, produces d(G) and
preserves the pure-tensor formula. For a module map G to H, the two composites
agree on pure tensors by naturality of t and linearity of L0.map; sheafification
then proves the displayed naturality of d.
(blueprint: lem-weil-pbc-etale-module-ring-iso-tensor). -/
theorem etaleModuleRingIsoTensor (U V : Scheme.{u}) (f : U ⟶ V)
    (RV : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    (RU : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
    (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤ Sheaf U.smallEtaleTopology
      CommRingCat.{u + 1})
    (c : Lr.obj RV ≅ RU)
    (L0 : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
      1} RingCat.{u + 1})).obj RV) ⥤ SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV)))
    (LM : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
        1} RingCat.{u + 1})).obj RV) ⥤ SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU))
    (t : LM ⋙ SheafOfModules.pushforward (F := 𝟭 U.Etale) ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom ≅ L0) :
    (∃ (d : ∀ G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RV),
        SheafOfModules.changeOfRings.{u, u + 1, u + 1} (J := U.smallEtaleTopology) c.hom (L0.obj
          G) ≅ LM.obj G),
      (∀ (G H : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u
        + 1} RingCat.{u + 1})).obj RV)) (h : G ⟶ H),
        SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} (J := U.smallEtaleTopology) c.hom
          (L0.obj G) (L0.map h) ≫ (d H).hom =
          (d G).hom ≫ LM.map h) ∧
      (∀ (G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
        1} RingCat.{u + 1})).obj RV)) (W : U.Etaleᵒᵖ)
        (a : RU.obj.obj W) (m : (L0.obj G).val.obj W),
        (d G).hom.val.app W
          ((toSheafify U.smallEtaleTopology
            (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (J := U.smallEtaleTopology)
              c.hom (L0.obj G)).presheaf).app W
              (a ⊗ₜ[(Lr.obj RV).obj.obj W, (c.hom.hom.app W).hom] m)) =
          (t.inv.app G).val.app W ((c.inv.hom.app W a) • m))) := by
  classical
  have _ := f
  let d := fun G ↦ tensorComparisonSheafIso U (R := Lr.obj RV) (S := RU)
    c (L0.obj G) (LM.obj G) (t.app G).symm
  refine ⟨d, ?_, ?_⟩
  · intro G H h
    let F := PresheafOfModules.sheafification.{u + 1}
      (𝟙 ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU).obj)
    let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU).obj)
    let pG := tensorComparisonPresheafIso U (R := Lr.obj RV) (S := RU)
      c (L0.obj G) (LM.obj G) (t.app G).symm
    let pH := tensorComparisonPresheafIso U (R := Lr.obj RV) (S := RU)
      c (L0.obj H) (LM.obj H) (t.app H).symm
    let ψ : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (J := U.smallEtaleTopology) c.hom (L0.obj G) ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (J := U.smallEtaleTopology) c.hom (L0.obj H) :=
      { app := fun W ↦ (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.hom.app W).hom).map
          ((L0.map h).val.app W)
        naturality := SheafOfModules.changeOfRingsHom_naturality c.hom (L0.obj G)
          (L0.map h) }
    have hp : ψ ≫ pH.hom = pG.hom ≫ (LM.map h).val := by
      apply PresheafOfModules.hom_ext
      intro W
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      change tensorComparisonApp U (R := Lr.obj RV) (S := RU)
          c (L0.obj H) (LM.obj H) (t.app H).symm W
            ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.hom.app W).hom).map
              ((L0.map h).val.app W)
                ((1 : RU.obj.obj W) ⊗ₜ[(Lr.obj RV).obj.obj W,
                  (c.hom.hom.app W).hom] m)) =
        (LM.map h).val.app W (tensorComparisonApp U (R := Lr.obj RV) (S := RU)
          c (L0.obj G) (LM.obj G) (t.app G).symm W
            ((1 : RU.obj.obj W) ⊗ₜ[(Lr.obj RV).obj.obj W,
              (c.hom.hom.app W).hom] m))
      have hx := ModuleCat.ExtendScalars.map_tmul
        (R := (Lr.obj RV).obj.obj W) (S := RU.obj.obj W)
        (c.hom.hom.app W).hom ((L0.map h).val.app W) (1 : RU.obj.obj W) m
      rw [hx]
      rw [tensorComparisonApp_tmul U (R := Lr.obj RV) (S := RU),
        tensorComparisonApp_tmul U (R := Lr.obj RV) (S := RU)]
      simp only [one_smul]
      exact ConcreteCategory.congr_hom
        (congrArg (fun q ↦ q.val.app W) (t.inv.naturality h)) m
    change F.map ψ ≫ F.map pH.hom ≫ adj.counit.app (LM.obj H) =
      F.map pG.hom ≫ adj.counit.app (LM.obj G) ≫ LM.map h
    have hn := adj.counit_naturality (LM.map h)
    change F.map (LM.map h).val ≫ adj.counit.app (LM.obj H) =
      adj.counit.app (LM.obj G) ≫ LM.map h at hn
    rw [← hn]
    change F.map ψ ≫ F.map pH.hom ≫ adj.counit.app (LM.obj H) =
      F.map pG.hom ≫ F.map (LM.map h).val ≫ adj.counit.app (LM.obj H)
    rw [← F.map_comp_assoc, hp, F.map_comp_assoc]
  · intro G W a m
    rw [tensorComparisonSheafIso_unit]
    rw [tensorComparisonApp_tmul]
    have hc : c.hom.hom.app W (c.inv.hom.app W a) = a :=
      ConcreteCategory.congr_hom (congrArg (fun q ↦ q.hom.app W) c.inv_hom_id) a
    have hs := (t.inv.app G).val.app W |>.hom.map_smul (c.inv.hom.app W a) m
    change (t.inv.app G).val.app W ((c.inv.hom.app W a) • m) =
      c.hom.hom.app W (c.inv.hom.app W a) •
        (show (LM.obj G).val.obj W from (t.inv.app G).val.app W m) at hs
    rw [hc] at hs
    exact hs.symm

end AlgebraicGeometry
