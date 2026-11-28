import Langlands.MathlibBase
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy
import WeilConjectures.SixFunctors.ProEtale.Adic.StalkIhomDual
import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseTensor
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorDualToIhom
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GermMonoidal
import WeilConjectures.WeilSheaf.Dual

/-!
# Stalks of tensor products of lisse sheaves

For `ℓ`-adic sheaves `G` and `H` on a scheme `Z` and a point `s : Spec K ⟶ Z` with values in a
field, the lax monoidal stalk functor `Φ = Γ(Spec K, s^* -)` and the quotient map
`G ⊗ H ⟶ G ⊗_{ℚ̄_ℓ} H` give the comparison `Φ G ⊗ Φ H ⟶ Φ (G ⊗_{ℚ̄_ℓ} H)`
(`AlgebraicGeometry.ProEtale.tensorStalkMap`), natural in both sheaves.

`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.tensorLeft` proves lisseness of the tensor product
of two lisse sheaves by the isomorphism `G ⊗ ℚ̄_ℓⁿ ≅ Gⁿ` on a cover trivialising `H`.
For `H` lisse and `K` algebraically closed, `AlgebraicGeometry.ProEtale.isIso_tensorStalkMap`
shows the comparison is an isomorphism by pulling back along `s` and using additivity in `H`
and the comparison for the constant sheaf.
`AlgebraicGeometry.ProEtale.evaluationPairing_unit` expresses the comparison as the evaluation
pairing of the unit `G ⟶ 𝓗om(H, G ⊗ H)` of the tensor–hom adjunction. Preservation of evaluation
pairings gives compatibility with monodromy transport
(`AlgebraicGeometry.ProEtale.LisseMonodromy.mono_tensorStalkMap`).
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

section StalkMap

variable {K : Type u} [Field K] {Z : Scheme.{u}}

/-- The comparison `Φ G ⊗ Φ H ⟶ Φ (G ⊗_{ℚ̄_ℓ} H)` of the stalks at `s : Spec K ⟶ Z`: the tensor
comparison of the lax monoidal stalk functor followed by the stalk of the quotient map
`G ⊗ H ⟶ G ⊗_{ℚ̄_ℓ} H`. -/
noncomputable def tensorStalkMap (s : Spec (.of K) ⟶ Z) (G H : AdicSheaf l Z) :
    (stalkFunctor l s).obj G.X ⊗ (stalkFunctor l s).obj H.X ⟶
      (stalkFunctor l s).obj ((Mod.tensorLeft H).obj G).X :=
  μ (stalkFunctor l s) G.X H.X ≫ (stalkFunctor l s).map (Mod.tensorπ G H)

lemma tensorStalkMap_tmul (s : Spec (.of K) ⟶ Z) (G H : AdicSheaf l Z)
    (g : (stalkFunctor l s).obj G.X) (h : (stalkFunctor l s).obj H.X) :
    (tensorStalkMap s G H).hom (g ⊗ₜ h) =
      ((stalkFunctor l s).map (Mod.tensorπ G H)).hom
        ((μ (stalkFunctor l s) G.X H.X).hom (g ⊗ₜ h)) :=
  rfl

/-- The comparison is natural in both sheaves. -/
@[reassoc]
lemma tensorStalkMap_naturality (s : Spec (.of K) ⟶ Z) {G G' H H' : AdicSheaf l Z}
    (f : G ⟶ G') (g : H ⟶ H') :
    ((stalkFunctor l s).map f.hom ⊗ₘ (stalkFunctor l s).map g.hom) ≫ tensorStalkMap s G' H' =
      tensorStalkMap s G H ≫
        (stalkFunctor l s).map ((Mod.tensorLeft H).map f ≫ (Mod.tensorLeftMap g).app G').hom := by
  simp only [tensorStalkMap, Category.assoc]
  rw [μ_natural_assoc, ← Functor.map_comp, ← Functor.map_comp, Mod.comp_hom',
    Mod.tensorπ_map_assoc, Mod.tensorπ_tensorLeftMap, MonoidalCategory.tensorHom_def,
    Category.assoc]

/-- The comparison is natural in the second sheaf. -/
@[reassoc]
lemma tensorStalkMap_naturality_right (s : Spec (.of K) ⟶ Z) (G : AdicSheaf l Z)
    {H H' : AdicSheaf l Z} (g : H ⟶ H') :
    ((stalkFunctor l s).obj G.X ◁ (stalkFunctor l s).map g.hom) ≫ tensorStalkMap s G H' =
      tensorStalkMap s G H ≫ (stalkFunctor l s).map ((Mod.tensorLeftMap g).app G).hom := by
  simp only [tensorStalkMap, Category.assoc]
  rw [μ_natural_right_assoc, ← Functor.map_comp, ← Functor.map_comp,
    Mod.tensorπ_tensorLeftMap]

/-- **The comparison is an evaluation pairing.** The pairing of the stalk of the unit
`G ⟶ 𝓗om(H, G ⊗_{ℚ̄_ℓ} H)` of the tensor–hom adjunction with the stalk of `H` is the
comparison `Φ G ⊗ Φ H ⟶ Φ (G ⊗_{ℚ̄_ℓ} H)`, by the triangle identity. -/
lemma evaluationPairing_unit (s : Spec (.of K) ⟶ Z) (G H : AdicSheaf l Z)
    (g : (stalkFunctor l s).obj G.X) (h : (stalkFunctor l s).obj H.X) :
    Mod.evaluationPairing (stalkFunctor l s) H ((Mod.tensorLeft H).obj G)
        (((stalkFunctor l s).map ((Mod.ihomAdjunction H).unit.app G).hom).hom g) h =
      (tensorStalkMap s G H).hom (g ⊗ₜ h) := by
  rw [Mod.evaluationPairing_apply]
  have h₁ : (μ (stalkFunctor l s) ((Mod.ihom H).obj ((Mod.tensorLeft H).obj G)).X H.X).hom
      (((stalkFunctor l s).map ((Mod.ihomAdjunction H).unit.app G).hom).hom g ⊗ₜ h) =
      ((stalkFunctor l s).map (((Mod.ihomAdjunction H).unit.app G).hom ▷ H.X)).hom
        ((μ (stalkFunctor l s) G.X H.X).hom (g ⊗ₜ h)) :=
    congrArg (fun m => m.hom (g ⊗ₜ h))
      (μ_natural_left (stalkFunctor l s) ((Mod.ihomAdjunction H).unit.app G).hom H.X)
  rw [h₁, ← ModuleCat.comp_apply, ← Functor.map_comp]
  have key : ((Mod.ihomAdjunction H).unit.app G).hom ▷ H.X ≫
      Mod.evaluation H ((Mod.tensorLeft H).obj G) = Mod.tensorπ G H := by
    have e₁ := Mod.tensorπ_map_assoc H ((Mod.ihomAdjunction H).unit.app G)
      ((Mod.ihomAdjunction H).counit.app ((Mod.tensorLeft H).obj G)).hom
    rw [Mod.evaluation]
    refine e₁.symm.trans ?_
    rw [← Mod.comp_hom']
    erw [(Mod.ihomAdjunction H).left_triangle_components, Mod.id_hom', Category.comp_id]
    rfl
  rw [key]
  rfl

end StalkMap

section Regular

variable {K : Type u} [Field K] {Z : Scheme.{u}}

/-- For the constant sheaf `ℚ̄_ℓ`, the comparison is an isomorphism: followed by
`G ⊗_{ℚ̄_ℓ} ℚ̄_ℓ ≅ G` it is the action of the stalk of `ℚ̄_ℓ` on the stalk of `G`, and the stalk of
`ℚ̄_ℓ` is `ℚ̄_ℓ`, generated by the unit section, which acts as the identity. -/
theorem isIso_tensorStalkMap_unit (s : Spec (.of K) ⟶ Z) (G : AdicSheaf l Z) :
    IsIso (tensorStalkMap s G (AdicSheaf.unit l Z)) := by
  let r : (stalkFunctor l s).obj ((Mod.tensorLeft (AdicSheaf.unit l Z)).obj G).X ⟶
      (stalkFunctor l s).obj G.X :=
    (stalkFunctor l s).map (Mod.tensorLeftRegularHom.app G).hom
  have hr : IsIso r := by
    have : IsIso (Mod.tensorLeftRegularHom.app G) := inferInstance
    have : IsIso (Mod.tensorLeftRegularHom.app G).hom :=
      inferInstanceAs (IsIso ((Mod.forget _).map (Mod.tensorLeftRegularHom.app G)))
    exact Functor.map_isIso _ _
  have h : Mod.tensorπ G (AdicSheaf.unit l Z) ≫
      ((Mod.tensorLeftRegularHom.app G).hom : _ ⟶ G.X) =
        (β_ G.X (adicConstantSheaf l Z)).hom ≫ Mod.act G.X :=
    congrArg Mod.Hom.hom (Mod.tensorLeftπ_tensorLeftRegularHom_app G)
  have h' : (stalkFunctor l s).map (Mod.tensorπ G (AdicSheaf.unit l Z)) ≫ r =
      (stalkFunctor l s).map (β_ G.X (adicConstantSheaf l Z)).hom ≫
        (stalkFunctor l s).map (Mod.act G.X) := by
    simp only [r]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (stalkFunctor l s).map h
  have hreg : ∀ x, r.hom (((stalkFunctor l s).map (Mod.tensorπ G (AdicSheaf.unit l Z))).hom x) =
      ((stalkFunctor l s).map (Mod.act G.X)).hom
        (((stalkFunctor l s).map (β_ G.X (adicConstantSheaf l Z)).hom).hom x) := fun x =>
    congrArg (fun f => f.hom x) h'
  have hbr : ∀ a b, ((stalkFunctor l s).map (β_ G.X (adicConstantSheaf l Z)).hom).hom
      ((μ (stalkFunctor l s) G.X (adicConstantSheaf l Z)).hom (a ⊗ₜ b)) =
        (μ (stalkFunctor l s) (adicConstantSheaf l Z) G.X).hom (b ⊗ₜ a) := fun a b =>
    congrArg (fun f => f.hom (a ⊗ₜ b)) (μ_comp_map_braiding_upperStar_comp_Γ s G.X
      (adicConstantSheaf l Z))
  have key : ((stalkFunctor l s).obj G.X ◁ unitSection l s) ≫
      (tensorStalkMap s G (AdicSheaf.unit l Z) ≫ r) = (ρ_ _).hom := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m c => ?_
    change r.hom (((stalkFunctor l s).map (Mod.tensorπ G (AdicSheaf.unit l Z))).hom
      ((μ (stalkFunctor l s) G.X (adicConstantSheaf l Z)).hom (m ⊗ₜ (unitSection l s).hom c))) =
        c • m
    erw [hreg, hbr]
    have hc : (unitSection l s).hom c =
        c • (unitSection l s).hom (1 : ULift.{u + 1} (PadicAlgCl l)) := by
      rw [← map_smul]
      congr 1
      exact (mul_one c).symm
    rw [hc, ← TensorProduct.smul_tmul', map_smul, map_smul, stalkFunctor_act_unitSection]
  have : IsIso ((stalkFunctor l s).obj G.X ◁ unitSection l s) := inferInstance
  have : IsIso (((stalkFunctor l s).obj G.X ◁ unitSection l s) ≫
      (tensorStalkMap s G (AdicSheaf.unit l Z) ≫ r)) := by
    rw [key]
    infer_instance
  have : IsIso (tensorStalkMap s G (AdicSheaf.unit l Z) ≫ r) :=
    IsIso.of_isIso_comp_left ((stalkFunctor l s).obj G.X ◁ unitSection l s) _
  exact IsIso.of_isIso_comp_right _ r

end Regular

section Additivity

variable {K : Type u} [Field K] {Z : Scheme.{u}}

lemma isIso_stalkFunctor_map_tensorLeftMap_app (s : Spec (.of K) ⟶ Z) (G : AdicSheaf l Z)
    {H H' : AdicSheaf l Z} (e : H ≅ H') :
    IsIso ((stalkFunctor l s).map ((Mod.tensorLeftMap e.hom).app G).hom) := by
  have : IsIso ((Mod.tensorLeftMap e.hom).app G) :=
    inferInstanceAs (IsIso ((Mod.tensorLeftMapIso e).app G).hom)
  have : IsIso ((Mod.tensorLeftMap e.hom).app G).hom :=
    inferInstanceAs (IsIso ((Mod.forget _).map ((Mod.tensorLeftMap e.hom).app G)))
  exact Functor.map_isIso _ _

/-- The comparison for `H` is an isomorphism if it is one for a sheaf isomorphic to `H`. -/
lemma isIso_tensorStalkMap_of_iso (s : Spec (.of K) ⟶ Z) (G : AdicSheaf l Z)
    {H H' : AdicSheaf l Z} (e : H ≅ H') (h : IsIso (tensorStalkMap s G H')) :
    IsIso (tensorStalkMap s G H) := by
  have := isIso_stalkFunctor_map_tensorLeftMap_app s G e
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((Mod.forget _).map e.hom))
  have : IsIso ((stalkFunctor l s).obj G.X ◁ (stalkFunctor l s).map e.hom.hom) := inferInstance
  have : IsIso (tensorStalkMap s G H ≫
      (stalkFunctor l s).map ((Mod.tensorLeftMap e.hom).app G).hom) := by
    rw [← tensorStalkMap_naturality_right]
    infer_instance
  exact IsIso.of_isIso_comp_right (tensorStalkMap s G H)
    ((stalkFunctor l s).map ((Mod.tensorLeftMap e.hom).app G).hom)

/-- The comparison is additive in the second sheaf: it is an isomorphism for a finite direct sum
if it is one for each summand. -/
lemma isIso_tensorStalkMap_biproduct (s : Spec (.of K) ⟶ Z) (G : AdicSheaf l Z) {n : ℕ}
    (H : Fin n → AdicSheaf l Z) (h : ∀ i, IsIso (tensorStalkMap s G (H i))) :
    IsIso (tensorStalkMap s G (⨁ H)) := by
  let F : AdicSheaf l Z ⥤ WeilCoefficients.{u} l := Mod.forget _ ⋙ stalkFunctor l s
  let Tπ : ∀ i, F.obj ((Mod.tensorLeft (⨁ H)).obj G) ⟶ F.obj ((Mod.tensorLeft (H i)).obj G) :=
    fun i => F.map ((Mod.tensorLeftMap (biproduct.π H i)).app G)
  let Tι : ∀ i, F.obj ((Mod.tensorLeft (H i)).obj G) ⟶ F.obj ((Mod.tensorLeft (⨁ H)).obj G) :=
    fun i => F.map ((Mod.tensorLeftMap (biproduct.ι H i)).app G)
  let Sπ : ∀ i, (stalkFunctor l s).obj G.X ⊗ F.obj (⨁ H) ⟶
      (stalkFunctor l s).obj G.X ⊗ F.obj (H i) := fun i =>
    (stalkFunctor l s).obj G.X ◁ F.map (biproduct.π H i)
  let Sι : ∀ i, (stalkFunctor l s).obj G.X ⊗ F.obj (H i) ⟶
      (stalkFunctor l s).obj G.X ⊗ F.obj (⨁ H) := fun i =>
    (stalkFunctor l s).obj G.X ◁ F.map (biproduct.ι H i)
  let T : ∀ i, (stalkFunctor l s).obj G.X ⊗ F.obj (H i) ⟶ F.obj ((Mod.tensorLeft (H i)).obj G) :=
    fun i => tensorStalkMap s G (H i)
  let TB : (stalkFunctor l s).obj G.X ⊗ F.obj (⨁ H) ⟶ F.obj ((Mod.tensorLeft (⨁ H)).obj G) :=
    tensorStalkMap s G (⨁ H)
  have hTi : ∀ i, IsIso (T i) := h
  have nπ : ∀ i, TB ≫ Tπ i = Sπ i ≫ T i := fun i =>
    (tensorStalkMap_naturality_right s G (biproduct.π H i)).symm
  have nι : ∀ i, Sι i ≫ TB = T i ≫ Tι i := fun i =>
    tensorStalkMap_naturality_right s G (biproduct.ι H i)
  have hS : ∑ i, Sπ i ≫ Sι i = 𝟙 _ := by
    have e : ∀ i, Sπ i ≫ Sι i =
        (stalkFunctor l s).obj G.X ◁ F.map (biproduct.π H i ≫ biproduct.ι H i) := fun i => by
      simp only [Sπ, Sι, F.map_comp, MonoidalCategory.whiskerLeft_comp]
    rw [Finset.sum_congr rfl fun i _ => e i, ← whiskerLeft_sum, ← F.map_sum, biproduct.total,
      F.map_id, MonoidalCategory.whiskerLeft_id]
  have hT : ∑ i, Tπ i ≫ Tι i = 𝟙 _ := by
    have e : ∀ i, Tπ i ≫ Tι i =
        F.map ((Mod.tensorLeftMap (biproduct.π H i ≫ biproduct.ι H i)).app G) := fun i => by
      simp only [Tπ, Tι, ← F.map_comp, Mod.tensorLeftMap_comp, NatTrans.comp_app]
    rw [Finset.sum_congr rfl fun i _ => e i, ← F.map_sum, ← NatTrans.app_sum]
    have : ∑ i, Mod.tensorLeftMap (biproduct.π H i ≫ biproduct.ι H i) =
        Mod.tensorLeftMapAddHom (⨁ H) (⨁ H) (∑ i, biproduct.π H i ≫ biproduct.ι H i) := by
      rw [map_sum]
      rfl
    rw [this, biproduct.total]
    change F.map ((Mod.tensorLeftMap (𝟙 (⨁ H))).app G) = 𝟙 _
    rw [Mod.tensorLeftMap_id]
    exact F.map_id _
  change IsIso TB
  refine ⟨⟨∑ i : Fin n, Tπ i ≫ inv (T i) ≫ Sι i, ?_, ?_⟩⟩
  · rw [Preadditive.comp_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hS
    rw [reassoc_of% nπ i, IsIso.hom_inv_id_assoc]
  · rw [Preadditive.sum_comp]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hT
    rw [Category.assoc, Category.assoc, nι i, IsIso.inv_hom_id_assoc]

end Additivity

section Pullback

variable {K : Type u} [Field K] {Z V : Scheme.{u}}

/-- **Compatibility with pullback.** The comparison at `t ≫ f` for `G` and `H` is an isomorphism
exactly when the comparison at `t` for `f^* G` and `f^* H` is one: the stalk functor at `t ≫ f`
is the stalk functor at `t` after `f^*`, as lax monoidal functors, and `f^*` commutes with the
tensor product of modules compatibly with the quotient maps. -/
lemma isIso_tensorStalkMap_comp_iff (f : V ⟶ Z) (t : Spec (.of K) ⟶ V) (G H : AdicSheaf l Z) :
    IsIso (tensorStalkMap (t ≫ f) G H) ↔
      IsIso (tensorStalkMap t ((f)^*ᵃ[l].obj G) ((f)^*ᵃ[l].obj H)) := by
  let τ : stalkFunctor l (t ≫ f) ≅ (f)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l t :=
    Functor.isoWhiskerRight (upperStarComp _ t f) _ ≪≫ Functor.associator _ _ _
  have : NatTrans.IsMonoidal τ.hom := by
    dsimp only [τ, Iso.trans_hom, Functor.isoWhiskerRight_hom]
    infer_instance
  let T' : ((f)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l t).obj G.X ⊗
      ((f)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l t).obj H.X ⟶
      (stalkFunctor l t).obj ((Mod.tensorLeft ((f)^*ᵃ[l].obj H)).obj ((f)^*ᵃ[l].obj G)).X :=
    tensorStalkMap t ((f)^*ᵃ[l].obj G) ((f)^*ᵃ[l].obj H)
  let e := (stalkFunctor l t).mapIso
    ((Mod.forget (adicConstantSheaf l V)).mapIso ((adicUpperStarTensorLeftIso l f H).app G))
  let c : ((f)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l t).obj ((Mod.tensorLeft H).obj G).X ⟶
      (stalkFunctor l t).obj ((Mod.tensorLeft ((f)^*ᵃ[l].obj H)).obj ((f)^*ᵃ[l].obj G)).X :=
    e.hom
  have hc : IsIso c := Iso.isIso_hom e
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (f)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l f)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (f)^*ᵃ[l])
  have : ∀ X Y : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l),
      IsIso (μ (f)^*[WeilCoefficients.{u} l] X Y) := fun X Y => inferInstance
  have hπ : (f)^*[WeilCoefficients.{u} l].map (Mod.tensorπ G H) ≫
      ((adicUpperStarTensorLeftIso l f H).hom.app G).hom =
        inv (μ (f)^*[WeilCoefficients.{u} l] G.X H.X) ≫
          Mod.tensorπ ((f)^*ᵃ[l].obj G) ((f)^*ᵃ[l].obj H) :=
    Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicUpperStarRingHom l f) _ G H
  have h₃ : μ (f)^*[WeilCoefficients.{u} l] G.X H.X ≫
      (f)^*[WeilCoefficients.{u} l].map (Mod.tensorπ G H) ≫
        ((adicUpperStarTensorLeftIso l f H).hom.app G).hom =
      Mod.tensorπ ((f)^*ᵃ[l].obj G) ((f)^*ᵃ[l].obj H) := by
    erw [hπ, IsIso.hom_inv_id_assoc]
  have h₄ := congrArg (stalkFunctor l t).map h₃
  erw [Functor.map_comp, Functor.map_comp] at h₄
  have h₂ : μ ((f)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l t) G.X H.X ≫
      ((f)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l t).map (Mod.tensorπ G H) ≫ c = T' := by
    rw [Functor.LaxMonoidal.comp_μ, Category.assoc]
    exact congrArg (μ (stalkFunctor l t) ((f)^*[WeilCoefficients.{u} l].obj G.X)
      ((f)^*[WeilCoefficients.{u} l].obj H.X) ≫ ·) h₄
  have n₁ := τ.hom.naturality (Mod.tensorπ G H)
  have n₂ := NatTrans.IsMonoidal.tensor (τ := τ.hom) G.X H.X
  have key : (τ.hom.app G.X ⊗ₘ τ.hom.app H.X) ≫ T' =
      tensorStalkMap (t ≫ f) G H ≫ τ.hom.app ((Mod.tensorLeft H).obj G).X ≫ c := by
    rw [← h₂]
    calc (τ.hom.app G.X ⊗ₘ τ.hom.app H.X) ≫
          μ ((f)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l t) G.X H.X ≫
            ((f)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l t).map (Mod.tensorπ G H) ≫ c =
        ((τ.hom.app G.X ⊗ₘ τ.hom.app H.X) ≫
          μ ((f)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l t) G.X H.X) ≫
            ((f)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l t).map (Mod.tensorπ G H) ≫ c :=
          (Category.assoc _ _ _).symm
      _ = (μ (stalkFunctor l (t ≫ f)) G.X H.X ≫ τ.hom.app (G.X ⊗ H.X)) ≫
            ((f)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l t).map (Mod.tensorπ G H) ≫ c := by
          rw [← n₂]
      _ = μ (stalkFunctor l (t ≫ f)) G.X H.X ≫ (τ.hom.app (G.X ⊗ H.X) ≫
            ((f)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l t).map (Mod.tensorπ G H)) ≫ c := by
          simp only [Category.assoc]
      _ = μ (stalkFunctor l (t ≫ f)) G.X H.X ≫ ((stalkFunctor l (t ≫ f)).map (Mod.tensorπ G H) ≫
            τ.hom.app ((Mod.tensorLeft H).obj G).X) ≫ c := by
          rw [← n₁]
      _ = tensorStalkMap (t ≫ f) G H ≫ τ.hom.app ((Mod.tensorLeft H).obj G).X ≫ c := by
          simp only [tensorStalkMap, Category.assoc]
  have hττ : IsIso (τ.hom.app G.X ⊗ₘ τ.hom.app H.X) := inferInstance
  constructor
  · intro h
    have : IsIso ((τ.hom.app G.X ⊗ₘ τ.hom.app H.X) ≫ T') := by
      rw [key]
      infer_instance
    exact IsIso.of_isIso_comp_left (τ.hom.app G.X ⊗ₘ τ.hom.app H.X) T'
  · intro h
    have : IsIso T' := h
    have : IsIso (tensorStalkMap (t ≫ f) G H ≫ τ.hom.app ((Mod.tensorLeft H).obj G).X ≫ c) := by
      rw [← key]
      infer_instance
    exact IsIso.of_isIso_comp_right (tensorStalkMap (t ≫ f) G H)
      (τ.hom.app ((Mod.tensorLeft H).obj G).X ≫ c)

end Pullback

section Lisse

/-- **Stalks of tensor products of lisse sheaves.** At a point with values in an algebraically
closed field, the comparison `Φ G ⊗ Φ H ⟶ Φ (G ⊗_{ℚ̄_ℓ} H)` is an isomorphism when `H` is lisse.
Pulling back along the point makes `H` a finite sum of copies of `ℚ̄_ℓ`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_iso_biproduct_of_isAlgClosed`).
The comparison is additive in `H` and is an isomorphism for `H = ℚ̄_ℓ`. -/
theorem isIso_tensorStalkMap {K : Type u} [Field K] [IsAlgClosed K] {Z : Scheme.{u}}
    (s : Spec (.of K) ⟶ Z) (G : AdicSheaf l Z) {H : AdicSheaf l Z} (hH : IsAdicLisseSheaf H) :
    IsIso (tensorStalkMap s G H) := by
  have hs : s = 𝟙 _ ≫ s := (Category.id_comp s).symm
  rw [hs, isIso_tensorStalkMap_comp_iff]
  obtain ⟨n, ⟨e⟩⟩ := (hH.upperStar s).exists_iso_biproduct_of_isAlgClosed
  refine isIso_tensorStalkMap_of_iso _ _ e ?_
  exact isIso_tensorStalkMap_biproduct _ _ _ fun _ => isIso_tensorStalkMap_unit _ _

variable {X : Scheme.{u}}

/-- The functor `M ↦ P ⊗_{ℚ̄_ℓ} M` of `ℓ`-adic sheaves, for a fixed `P`. -/
noncomputable def tensorLeftFlip (P : AdicSheaf l X) : AdicSheaf l X ⥤ AdicSheaf l X where
  obj M := (Mod.tensorLeft M).obj P
  map g := (Mod.tensorLeftMap g).app P
  map_id M := by
    rw [Mod.tensorLeftMap_id]
    rfl
  map_comp f g := by
    rw [Mod.tensorLeftMap_comp]
    rfl

instance (P : AdicSheaf l X) : (tensorLeftFlip P).Additive where
  map_add {M M' f g} := by
    change (Mod.tensorLeftMap (f + g)).app P = (Mod.tensorLeftMap f).app P +
      (Mod.tensorLeftMap g).app P
    rw [Mod.tensorLeftMap_add, NatTrans.app_add]

/-- **The tensor product of lisse sheaves is lisse.** On a pro-étale cover trivialising `H`,
pullback commutes with the tensor product
(`AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso`) and `P ⊗_{ℚ̄_ℓ} ℚ̄_ℓⁿ ≅ Pⁿ`, a finite
direct sum of copies of the lisse pullback of `G`. -/
theorem IsAdicLisseSheaf.tensorLeft {G H : AdicSheaf l X} (hG : IsAdicLisseSheaf G)
    (hH : IsAdicLisseSheaf H) : IsAdicLisseSheaf ((Mod.tensorLeft H).obj G) := by
  obtain ⟨R, hR, hRH⟩ := hH
  obtain ⟨κ, V, g, rfl⟩ := R.exists_eq_ofArrows
  refine IsAdicLisseSheaf.of_cover g hR fun k => ?_
  obtain ⟨n, ⟨e⟩⟩ := hRH (g k) (.mk k)
  refine (IsAdicLisseSheaf.biproduct_const (hG.upperStar (g k)) n).of_iso ?_
  exact ((adicUpperStarTensorLeftIso l (g k) H).app G ≪≫
    (Mod.tensorLeftMapIso e).app _ ≪≫
    (tensorLeftFlip ((g k)^*ᵃ[l].obj G)).mapBiproduct _ ≪≫
    biproduct.mapIso fun _ => Mod.tensorLeftRegularIso.app _).symm

end Lisse

section Monodromy

open Scheme.FiniteEtale

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- **Monodromy preserves the tensor comparison.** For lisse `G` and `H` with `G ⊗_{ℚ̄_ℓ} H`
lisse, the transport of stalks along a path carries the comparison
`Φ_y G ⊗ Φ_y H ⟶ Φ_y (G ⊗_{ℚ̄_ℓ} H)` to the comparison at the end point: the comparison is the
evaluation pairing of the unit `G ⟶ 𝓗om(H, G ⊗_{ℚ̄_ℓ} H)` (a morphism of lisse sheaves, the
internal hom of lisse sheaves being lisse), and transport is natural and preserves evaluation
pairings (`AlgebraicGeometry.ProEtale.LisseMonodromy.mono_evaluationPairing`). -/
theorem LisseMonodromy.mono_tensorStalkMap (M : LisseMonodromy l Y Ω)
    {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z) (G H : LisseSheaf l Y)
    (hT : IsAdicLisseSheaf ((Mod.tensorLeft H.obj).obj G.obj))
    (g : (stalkFunctor l y).obj G.obj.X) (h : (stalkFunctor l y).obj H.obj.X) :
    ((M.mono τ).hom.app ⟨_, hT⟩).hom ((tensorStalkMap y G.obj H.obj).hom (g ⊗ₜ h)) =
      (tensorStalkMap z G.obj H.obj).hom
        (((M.mono τ).hom.app G).hom g ⊗ₜ ((M.mono τ).hom.app H).hom h) := by
  have hI : IsAdicLisseSheaf ((AdicSheaf.ihom H.obj).obj ((Mod.tensorLeft H.obj).obj G.obj)) :=
    IsAdicLisseSheaf.ihom H.property hT
  let η : G ⟶ ⟨_, hI⟩ := ObjectProperty.homMk ((Mod.ihomAdjunction H.obj).unit.app G.obj)
  have hη : ∀ x, ((M.mono τ).hom.app ⟨_, hI⟩).hom
      (((stalkFunctor l y).map ((Mod.ihomAdjunction H.obj).unit.app G.obj).hom).hom x) =
      ((stalkFunctor l z).map ((Mod.ihomAdjunction H.obj).unit.app G.obj).hom).hom
        (((M.mono τ).hom.app G).hom x) := fun x =>
    congrArg (fun m => m.hom x) ((M.mono τ).hom.naturality η)
  refine (congrArg (fun x => ((M.mono τ).hom.app ⟨_, hT⟩).hom x)
    (evaluationPairing_unit y G.obj H.obj g h).symm).trans ?_
  refine (M.mono_evaluationPairing τ H ⟨_, hT⟩ hI _ _).symm.trans ?_
  refine (congrArg (fun x => Mod.evaluationPairing (stalkFunctor l z) H.obj
    ((Mod.tensorLeft H.obj).obj G.obj) x (((M.mono τ).hom.app H).hom h)) (hη g)).trans ?_
  exact evaluationPairing_unit z G.obj H.obj _ _

end Monodromy

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilCoefficients

variable {l : ℕ} [Fact l.Prime]

/-- An element of the underlying `ℚ̄_ℓ`-vector space of a module over `ULift ℚ̄_ℓ`, as an element
of that module. -/
abbrev ofToModuleCat {M : WeilCoefficients.{u} l} (x : (toModuleCat l).obj M) : M := x

/-- An element of a module over `ULift ℚ̄_ℓ`, as an element of its underlying `ℚ̄_ℓ`-vector
space. -/
abbrev toToModuleCat {M : WeilCoefficients.{u} l} (x : M) : (toModuleCat l).obj M := x

/-- The canonical map `M ⊗_{ℚ̄_ℓ} N → M ⊗_{ULift ℚ̄_ℓ} N`, `m ⊗ n ↦ m ⊗ n`, for modules over
`ULift ℚ̄_ℓ` viewed as `ℚ̄_ℓ`-vector spaces. -/
noncomputable def tensorRestrict (M N : WeilCoefficients.{u} l) :
    TensorProduct (PadicAlgCl l) ((toModuleCat l).obj M) ((toModuleCat l).obj N) →ₗ[PadicAlgCl l]
      (toModuleCat l).obj (M ⊗ N) :=
  TensorProduct.lift <| LinearMap.mk₂ (PadicAlgCl l)
    (fun m n => toToModuleCat (M := M ⊗ N)
      (ofToModuleCat m ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] ofToModuleCat n))
    (fun m m' n => congrArg (toToModuleCat (M := M ⊗ N))
      (TensorProduct.add_tmul (ofToModuleCat m) (ofToModuleCat m') (ofToModuleCat n)))
    (fun c m n => congrArg (toToModuleCat (M := M ⊗ N))
      (TensorProduct.smul_tmul' (ULift.up c) (ofToModuleCat m) (ofToModuleCat n)).symm)
    (fun m n n' => congrArg (toToModuleCat (M := M ⊗ N))
      (TensorProduct.tmul_add (ofToModuleCat m) (ofToModuleCat n) (ofToModuleCat n')))
    (fun c m n => congrArg (toToModuleCat (M := M ⊗ N))
      (TensorProduct.tmul_smul (ULift.up c) (ofToModuleCat m) (ofToModuleCat n)))

lemma tensorRestrict_tmul (M N : WeilCoefficients.{u} l) (m : (toModuleCat l).obj M)
    (n : (toModuleCat l).obj N) :
    tensorRestrict M N (m ⊗ₜ n) = toToModuleCat (M := M ⊗ N)
      (ofToModuleCat m ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] ofToModuleCat n) :=
  TensorProduct.lift.tmul _ _

/-- The canonical map `M ⊗_{ℚ̄_ℓ} N → M ⊗_{ULift ℚ̄_ℓ} N` is bijective. -/
lemma tensorRestrict_bijective (M N : WeilCoefficients.{u} l) :
    Function.Bijective (tensorRestrict M N) := by
  let A := TensorProduct (PadicAlgCl l) ((toModuleCat l).obj M) ((toModuleCat l).obj N)
  let fwd : A →+ ↑(M ⊗ N) := AddMonoidHom.mk' (fun x => ofToModuleCat (tensorRestrict M N x))
    fun x y => map_add (tensorRestrict M N) x y
  let inv : ↑(M ⊗ N) →+ A :=
    TensorProduct.liftAddHom
      { toFun m :=
          { toFun n := toToModuleCat m ⊗ₜ[PadicAlgCl l] toToModuleCat n
            map_zero' := TensorProduct.tmul_zero _ _
            map_add' n n' := TensorProduct.tmul_add _ _ _ }
        map_zero' := by ext n; exact TensorProduct.zero_tmul _ _
        map_add' m m' := by ext n; exact TensorProduct.add_tmul _ _ _ }
      fun r m n => TensorProduct.smul_tmul r.down (toToModuleCat m) (toToModuleCat n)
  have h₁ : ∀ x, inv (fwd x) = x := fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul m n =>
      change inv (ofToModuleCat (tensorRestrict M N (m ⊗ₜ n))) = _
      rw [tensorRestrict_tmul]
      exact TensorProduct.liftAddHom_tmul _ _ _ _
    | add x y hx hy => simp only [map_add, hx, hy]
  have h₂ : ∀ y, fwd (inv y) = y := fun y => by
    induction y using TensorProduct.inductionOn with
    | tmul m n =>
      change ofToModuleCat (tensorRestrict M N (toToModuleCat m ⊗ₜ toToModuleCat n)) = _
      rw [tensorRestrict_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨fun x y hxy => (h₁ x).symm.trans ((congrArg inv (congrArg ofToModuleCat hxy)).trans
    (h₁ y)), fun y => ⟨inv y, h₂ y⟩⟩

end AlgebraicGeometry.WeilCoefficients
