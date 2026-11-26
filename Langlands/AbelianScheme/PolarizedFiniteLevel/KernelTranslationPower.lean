import Langlands.AbelianScheme.PolarizedFiniteLevel.KernelTranslationCocycle

/-! # Tensor powers of kernel translation comparisons -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Scheme.Modules

open CategoryTheory.MonoidalCategory Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

private lemma tensorMap_smul {X : Scheme.{u}} {M M' N N' : X.Modules}
    (r s : Γ(X, ⊤)) (f : M ⟶ M') (g : N ⟶ N') :
    tensorMap (r • f) (s • g) = (r * s) • tensorMap f g := by
  apply (tensorHomEquiv M N (tensorObj M' N')).injective
  conv_lhs => rw [← Category.comp_id (tensorMap (r • f) (s • g))]
  have h : (r * s) • tensorMap f g = tensorMap f g ≫ ((r * s) • 𝟙 _) := by
    rw [Linear.comp_smul, Category.comp_id]
  rw [h, tensorHomEquiv_tensorMap_comp, tensorHomEquiv_tensorMap_comp]
  have h' : tensorHomEquiv M' N' (tensorObj M' N') ((r * s) • 𝟙 _) =
      tensorHomEquiv M' N' (tensorObj M' N') (𝟙 _) ≫ ((r * s) • 𝟙 (tensorObj M' N')).val := by
    conv_lhs => rw [← Category.id_comp ((r * s) • 𝟙 (tensorObj M' N'))]
    rw [tensorHomEquiv_comp]
  rw [h']
  refine PresheafOfModules.hom_ext (fun U => ModuleCat.MonoidalCategory.tensor_ext (fun x y => ?_))
  let u := X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  let w := (tensorSheafifyUnit M' N').app U
  change w.hom (((u r) • f.app U.unop x) ⊗ₜ ((u s) • g.app U.unop y)) =
    (u (r * s)) • w.hom (f.app U.unop x ⊗ₜ g.app U.unop y)
  rw [TensorProduct.smul_tmul_smul, map_smul, map_mul]

private lemma tensorPowMap_smul {X : Scheme.{u}} {M N : X.Modules}
    (r : Γ(X, ⊤)) (f : M ⟶ N) (n : ℕ) :
    tensorPowMap (r • f) n = r ^ n • tensorPowMap f n := by
  induction n with
  | zero => simp [tensorPowMap]
  | succ n ih =>
    change tensorMap (r • f) (tensorPowMap (r • f) n) = _ • tensorMap f (tensorPowMap f n)
    rw [ih, tensorMap_smul, pow_succ']

variable {X U : Scheme.{u}} {F : X.Modules} {a b c : U ⟶ X}

/-- The map on a power of the bundle, expressed on pullbacks along the same two maps. -/
def pullbackPowerMap (n : ℕ) (f : (Scheme.Modules.pullback a).obj F ⟶
    (Scheme.Modules.pullback b).obj F) : (Scheme.Modules.pullback a).obj (tensorPow F n) ⟶
      (Scheme.Modules.pullback b).obj (tensorPow F n) :=
  (pullbackTensorPowIso a F n).hom ≫ tensorPowMap f n ≫ (pullbackTensorPowIso b F n).inv

private lemma pullbackPowerMap_eq_hom (n : ℕ) (e : (Scheme.Modules.pullback a).obj F ≅
    (Scheme.Modules.pullback b).obj F) :
    pullbackPowerMap n e.hom = (pullbackTensorPowIso a F n ≪≫ tensorPowIso e n ≪≫
      (pullbackTensorPowIso b F n).symm).hom := by
  simp only [pullbackPowerMap, Iso.trans_hom, tensorPowIso_hom, Iso.symm_hom]

instance pullbackPowerMap_isIso (n : ℕ) (f : (Scheme.Modules.pullback a).obj F ⟶
    (Scheme.Modules.pullback b).obj F) [IsIso f] : IsIso (pullbackPowerMap n f) := by
  rw [show f = (asIso f).hom from rfl, pullbackPowerMap_eq_hom]
  infer_instance

lemma pullbackPowerMap_comp (n : ℕ) (f : (Scheme.Modules.pullback a).obj F ⟶
    (Scheme.Modules.pullback b).obj F) (g : (Scheme.Modules.pullback b).obj F ⟶
    (Scheme.Modules.pullback c).obj F) :
    pullbackPowerMap n (f ≫ g) = pullbackPowerMap n f ≫ pullbackPowerMap n g := by
  simp [pullbackPowerMap, tensorPowMap_comp]

lemma pullbackPowerMap_smul (n : ℕ) (r : Γ(U, ⊤))
    (f : (Scheme.Modules.pullback a).obj F ⟶ (Scheme.Modules.pullback b).obj F) :
    pullbackPowerMap n (r • f) = r ^ n • pullbackPowerMap n f := by
  rw [pullbackPowerMap, tensorPowMap_smul, Linear.smul_comp, Linear.comp_smul]
  rfl

lemma transport_rfl {V : Scheme.{u}} (k : V ⟶ U)
    (f : (Scheme.Modules.pullback a).obj F ⟶ (Scheme.Modules.pullback b).obj F) :
    transport k (u' := k ≫ a) (v' := k ≫ b) rfl rfl f =
      (Scheme.Modules.pullbackComp k a).inv.app F ≫
        (Scheme.Modules.pullback k).map f ≫ (Scheme.Modules.pullbackComp k b).hom.app F := by
  simp [transport, compIso, UnitCocycleDescentUniqueness.compIso, Scheme.Modules.pullbackCongr]

set_option maxHeartbeats 800000 in
lemma pullbackPowerMap_transport {V : Scheme.{u}} (k : V ⟶ U) (n : ℕ)
    (f : (Scheme.Modules.pullback a).obj F ⟶ (Scheme.Modules.pullback b).obj F) [IsIso f] :
    pullbackPowerMap n (transport k (u' := k ≫ a) (v' := k ≫ b) rfl rfl f) =
      transport k (u' := k ≫ a) (v' := k ≫ b) rfl rfl (pullbackPowerMap n f) := by
  rw [transport_rfl, transport_rfl]
  let e := asIso f
  let e' := ((Scheme.Modules.pullbackComp k a).app F).symm ≪≫
    (Scheme.Modules.pullback k).mapIso e ≪≫ (Scheme.Modules.pullbackComp k b).app F
  change pullbackPowerMap n e'.hom = _
  rw [pullbackPowerMap_eq_hom]
  dsimp only [e']
  rw [pullbackTensorPowIso_comp_iso, pullbackTensorPowIso_comp_iso, tensorPowIso_trans,
    tensorPowIso_trans, tensorPowIso_symm]
  have hnat := congrArg Iso.hom (pullbackTensorPowIso_naturality_iso k e n)
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.trans_assoc, Iso.trans_inv,
    Iso.symm_inv] at hnat ⊢
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% hnat]
  simp [pullbackPowerMap, e]

end Langlands.Scheme.Modules
