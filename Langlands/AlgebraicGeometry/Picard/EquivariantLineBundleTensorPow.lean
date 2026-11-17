import Langlands.AlgebraicGeometry.Picard.EquivariantLineBundle
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Langlands.AlgebraicGeometry.Modules.PullbackMonoidal
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms

/-! # Tensor powers of actual equivariant line bundles -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.Scheme.Modules

variable {W X Y : Scheme.{u}}

/-- Functoriality of tensor powers: identities. -/
@[simp]
lemma tensorPowMap_id (M : X.Modules) (n : ℕ) : tensorPowMap (𝟙 M) n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change tensorMap (𝟙 M) (tensorPowMap (𝟙 M) n) = 𝟙 _
      rw [ih]
      exact (tensorFunctor X).map_id (M, tensorPow M n)

/-- Functoriality of tensor powers: composition. -/
lemma tensorPowMap_comp {M N P : X.Modules} (a : M ⟶ N) (b : N ⟶ P) (n : ℕ) :
    tensorPowMap (a ≫ b) n = tensorPowMap a n ≫ tensorPowMap b n := by
  induction n with
  | zero => exact (Category.comp_id _).symm
  | succ n ih =>
      change tensorMap (a ≫ b) (tensorPowMap (a ≫ b) n) =
        tensorMap a (tensorPowMap a n) ≫ tensorMap b (tensorPowMap b n)
      rw [ih, tensorMap_comp]

/-- Pullback of module sheaves commutes with right-associated tensor powers. -/
def pullbackTensorPowIso (f : X ⟶ Y) (M : Y.Modules) : (n : ℕ) →
    (Scheme.Modules.pullback f).obj (tensorPow M n) ≅
      tensorPow ((Scheme.Modules.pullback f).obj M) n
  | 0 => pullbackUnitIso f
  | n + 1 => pullbackTensorIso f M (tensorPow M n) ≪≫
      (tensorFunctor X).mapIso ((Iso.refl _).prod (pullbackTensorPowIso f M n))

lemma pullbackTensorPowIso_succ_hom (f : X ⟶ Y) (M : Y.Modules) (n : ℕ) :
    (pullbackTensorPowIso f M (n + 1)).hom =
      pullbackTensorComparisonApp f M (tensorPow M n) ≫
        tensorMap (𝟙 _) (pullbackTensorPowIso f M n).hom := rfl

/-- Naturality of the tensor-power comparison in the module. -/
lemma pullbackTensorPowIso_naturality (f : X ⟶ Y) {M M' : Y.Modules} (g : M ⟶ M') (n : ℕ) :
    (Scheme.Modules.pullback f).map (tensorPowMap g n) ≫ (pullbackTensorPowIso f M' n).hom =
      (pullbackTensorPowIso f M n).hom ≫ tensorPowMap ((Scheme.Modules.pullback f).map g) n := by
  induction n with
  | zero =>
      change (Scheme.Modules.pullback f).map (𝟙 (structureSheaf Y)) ≫ (pullbackUnitIso f).hom =
        (pullbackUnitIso f).hom ≫ 𝟙 _
      rw [CategoryTheory.Functor.map_id]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ n ih =>
      change (Scheme.Modules.pullback f).map (tensorMap g (tensorPowMap g n)) ≫
          (pullbackTensorComparisonApp f M' (tensorPow M' n) ≫
            tensorMap (𝟙 _) (pullbackTensorPowIso f M' n).hom) =
        (pullbackTensorComparisonApp f M (tensorPow M n) ≫
            tensorMap (𝟙 _) (pullbackTensorPowIso f M n).hom) ≫
          tensorMap ((Scheme.Modules.pullback f).map g)
            (tensorPowMap ((Scheme.Modules.pullback f).map g) n)
      rw [← Category.assoc, pullbackTensorComparisonApp_naturality, Category.assoc,
        Category.assoc, tensorMap_comp, tensorMap_comp, ih, Category.id_comp, Category.comp_id]

/-- Compatibility of the tensor-power comparison with composition of pullbacks. -/
lemma pullbackTensorPowIso_comp (k : W ⟶ X) (a : X ⟶ Y) (M : Y.Modules) (n : ℕ) :
    (Scheme.Modules.pullbackComp k a).hom.app (tensorPow M n) ≫
        (pullbackTensorPowIso (k ≫ a) M n).hom =
      (Scheme.Modules.pullback k).map (pullbackTensorPowIso a M n).hom ≫
        (pullbackTensorPowIso k ((Scheme.Modules.pullback a).obj M) n).hom ≫
          tensorPowMap ((Scheme.Modules.pullbackComp k a).hom.app M) n := by
  induction n with
  | zero =>
      change (Scheme.Modules.pullbackComp k a).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
          (pullbackUnitIso (k ≫ a)).hom =
        (Scheme.Modules.pullback k).map (pullbackUnitIso a).hom ≫ (pullbackUnitIso k).hom ≫ 𝟙 _
      rw [pullbackUnitComposition]
      exact congrArg _ (Category.comp_id _).symm
  | succ n ih =>
      change (Scheme.Modules.pullbackComp k a).hom.app (tensorObj M (tensorPow M n)) ≫
          (pullbackTensorComparisonApp (k ≫ a) M (tensorPow M n) ≫
            tensorMap (𝟙 _) (pullbackTensorPowIso (k ≫ a) M n).hom) =
        (Scheme.Modules.pullback k).map (pullbackTensorComparisonApp a M (tensorPow M n) ≫
            tensorMap (𝟙 _) (pullbackTensorPowIso a M n).hom) ≫
          (pullbackTensorComparisonApp k ((Scheme.Modules.pullback a).obj M)
              (tensorPow ((Scheme.Modules.pullback a).obj M) n) ≫
            tensorMap (𝟙 _) (pullbackTensorPowIso k ((Scheme.Modules.pullback a).obj M) n).hom) ≫
          tensorMap ((Scheme.Modules.pullbackComp k a).hom.app M)
            (tensorPowMap ((Scheme.Modules.pullbackComp k a).hom.app M) n)
      rw [← Category.assoc, pullbackTensorComposition, Functor.map_comp]
      simp only [Category.assoc]
      rw [tensorMap_comp, reassoc_of% (pullbackTensorComparisonApp_naturality k
        (𝟙 ((Scheme.Modules.pullback a).obj M)) (pullbackTensorPowIso a M n).hom),
        tensorMap_comp, tensorMap_comp, ih, CategoryTheory.Functor.map_id]
      simp only [Category.id_comp, Category.comp_id]

@[simp]
lemma tensorPowIso_refl (M : X.Modules) (n : ℕ) : tensorPowIso (Iso.refl M) n = Iso.refl _ := by
  ext1
  rw [tensorPowIso_hom, Iso.refl_hom, tensorPowMap_id, Iso.refl_hom]

lemma tensorPowIso_trans {M N P : X.Modules} (e : M ≅ N) (e' : N ≅ P) (n : ℕ) :
    tensorPowIso (e ≪≫ e') n = tensorPowIso e n ≪≫ tensorPowIso e' n := by
  ext1
  rw [tensorPowIso_hom, Iso.trans_hom, Iso.trans_hom, tensorPowIso_hom, tensorPowIso_hom,
    tensorPowMap_comp]

lemma tensorPowIso_symm {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    tensorPowIso e.symm n = (tensorPowIso e n).symm := by
  ext1
  rw [← cancel_epi (tensorPowIso e n).hom, Iso.symm_hom, Iso.hom_inv_id, tensorPowIso_hom,
    tensorPowIso_hom, ← tensorPowMap_comp, Iso.symm_hom, e.hom_inv_id, tensorPowMap_id]

/-- Isomorphism form of the composition compatibility. -/
lemma pullbackTensorPowIso_comp_iso (k : W ⟶ X) (a : X ⟶ Y) (M : Y.Modules) (n : ℕ) :
    pullbackTensorPowIso (k ≫ a) M n =
      ((Scheme.Modules.pullbackComp k a).app (tensorPow M n)).symm ≪≫
        (Scheme.Modules.pullback k).mapIso (pullbackTensorPowIso a M n) ≪≫
          pullbackTensorPowIso k ((Scheme.Modules.pullback a).obj M) n ≪≫
            tensorPowIso ((Scheme.Modules.pullbackComp k a).app M) n := by
  ext1
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorPowIso_hom, Iso.app_hom,
    Iso.app_inv]
  rw [← pullbackTensorPowIso_comp, Iso.inv_hom_id_app_assoc]

/-- Isomorphism form of the naturality of the comparison. -/
lemma pullbackTensorPowIso_naturality_iso (f : X ⟶ Y) {M M' : Y.Modules} (e : M ≅ M') (n : ℕ) :
    (Scheme.Modules.pullback f).mapIso (tensorPowIso e n) ≪≫ pullbackTensorPowIso f M' n =
      pullbackTensorPowIso f M n ≪≫ tensorPowIso ((Scheme.Modules.pullback f).mapIso e) n := by
  ext1
  simp only [Iso.trans_hom, Functor.mapIso_hom, tensorPowIso_hom]
  exact pullbackTensorPowIso_naturality f e.hom n

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

variable {E : EtaleEquivalenceRelation.{u}}

namespace EquivariantLineBundle

/-- The underlying module isomorphism of a transport. -/
def transportModule (B : EquivariantLineBundle E) {T : Scheme.{u}} (a b : T ⟶ E.U)
    (h : E.Related a b) :
    (Scheme.Modules.pullback a).obj B.bundle.obj ≅ (Scheme.Modules.pullback b).obj B.bundle.obj :=
  (LineBundle.forget T).mapIso (B.transport a b h)

/-- The transport on the `n`-th tensor power, through the canonical tensor-power comparisons. -/
def tensorPowTransport (B : EquivariantLineBundle E) (n : ℕ) {T : Scheme.{u}} (a b : T ⟶ E.U)
    (h : E.Related a b) :
    (Scheme.Modules.pullback a).obj (tensorPow B.bundle.obj n) ≅
      (Scheme.Modules.pullback b).obj (tensorPow B.bundle.obj n) :=
  pullbackTensorPowIso a B.bundle.obj n ≪≫ tensorPowIso (B.transportModule a b h) n ≪≫
    (pullbackTensorPowIso b B.bundle.obj n).symm

lemma transportModule_self (B : EquivariantLineBundle E) {T : Scheme.{u}} (a : T ⟶ E.U)
    (h : E.Related a a) : B.transportModule a a h = Iso.refl _ := by
  rw [transportModule, B.transport_self]
  rfl

lemma transportModule_trans (B : EquivariantLineBundle E) {T : Scheme.{u}} (a b c : T ⟶ E.U)
    (hab : E.Related a b) (hbc : E.Related b c) (hac : E.Related a c) :
    B.transportModule a b hab ≪≫ B.transportModule b c hbc = B.transportModule a c hac := by
  rw [transportModule, transportModule, transportModule, ← B.transport_trans a b c hab hbc hac,
    Functor.mapIso_trans]
  rfl

lemma transportModule_precompose (B : EquivariantLineBundle E) {T W : Scheme.{u}} (k : W ⟶ T)
    (a b : T ⟶ E.U) (h : E.Related a b) (h' : E.Related (k ≫ a) (k ≫ b)) :
    B.transportModule (k ≫ a) (k ≫ b) h' =
      ((Scheme.Modules.pullbackComp k a).app B.bundle.obj).symm ≪≫
        (Scheme.Modules.pullback k).mapIso (B.transportModule a b h) ≪≫
          (Scheme.Modules.pullbackComp k b).app B.bundle.obj := by
  rw [transportModule, B.transport_precompose k a b h h']
  rfl

lemma tensorPowTransport_self (B : EquivariantLineBundle E) (n : ℕ) {T : Scheme.{u}}
    (a : T ⟶ E.U) (h : E.Related a a) : B.tensorPowTransport n a a h = Iso.refl _ := by
  rw [tensorPowTransport, transportModule_self, tensorPowIso_refl, Iso.refl_trans,
    Iso.self_symm_id]

lemma tensorPowTransport_trans (B : EquivariantLineBundle E) (n : ℕ) {T : Scheme.{u}}
    (a b c : T ⟶ E.U) (hab : E.Related a b) (hbc : E.Related b c) (hac : E.Related a c) :
    B.tensorPowTransport n a b hab ≪≫ B.tensorPowTransport n b c hbc =
      B.tensorPowTransport n a c hac := by
  rw [tensorPowTransport, tensorPowTransport, tensorPowTransport,
    ← B.transportModule_trans a b c hab hbc hac, tensorPowIso_trans]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

lemma tensorPowTransport_precompose (B : EquivariantLineBundle E) (n : ℕ) {T W : Scheme.{u}}
    (k : W ⟶ T) (a b : T ⟶ E.U) (h : E.Related a b) (h' : E.Related (k ≫ a) (k ≫ b)) :
    B.tensorPowTransport n (k ≫ a) (k ≫ b) h' =
      ((Scheme.Modules.pullbackComp k a).app (tensorPow B.bundle.obj n)).symm ≪≫
        (Scheme.Modules.pullback k).mapIso (B.tensorPowTransport n a b h) ≪≫
          (Scheme.Modules.pullbackComp k b).app (tensorPow B.bundle.obj n) := by
  rw [tensorPowTransport, tensorPowTransport, B.transportModule_precompose k a b h h',
    pullbackTensorPowIso_comp_iso, pullbackTensorPowIso_comp_iso, tensorPowIso_trans,
    tensorPowIso_trans, tensorPowIso_symm]
  have hnat := pullbackTensorPowIso_naturality_iso k (B.transportModule a b h) n
  ext1
  have hnat' := congrArg Iso.hom hnat
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_trans,
    Functor.mapIso_symm, Iso.trans_assoc, Iso.trans_inv, Iso.symm_inv] at hnat' ⊢
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% hnat']
  simp

end EquivariantLineBundle

end Langlands.AlgebraicGeometry.Picard
