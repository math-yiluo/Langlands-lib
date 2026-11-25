/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassChern
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerForgetEvaluation
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionEvaluation

/-! # Universal property of the evaluated scalar-extended root tower

Source: blueprint sec-smooth-purity/sk-prop-sp-tower-geometric,
classes (2), evaluation of coefficient extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory Opposite AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

private def constantResidueHomEquiv (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) (n : ℕ)
    (M N : SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (Rlevel l T n)) :
    (M ⟶ N) ≃
      ((SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj N) := by
  let J := Scheme.ProEt.topology T
  let P := (Functor.const T.ProEtᵒᵖ).obj
    (CommRingCat.of (ULift.{u + 1, 0} (ZMod (l ^ (n + 1)))))
  let η := toSheafify J P
  have : J.WEqualsLocallyBijective CommRingCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
      (A := CommRingCat.{u + 1}) J
  have : Presheaf.IsLocallySurjective J η := by dsimp [η]; infer_instance
  refine
    { toFun := (SheafOfModules.toSheaf _).map
      invFun := fun q ↦ ⟨PresheafOfModules.homMk q.hom ?_⟩
      left_inv := fun f ↦ ?_
      right_inv := fun q ↦ ?_ }
  · intro U a x
    let qU : M.val.obj U →+ N.val.obj U := (q.hom.app U).hom
    apply N.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J η a)
    rintro V p ⟨b, hb⟩
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective b.down
    have hb' : b = (z : ULift.{u + 1, 0} (ZMod (l ^ (n + 1)))) :=
      ULift.ext hz.symm
    let qV : M.val.obj (op V) →+ N.val.obj (op V) := (q.hom.app (op V)).hom
    have hn (y : M.val.obj U) :
        qV (M.val.map p.op y) = N.val.map p.op (qU y) :=
      ConcreteCategory.congr_hom (q.hom.naturality p.op) y
    have hb'' : (η.app (op V)) b =
        ((SemilinearSections.ring J (Rlevel l T n)).obj.map p.op) a := hb
    change N.val.map p.op (qU (a • x)) = N.val.map p.op (a • qU x)
    erw [← hn, M.val.map_smul, N.val.map_smul, ← hb'', hb', map_intCast,
      Int.cast_smul_eq_zsmul, map_zsmul, Int.cast_smul_eq_zsmul, hn]
    exact (Int.cast_smul_eq_zsmul _ z _).symm
  · apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    rfl
  · apply Sheaf.hom_ext
    ext U x
    rfl

private theorem constantResidueHomEquiv_apply (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (n : ℕ)
    (M N : SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (Rlevel l T n)) (f : M ⟶ N) :
    constantResidueHomEquiv l T n M N f = (SheafOfModules.toSheaf _).map f := rfl

attribute [local irreducible] constantResidueHomEquiv

attribute [local irreducible] SemilinearSections.scalarExtensionSection

/-- Evaluation of scalar extension represents additive maps from the roots sheaf.
Source: blueprint classes (2), evaluation of coefficient extension
(blueprint: lem-sp-tower-line-evaluation-universal).

Proof: restrict the sequence-site scalar-extension presheaf to level n. Its value
at U is A_n(U) tensor over R_n(U) with the evaluated root module. Vertical
restriction commutes with sheafification: covering sieves in the sequence topology
restrict to exactly the covering sieves at level n, and the sheafification unit
is locally bijective on both sites. The tensor/restriction adjunction consequently
identifies morphisms from the evaluated extension with R_n-linear maps from the
evaluated root module to N with scalars restricted along the coefficient map.
The section and restriction equations of the recorded Forget functor identify
its underlying additive sheaf with the n-th level of the forgotten root module.
Compose with rootForget to identify this with the actual roots sheaf. Additive
maps between sheaves killed by ell^(n+1) are automatically linear over the
constant ZMod sheaf, by local lifting of scalars to constant integer sections.
These identifications give the displayed Hom equivalences. Postcomposition
commutes with each identification. The tensor adjunction sends x to 1 tensor x;
linearity gives the displayed formula for arbitrary a. No normalization of the
derived Chern comparisons is required. -/
theorem towerLineEvaluation_universal (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T) (n : ℕ) :
    ∃ Φ : ∀ N : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T n),
      (((SpTowerShriek.ev l E T n).obj (lineModule l E c)) ⟶ N) ≃
        ((roots l T).obj (op n) ⟶ (SheafOfModules.toSheaf _).obj N),
      (∀ {N N'} (f : (SpTowerShriek.ev l E T n).obj (lineModule l E c) ⟶ N)
        (g : N ⟶ N'),
        Φ N' (f ≫ g) = Φ N f ≫ (SheafOfModules.toSheaf _).map g) ∧
      (∀ N (f : (SpTowerShriek.ev l E T n).obj (lineModule l E c) ⟶ N)
        (U : T.ProEtᵒᵖ) (a : (SpTowerShriek.B l E T n).obj.obj U)
        (x : c.rootModule.val.obj (op (n, U.unop)))
        (x' : ((c.reduction.forget.F.obj c.rootModule).obj (op n)).obj.obj U)
        (v : ((SpTowerShriek.ev l E T n).obj (lineModule l E c)).val.obj U),
        HEq x x' →
        HEq v (a • SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
          (coefficientSystemMap l E T) c.scalar c.rootModule (op (n, U.unop)) x) →
        f.val.app U v = a • (show N.val.obj U from (Φ N f).hom.app U
          (((c.rootForget.hom.app (op n)).hom.app U) x'))) := by
  dsimp only [lineModule, SpTowerShriek.ev, SpTowerShriek.B, SpTowerShriek.tau]
  let J := Scheme.ProEt.topology T
  let R := fun n ↦ (Rrings l T).obj (op n)
  let τ := fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op
  let D := fun n ↦ (Arings l E T).obj (op n)
  let σ := fun n ↦ (Arings l E T).map (homOfLE (Nat.le_succ n)).op
  let φ : SemilinearSections.systemRing.{u + 1, u, u + 1} J R τ ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} J D σ := coefficientSystemMap l E T
  have hφ : ∀ (n : ℕ) (U : T.ProEtᵒᵖ),
      φ.hom.app (op (n, U.unop)) = (coefficientMap l E T n).hom.app U :=
    (SemilinearSections.systemMap_existsUnique.{u + 1, u, u + 1} J R τ
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
      (coefficientMap l E T) (coefficientMap_transition l E T)).exists.choose_spec
  obtain ⟨Ψ, hΨ, hsection⟩ := SemilinearSections.scalarExtension_evaluation.{u + 1, u, u + 1}
    J R D τ σ (coefficientMap l E T) φ hφ c.scalar c.rootModule n
  let M := (SemilinearSections.evaluation.{u + 1, u, u + 1} J R τ n).obj c.rootModule
  obtain ⟨e, he⟩ := forget_evaluation_iso T (Rrings l T) c.reduction.forget
    c.rootModule n (roots l T) c.rootForget
  let Φ := fun N ↦ (Ψ N).trans
    ((constantResidueHomEquiv l T n M
      ((SemilinearSections.res (coefficientMap l E T n)).obj N)).trans
        (Iso.homCongr e.symm (Iso.refl _)))
  have hΦ (N : SemilinearSections.Mod.{u + 1, u, u + 1}
      J (D n))
      (f : (SemilinearSections.evaluation.{u + 1, u, u + 1}
        J D σ n).obj
          (c.scalar.model.E.obj c.rootModule) ⟶ N) :
      Φ N f = e.hom ≫
        (SheafOfModules.toSheaf
          (SemilinearSections.ring (Scheme.ProEt.topology T) (Rlevel l T n))).map (Ψ N f) := by
    dsimp only [Φ]
    erw [Equiv.trans_apply, Equiv.trans_apply, constantResidueHomEquiv_apply,
      Iso.homCongr_apply]
    simp only [Iso.symm_inv, Iso.refl_hom, Category.comp_id]
  refine ⟨Φ, ?_, ?_⟩
  · intro N N' f g
    erw [hΦ, hΦ, hΨ]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  · intro N f U a x x' v hx hv
    erw [hΦ]
    change f.val.app U v = a • (show N.val.obj U from (Ψ N f).val.app U
      (e.hom.hom.app U (((c.rootForget.hom.app (op n)).hom.app U) x')))
    rw [he U x x' hx]
    exact hsection N f U a x v hv

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
