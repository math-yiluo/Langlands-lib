/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions

import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateLocalRootTensorsExt
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateTransportedPullbackNormalization

/-! # Coherence of normalized finite Tate comparison maps

Source: Stacks Project, Tags 03PK, 03Q1 and 099R.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

private theorem etale_root_value_injective (T : Scheme.{u}) (m : ℕ)
    (U : T.Etaleᵒᵖ) : Function.Injective (finiteTateEtaleRootValue T m U) := by
  have : Mono (kernel.ι (m • 𝟙 T.gmSheaf)).hom :=
    (sheafToPresheaf _ _).map_mono _
  intro x y h
  apply (AddCommGrpCat.mono_iff_injective
    ((kernel.ι (m • 𝟙 T.gmSheaf)).hom.app U)).mp inferInstance
  apply ULift.ext
  exact Additive.toMul.injective h

private theorem etale_root_pullback_value (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
    (U : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf m).obj.obj U) :
    finiteTateEtaleRootValue T' m _
      (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
        ((finiteEtaleTwistPullbackData A m hm hA).r v hT).hom).hom.app U z) =
      Units.map (pullback.fst U.unop.hom v).appTop.hom.toMonoidHom
        (finiteTateEtaleRootValue T m U z) := by
  have h := congrArg
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _)
      ((finiteEtaleTwistPullbackData A m hm hA).laws.2.1 v hT)
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right] at h
  unfold upperStarGmSheafToGmSheaf at h
  rw [Equiv.apply_symm_apply] at h
  exact congrArg (fun f ↦ Additive.toMul ((f.hom.app U z).down)) h.symm

private theorem etale_tensor_map_generator (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) {M N M' N' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : M ⟶ M') (g : N ⟶ N') (U : T.Etaleᵒᵖ)
    (x : M.obj.obj U) (y : N.obj.obj U) :
    (tensorHom f g).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M N).app U (x ⊗ₜ[A] y)) =
    (Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M' N').app U
      (f.hom.app U x ⊗ₜ[A] g.hom.app U y) := by
  have h := congrArg (fun t ↦ t.app U)
    (Functor.LaxMonoidal.μ_natural (F := sheafToPresheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} A)) f g)
  exact (ConcreteCategory.congr_hom h (x ⊗ₜ[A] y)).symm

private theorem etale_unit_generator (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    Functor.LaxMonoidal.ε (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) =
      toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A)) := by
  simp only [Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
  change _ ≫ (sheafToPresheaf _ _).map (𝟙 _) = _
  simp
  rfl

private theorem etale_pullback_zero_generator (A : Type (u + 1)) [CommRing A]
    {T T' : Scheme.{u}} (v : T' ⟶ T) (U : T.Etaleᵒᵖ) (a : A) :
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
        (ModuleCat.of A A)).hom).hom.app U
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app U a) =
    (toSheafify T'.smallEtaleTopology
      ((Functor.const T'.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U) a := by
  let : (MorphismProperty.Over.pullback @Etale ⊤ v).IsContinuous
      T.smallEtaleTopology T'.smallEtaleTopology :=
    Scheme.isContinuous_overPullback @Etale @Etale le_rfl v
  have h := Etale.upperStarConstantSheafIso_hom_app_tensorUnit (ModuleCat.{u + 1} A) v
  change (upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).hom.app
    (ModuleCat.of A A) = _ at h
  erw [Iso.app_hom, h, Etale.upperStarLowerStarAdjunction_homEquiv_η]
  rw [← etale_unit_generator, ← etale_unit_generator]
  exact ConcreteCategory.congr_hom
    (Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
      (MorphismProperty.Over.pullback @Etale ⊤ v) (ModuleCat.{u + 1} A)
      T.smallEtaleTopology T'.smallEtaleTopology U) a

private theorem etale_pushforward_tensor_generator (A : Type (u + 1)) [CommRing A]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (M N : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) (U : T.Etaleᵒᵖ)
    (x : M.obj.obj ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U))
    (y : N.obj.obj ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U)) :
    (Functor.LaxMonoidal.μ (Etale.lowerStar (ModuleCat.{u + 1} A) v) M N).hom.app U
      ((Functor.LaxMonoidal.μ
        (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        ((Etale.lowerStar (ModuleCat.{u + 1} A) v).obj M)
        ((Etale.lowerStar (ModuleCat.{u + 1} A) v).obj N)).app U (x ⊗ₜ[A] y)) =
    (Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M N).app
      ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U) (x ⊗ₜ[A] y) := by
  let : (MorphismProperty.Over.pullback @Etale ⊤ v).IsContinuous
      T.smallEtaleTopology T'.smallEtaleTopology :=
    Scheme.isContinuous_overPullback @Etale @Etale le_rfl v
  have h := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (MorphismProperty.Over.pullback @Etale ⊤ v) (ModuleCat.{u + 1} A)
    T.smallEtaleTopology T'.smallEtaleTopology M N U
  have hx := ConcreteCategory.congr_hom h (x ⊗ₜ[A] y)
  exact hx

private theorem etale_pullback_tensor_generator (A : Type (u + 1)) [CommRing A]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    {M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M' N' : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : (Etale.upperStar (ModuleCat.{u + 1} A) v).obj M ⟶ M')
    (g : (Etale.upperStar (ModuleCat.{u + 1} A) v).obj N ⟶ N')
    (U : T.Etaleᵒᵖ) (x : M.obj.obj U) (y : N.obj.obj U) :
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
      (Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v) M N ≫
        tensorHom f g)).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M N).app U (x ⊗ₜ[A] y)) =
    (Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M' N').app
      ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U)
      ((((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _ f).hom.app
        U x) ⊗ₜ[A]
        (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _ g).hom.app
          U y)) := by
  have h : (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
      (Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v) M N ≫
        tensorHom f g) =
    tensorHom
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _ f)
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _ g) ≫
        Functor.LaxMonoidal.μ (Etale.lowerStar (ModuleCat.{u + 1} A) v) M' N' := by
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    rw [(Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).unit_app_tensor_comp_map_δ]
    rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural,
      ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
  rw [h]
  change (Functor.LaxMonoidal.μ (Etale.lowerStar (ModuleCat.{u + 1} A) v) M' N').hom.app U
    ((tensorHom
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _ f)
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _ g)).hom.app
        U _) = _
  rw [etale_tensor_map_generator, etale_pushforward_tensor_generator]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (n : ℕ)

private theorem etale_pullback_normalized {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (l : Γ(T, ⊤))) (hT' : IsUnit (l : Γ(T', ⊤)))
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ) :
    IsFiniteTateEtalePullback l E n T v r hA k
      ((finiteEtaleTwistPullbackData (finiteTateCoefficient l E n) (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) hA).c v
          (by simpa using hT.pow (r + 1))
          (by simpa using hT'.pow (r + 1)) (k : ℤ)) := by
  let C := finiteEtaleTwistPullbackData (finiteTateCoefficient l E n) (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) hA
  let H : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa using hT.pow (r + 1)
  let H' : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T', ⊤)) := by
    simpa using hT'.pow (r + 1)
  change IsFiniteTateEtalePullback l E n T v r hA k (C.c v H H' (k : ℤ))
  refine Nat.twoStepInduction ?_ ?_ ?_ k
  · intro U a z z' hz
    change ((Etale.upperStarLowerStarAdjunction _ v).homEquiv _ _
      (C.c v H H' 0).hom).hom.app U _ = _
    rw [C.laws.2.2.2.1 v H H']
    exact etale_pullback_zero_generator _ v U a
  · intro U a z z' hz
    have hz' :
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
          (C.r v H).hom).hom.app U (z 0) = z' 0 := by
      apply etale_root_value_injective T' (l ^ (r + 1)) _
      exact (etale_root_pullback_value _ _ _ hA v H U (z 0)).trans (hz 0).symm
    change ((Etale.upperStarLowerStarAdjunction _ v).homEquiv _ _
      (C.c v H H' 1).hom).hom.app U
        (finiteEtaleTateOneGenerator _ _ T hA U a (z 0)) = _
    rw [C.laws.2.2.1 v H H' U a (z 0), hz']
    rfl
  · intro j hj hj1 U a z z' hz
    change ((Etale.upperStarLowerStarAdjunction _ v).homEquiv _ _
      (C.c v H H' (.ofNat (j + 2))).hom).hom.app U _ = _
    rw [C.laws.2.2.2.2.1 v H H' j]
    change ((Etale.upperStarLowerStarAdjunction _ v).homEquiv _ _
      (Functor.OplaxMonoidal.δ (Etale.upperStar _ v) _ _ ≫
        tensorHom (C.c v H H' (.ofNat (j + 1))).hom (C.c v H H' 1).hom)).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n))) _ _).app U
        (finiteTateEtalePowerGenerator T _ _ hA U a (j + 1)
          (fun i ↦ z i.castSucc) ⊗ₜ[_]
        finiteEtaleTateOneGenerator _ _ T hA U 1 (z (Fin.last (j + 1))))) = _
    rw [etale_pullback_tensor_generator]
    erw [hj1 U a (fun i ↦ z i.castSucc) (fun i ↦ z' i.castSucc)
      (fun i ↦ hz i.castSucc)]
    have hz' :
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
          (C.r v H).hom).hom.app U (z (Fin.last (j + 1))) =
            z' (Fin.last (j + 1)) := by
      apply etale_root_value_injective T' (l ^ (r + 1)) _
      exact (etale_root_pullback_value _ _ _ hA v H U _).trans (hz _).symm
    rw [C.laws.2.2.1 v H H' U 1 _, hz']
    rfl

private theorem etale_root_power_value (T : Scheme.{u}) (m m' q : ℕ)
    (f : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
    (hf : f ≫ kernel.ι (m • 𝟙 T.gmSheaf) = q • kernel.ι (m' • 𝟙 T.gmSheaf))
    (U : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf m').obj.obj U) :
    finiteTateEtaleRootValue T m U (f.hom.app U z) =
      finiteTateEtaleRootValue T m' U z ^ q := by
  have h := congrArg (fun t ↦ t.hom.app U z) hf
  have hn : (q • kernel.ι (m' • 𝟙 T.gmSheaf)).hom =
      q • (kernel.ι (m' • 𝟙 T.gmSheaf)).hom :=
    (sheafToPresheaf _ _).map_nsmul (f := kernel.ι (m' • 𝟙 T.gmSheaf)) (n := q)
  rw [hn, NatTrans.app_nsmul] at h
  exact congrArg (fun t ↦ Additive.toMul t.down) h

private theorem etale_transition_normalized (T : Scheme.{u})
    (hT : IsUnit (l : Γ(T, ⊤))) (r r' : ℕ) (h : r ≤ r')
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (hA' : ((l ^ (r' + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ) :
    ∃ q : T.rootsOfUnitySheaf (l ^ (r' + 1)) ⟶ T.rootsOfUnitySheaf (l ^ (r + 1)),
    ∃ t : finiteEtaleTateTwist T (l ^ (r' + 1)) _ hA' k ≅
        finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k,
      (∀ (U : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf (l ^ (r' + 1))).obj.obj U),
        finiteTateEtaleRootValue T (l ^ (r + 1)) U (q.hom.app U z) =
          finiteTateEtaleRootValue T (l ^ (r' + 1)) U z ^ (l ^ (r' - r))) ∧
      IsFiniteTateEtaleTransition l E n T r r' hA hA' k t := by
  let C := finiteEtaleTwistPullbackData (finiteTateCoefficient l E n) (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) hA
  have hdiv := pow_dvd_pow l (Nat.add_le_add_right h 1)
  have hT' : IsUnit ((l ^ (r' + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa using hT.pow (r' + 1)
  obtain ⟨q, t, hq, ht, ht0, htn, _⟩ :=
    C.laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (l ^ (r' + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hdiv T hT'
  have hd : l ^ (r' + 1) / l ^ (r + 1) = l ^ (r' - r) := by
    rw [← Nat.sub_add_cancel (Nat.add_le_add_right h 1), pow_add,
      Nat.mul_div_cancel _ (pow_pos (Fact.out : l.Prime).pos _)]
    congr 1
    omega
  have hq' := hq
  rw [hd] at hq'
  have hroot (U : T.Etaleᵒᵖ)
      (z' : (T.rootsOfUnitySheaf (l ^ (r' + 1))).obj.obj U)
      (z : (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U)
      (hz : finiteTateEtaleRootValue T (l ^ (r + 1)) U z =
        finiteTateEtaleRootValue T (l ^ (r' + 1)) U z' ^ (l ^ (r' - r))) :
      q.hom.app U z' = z := by
    apply etale_root_value_injective
    exact (etale_root_power_value T _ _ _ q hq' U z').trans hz.symm
  have hnorm (j : ℕ) : IsFiniteTateEtaleTransition l E n T r r' hA hA' j (t j) := by
    refine Nat.twoStepInduction ?_ ?_ ?_ j
    · intro U a z' z hz
      change (t 0).hom.hom.app U _ = _
      rw [ht0]
      rfl
    · intro U a z' z hz
      change (t 1).hom.hom.app U (finiteEtaleTateOneGenerator _ _ T hA' U a (z' 0)) = _
      rw [ht, hroot U _ _ (hz 0)]
      rfl
    · intro i hi hi1 U a z' z hz
      change (t (.ofNat (i + 2))).hom.hom.app U _ = _
      rw [htn]
      change (tensorHom (t (.ofNat (i + 1))).hom (t 1).hom).hom.app U
        ((Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n))) _ _).app U
          (finiteTateEtalePowerGenerator T _ _ hA' U a (i + 1)
            (fun j ↦ z' j.castSucc) ⊗ₜ[_]
          finiteEtaleTateOneGenerator _ _ T hA' U 1 (z' (Fin.last (i + 1))))) = _
      rw [etale_tensor_map_generator]
      erw [hi1 U a (fun j ↦ z' j.castSucc) (fun j ↦ z j.castSucc)
        (fun j ↦ hz j.castSucc)]
      rw [ht, hroot U _ _ (hz (Fin.last (i + 1)))]
      rfl
  exact ⟨q, t k, etale_root_power_value T _ _ _ q hq', hnorm k⟩

private theorem comparison_map_local_section (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) {M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (t : M ⟶ N) (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop) (z : M.obj.obj U) :
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map t).hom.app W
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj M).obj.map f.op
        (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M).hom.app U z)) =
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj N).obj.map f.op
      (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app N).hom.app U
        (t.hom.app U z)) := by
  have hn := ConcreteCategory.congr_hom
    (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map t).hom.naturality f.op)
      (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M).hom.app U z)
  have hu := congrArg (fun g ↦ g.hom.app U z)
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.naturality t)
  exact hn.trans (congrArg
    (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj N).obj.map f.op) hu.symm)

private theorem limit_root_successor (T : Scheme.{u}) (r : ℕ) (W : T.ProEtᵒᵖ)
    (x : (purTwistZlOne T l).obj.obj W) :
    finiteTateLimitRootValue l T r W x = finiteTateLimitRootValue l T (r + 1) W x ^ l := by
  let F := proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)
  have hw := congrArg (fun t ↦ t.hom.app W x)
    (limit.w F (homOfLE (Nat.le_succ r)).op)
  rw [show F.map (homOfLE (Nat.le_succ r)).op =
    proEtaleRootsOfUnityTransition T (l ^ (r + 1)) (l ^ (r + 2))
      (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
      (pow_dvd_pow l (Nat.le_succ (r + 1))) from
        Functor.ofOpSequence_map_homOfLE_succ _ r] at hw
  have ht := proEtaleRootsOfUnityTransition_prime T l (Fact.out : l.Prime) r W
    ((limit.π F (op (r + 1))).hom.app W x)
  exact congrArg (fun t ↦ Additive.toMul t.down)
    ((congrArg ((proEtaleRootsOfUnityInclusion T (l ^ (r + 1))).hom.app W)
      hw.symm).trans ht)

private theorem limit_root_power (T : Scheme.{u}) (r s : ℕ) (h : r ≤ s)
    (W : T.ProEtᵒᵖ) (x : (purTwistZlOne T l).obj.obj W) :
    finiteTateLimitRootValue l T r W x =
      finiteTateLimitRootValue l T s W x ^ (l ^ (s - r)) := by
  induction s, h using Nat.le_induction with
  | base => simp
  | succ s h ih =>
    rw [ih, limit_root_successor, ← pow_mul]
    congr 1
    rw [show s + 1 - r = (s - r) + 1 by omega, pow_succ, Nat.mul_comm]

/-- Normalized comparisons respect scheme pullback and changes of annihilator.
Source: `lem-amb-finite-tate-site-descent`, proof step 2; Stacks 03PK and 03Q1
(blueprint: lem-amb-finite-tate-normalized-coherence).

Proof: use the etale finite-twist pullback comparisons and power transitions.
Define the pro-etale pullback map by transporting the etale pullback comparison
through b and the canonical comparison/pullback square. On local finite-root
lifts the root-projection identities and the finite-root comparison formulas show
that this transported map sends each prescribed pure tensor to the pulled-back
tensor. Finite root projections are locally surjective and pure tensors locally
generate the sheafified tensor powers, so these identities descend to all tests.
The same detection proves that the etale exponent transition makes the comparison
square commute: its root formula is exactly the transition of the root tower.
The exponent transition is invertible by `etaleFiniteTwistPullback`. For degree
zero all formulas are constant scalar maps; in positive degrees tensor the
first-degree formulas, using monoidality of inverse image and of the comparison
pullback square. No pullback is commuted with the infinite root limit. -/
theorem finite_tate_normalized_coherence
    (b : ∀ (T : Scheme.{u}), IsUnit (l : Γ(T, ⊤)) →
      ∀ (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅ finiteTateProSheaf l E n T k)
    (hb : (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      IsFiniteTateSiteComparison l E n T r hA k (b T hT r hA k))) :
    (∀ (T T' : Scheme.{u}) (v : T' ⟶ T)
      (hT : IsUnit (l : Γ(T, ⊤))) (hT' : IsUnit (l : Γ(T', ⊤)))
      (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃ (c : (Etale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅
            finiteEtaleTateTwist T' (l ^ (r + 1)) _ hA k)
        (d : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
          (finiteTateProSheaf l E n T k) ≅ finiteTateProSheaf l E n T' k),
      IsFiniteTateEtalePullback l E n T v r hA k c ∧
      IsFiniteTateProPullback l E n T v k d ∧
      (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).mapIso
          (b T hT r hA k) ≪≫ d =
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).app
            (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T').mapIso c ≪≫ b T' hT' r hA k) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r r' : ℕ) (_h : r ≤ r')
      (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
      (hA' : ((l ^ (r' + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃ t : finiteEtaleTateTwist T (l ^ (r' + 1)) _ hA' k ≅
          finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k,
        IsFiniteTateEtaleTransition l E n T r r' hA hA' k t ∧
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).mapIso t ≪≫ b T hT r hA k =
            b T hT r' hA' k) := by
  constructor
  · intro T T' v hT hT' r hA k
    let c := (finiteEtaleTwistPullbackData (finiteTateCoefficient l E n) (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hA).c v
        (by simpa using hT.pow (r + 1)) (by simpa using hT'.pow (r + 1)) (k : ℤ)
    have hc : IsFiniteTateEtalePullback l E n T v r hA k c :=
      etale_pullback_normalized l E n v hT hT' r hA k
    let d :=
      (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).mapIso
        (b T hT r hA k).symm ≪≫
      (ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).app
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T').mapIso c ≪≫ b T' hT' r hA k
    refine ⟨c, d, hc, ?_, ?_⟩
    · exact finite_tate_transported_pullback_normalized l E n T T' v hT hT' r hA k
        (b T hT r hA k) (b T' hT' r hA k) (hb T hT r hA k) (hb T' hT' r hA k) c hc
    · simp [d]
  · intro T hT r r' hrr hA hA' k
    obtain ⟨q, t, hq, ht⟩ := etale_transition_normalized l E n T hT r r' hrr hA hA' k
    refine ⟨t, ht, ?_⟩
    apply Iso.ext
    apply finiteTate_local_root_tensors_hom_ext l E n T hT r' hA' k
    intro U W f a z x hx
    change (b T hT r hA k).hom.hom.app W
      (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).map t.hom).hom.app W _) = _
    rw [comparison_map_local_section]
    rw [ht U a z (fun i ↦ q.hom.app U (z i)) (fun i ↦ hq U (z i))]
    rw [hb T hT r hA k U W f a (fun i ↦ q.hom.app U (z i)) x,
      hb T hT r' hA' k U W f a z x hx]
    intro i
    rw [limit_root_power l T r r' hrr W (x i), hx i, hq, map_pow]

end AlgebraicGeometry.Scheme
