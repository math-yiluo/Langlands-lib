/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward
import WeilConjectures.AlgebraicGeometry.Modules.QuasiAffineLocallyFreeEmbedding
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicPushforwardCoordinates
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChangeIsIso
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # A finite kernel presentation for sections on finite étale thickenings

## References

* Stacks Project, Tag 0EKP, construction in the proof of (2) to (3), with the ample invertible
  module equal to the structure sheaf
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem canonical_structure_baseChange_isIso {X Y X' Y' : Scheme.{u}}
    (p : X ⟶ Y) (q : X' ⟶ Y') (g : Y' ⟶ Y) (k : X' ⟶ X)
    (sq : IsPullback k q p g) [IsAffineHom p] :
    IsIso (((pullbackPushforwardAdjunction g).homEquiv _ _).symm
      ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
        (pushforwardComp k p).hom.app (unit X') ≫
        (pushforwardCongr sq.w).hom.app (unit X') ≫
        (pushforwardComp q g).inv.app (unit X'))) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  let E := (pushforward p).obj (unit X)
  let β := moduleBaseChangeMap p q g k sq.w (unit X)
  let ε := tensorPullbackObjUnitToUnit k
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : IsIso β := affinePushforward_baseChange_isIso p q g k sq (unit X)
  have : IsIso ε := (tensorPullbackObjUnitToUnit_isIso k).1
  let b := ((pullbackPushforwardAdjunction g).homEquiv _ _).symm
    ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
      (pushforwardComp k p).hom.app (unit X') ≫
      (pushforwardCongr sq.w).hom.app (unit X') ≫
      (pushforwardComp q g).inv.app (unit X'))
  have hb : b = (Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction g) adj).hom.app E ≫
      β ≫ (pushforward q).map ε := by
    apply ((pullbackPushforwardAdjunction g).homEquiv _ _).injective
    dsimp only [b]
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [← adj.homEquiv_unit]
    dsimp only [β, moduleBaseChangeMap]
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    simp only [Category.assoc]
    rw [← Functor.comp_map]
    rw [← (pushforwardComp q g).inv.naturality ε]
    rw [← (pushforwardCongr sq.w).hom.naturality_assoc ε]
    rw [← (pushforwardComp k p).hom.naturality_assoc ε]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp_assoc, (tensorPullbackObjUnitToUnit_isIso k).2]
  change IsIso b
  rw [hb]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem canonical_structure_baseChange_app_unit {X Y X' Y' : Scheme.{u}}
    (p : X ⟶ Y) (q : X' ⟶ Y') (g : Y' ⟶ Y) (k : X' ⟶ X)
    (w : k ≫ p = q ≫ g) (a : Γ(X, ⊤)) :
    ((((pullbackPushforwardAdjunction g).homEquiv _ _).symm
      ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
        (pushforwardComp k p).hom.app (unit X') ≫
        (pushforwardCongr w).hom.app (unit X') ≫
        (pushforwardComp q g).inv.app (unit X'))).app ⊤)
      (pullbackΓ g ((pushforward p).obj (unit X)) a) = k.appTop a := by
  have h := ((pullbackPushforwardAdjunction g).homEquiv _ _).apply_symm_apply
    ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
      (pushforwardComp k p).hom.app (unit X') ≫
      (pushforwardCongr w).hom.app (unit X') ≫
      (pushforwardComp q g).inv.app (unit X'))
  rw [Adjunction.homEquiv_unit] at h
  have ht := congrArg (fun z ↦ z.app ⊤ a) h
  simp only [Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardComp_inv_app_app, pushforwardCongr_hom_app_app,
    ConcreteCategory.comp_apply, eqToHom_refl, CategoryTheory.op_id] at ht
  erw [CategoryTheory.Functor.map_id] at ht
  dsimp at ht
  rw [pullbackΓ_apply]
  exact ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem free_coordinate_pullback_unit {X Y : Scheme.{u}} (g : Y ⟶ X)
    (I : Type u) [Fintype I] [DecidableEq I]
    (x : Γ(SheafOfModules.free (R := X.ringCatSheaf) I, ⊤)) (i : I) :
    freeSectionsEquiv I ((pullbackFreeIso g I).hom.app ⊤
      (pullbackΓ g (SheafOfModules.free I) x)) i = g.appTop (freeSectionsEquiv I x i) := by
  change Hom.app (freeπ (X := Y) i) ⊤ ((pullbackFreeIso g I).hom.app ⊤
    (pullbackΓ g (SheafOfModules.free I) x)) = _
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, pullbackFreeIso_hom_freeπ]
  change (pullbackObjUnitIso g).hom.app ⊤
    (((pullback g).map (freeπ i)).app ⊤ (pullbackΓ g (SheafOfModules.free I) x)) = _
  rw [pullbackΓ_naturality]
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    g.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at h
  have h' : (pullbackPushforwardAdjunction g).unit.app (unit X) ≫
      (pushforward g).map (pullbackObjUnitIso g).hom =
        SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := h
  have ht := congrArg (fun q ↦ Hom.app q ⊤ (Hom.app (freeπ (X := X) i) ⊤ x)) h'
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at ht
  rw [pullbackΓ_apply]
  exact ht

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

private theorem injective_module_app {X : Scheme.{u}} {M N : X.Modules}
    (α : M ⟶ N) [Mono α] : Function.Injective (α.app ⊤) := by
  let G := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)
  have : Mono (G.map α) := G.map_mono α
  exact (ModuleCat.mono_iff_injective (G.map α)).mp inferInstance

private theorem lift_of_cokernel_app_zero {X : Scheme.{u}} {M N : X.Modules}
    (α : M ⟶ N) [Mono α] (x : Γ(N, ⊤)) (hx : (cokernel.π α).app ⊤ x = 0) :
    ∃ a : Γ(M, ⊤), α.app ⊤ a = x := by
  have hx' : x ∈ {x | (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
      (cokernel.π α) x = 0} := hx
  rw [← Modules.range_map_kernelι ⊤ (cokernel.π α)] at hx'
  obtain ⟨k, hk⟩ := hx'
  refine ⟨(inv (Abelian.factorThruImage α)).app ⊤ k, ?_⟩
  have h : inv (Abelian.factorThruImage α) ≫ α = kernel.ι (cokernel.π α) := by
    calc
      inv (Abelian.factorThruImage α) ≫ α =
          inv (Abelian.factorThruImage α) ≫
            (Abelian.factorThruImage α ≫ kernel.ι (cokernel.π α)) :=
        congrArg (fun q ↦ inv (Abelian.factorThruImage α) ≫ q) (Abelian.image.fac α).symm
      _ = _ := by rw [IsIso.inv_hom_id_assoc]
  change (inv (Abelian.factorThruImage α) ≫ α).app ⊤ k = x
  rw [h]
  exact hk

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adic_coordinates_projection
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (V : (Spec (.of R)).Opens) (P : V.toScheme.FiniteEtale)
    {r : ℕ}
    (α : (Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left) ⟶
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))
    (n : ℕ) (hb : Function.Bijective
      ((FiniteEtale.Adic.pushforwardComparison f V P n).app ⊤))
    (a : Γ(P.obj.left, ⊤)) (i : Fin r) :
    FiniteEtale.Adic.coordinates f V P α n ((FiniteEtale.Adic.coverMap f V P n).appTop a) i =
      (pullback.fst V.ι (FiniteEtale.Adic.baseMap f n)).appTop
        (Modules.freeSectionsEquiv (ULift.{u} (Fin r)) (α.app ⊤ a) (ULift.up i)) := by
  let g := pullback.fst V.ι (FiniteEtale.Adic.baseMap f n)
  let E := (Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left)
  have hu : (FiniteEtale.Adic.pushforwardComparison f V P n).app ⊤
      (AlgebraicGeometry.pullbackΓ g E a) = (FiniteEtale.Adic.coverMap f V P n).appTop a := by
    exact Modules.canonical_structure_baseChange_app_unit P.obj.hom
      (FiniteEtale.Adic.coverToBase f V P n) g (FiniteEtale.Adic.coverMap f V P n)
      (by simp [FiniteEtale.Adic.coverToBase, g]) a
  have hs : FiniteEtale.Adic.liftSection f V P n
      ((FiniteEtale.Adic.coverMap f V P n).appTop a) = AlgebraicGeometry.pullbackΓ g E a := by
    rw [← hu]
    exact Function.leftInverse_invFun hb.1 _
  change Modules.freeSectionsEquiv (ULift.{u} (Fin r))
    (((Modules.pullback g).map α ≫
      (Modules.pullbackFreeIso g (ULift.{u} (Fin r))).hom).app ⊤
        (FiniteEtale.Adic.liftSection f V P n
          ((FiniteEtale.Adic.coverMap f V P n).appTop a))) (ULift.up i) = _
  rw [hs]
  change Modules.freeSectionsEquiv (ULift.{u} (Fin r))
    ((Modules.pullbackFreeIso g (ULift.{u} (Fin r))).hom.app ⊤
      (((Modules.pullback g).map α).app ⊤ (AlgebraicGeometry.pullbackΓ g E a))) (ULift.up i) = _
  rw [AlgebraicGeometry.pullbackΓ_naturality]
  exact Modules.free_coordinate_pullback_unit g _ _ _

private theorem pullback_matrix_relation {X Y : Scheme.{u}} {M : X.Modules}
    {r t : ℕ} (g : Y ⟶ X)
    (α : M ⟶ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))
    (δ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      SheafOfModules.free (ULift.{u} (Fin t))) (hz : α ≫ δ = 0)
    (a : Γ((Modules.pullback g).obj M, ⊤)) (j : Fin t) :
    ∑ i : Fin r, g.appTop (Modules.freeMatrix δ (ULift.up j) (ULift.up i)) *
      Modules.freeSectionsEquiv (ULift.{u} (Fin r))
        (((Modules.pullback g).map α ≫
          (Modules.pullbackFreeIso g (ULift.{u} (Fin r))).hom).app ⊤ a) (ULift.up i) = 0 := by
  let δn := (Modules.pullbackFreeIso g (ULift.{u} (Fin r))).inv ≫
    (Modules.pullback g).map δ ≫ (Modules.pullbackFreeIso g (ULift.{u} (Fin t))).hom
  let yn := ((Modules.pullback g).map α ≫
    (Modules.pullbackFreeIso g (ULift.{u} (Fin r))).hom).app ⊤ a
  have hy : δn.app ⊤ yn = 0 := by
    change (((Modules.pullback g).map α ≫
      (Modules.pullbackFreeIso g (ULift.{u} (Fin r))).hom) ≫ δn).app ⊤ a = 0
    have hcomp : ((Modules.pullback g).map α ≫
        (Modules.pullbackFreeIso g (ULift.{u} (Fin r))).hom) ≫ δn = 0 := by
      dsimp only [δn]
      rw [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, hz,
        Functor.map_zero, zero_comp]
    rw [hcomp]
    rfl
  have hmat := congrFun (Modules.freeSectionsEquiv_app δn yn) (ULift.up j)
  rw [hy, map_zero] at hmat
  have hm : Modules.freeMatrix δn = (Modules.freeMatrix δ).map g.appTop :=
    Modules.freeMatrix_pullback g δ
  rw [hm] at hmat
  change 0 = ∑ i : ULift.{u} (Fin r),
    g.appTop (Modules.freeMatrix δ (ULift.up j) i) *
      Modules.freeSectionsEquiv (ULift.{u} (Fin r)) yn i at hmat
  rw [← (Equiv.ulift.symm : Fin r ≃ ULift.{u} (Fin r)).sum_comp] at hmat
  exact hmat.symm

/-- Finite étale sections admit finite scalar coordinates and finitely many linear relations,
with injective coordinates on every quotient-power thickening. This statement does not
assume any scalar adic comparison. -/
theorem finiteEtale_adic_sections_kernel
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (V : (Spec (.of R)).Opens) (P : V.toScheme.FiniteEtale) :
    ∃ (r t : ℕ)
      (e : Γ(P.obj.left, ⊤) → Fin r → Γ(V.toScheme, ⊤))
      (en : ∀ n : ℕ, Γ(FiniteEtale.Adic.cover f V P n, ⊤) →
        Fin r → Γ(Limits.pullback V.ι (FiniteEtale.Adic.baseMap f n), ⊤))
      (c : Fin t → Fin r → Γ(V.toScheme, ⊤)),
      Function.Injective e ∧
      (∀ n, Function.Injective (en n)) ∧
      (∀ x : Fin r → Γ(V.toScheme, ⊤),
        (∀ j : Fin t, ∑ i : Fin r, c j i * x i = 0) → ∃ a, e a = x) ∧
      (∀ (n : ℕ) (a : Γ(FiniteEtale.Adic.cover f V P n, ⊤)) (j : Fin t),
        ∑ i : Fin r, (pullback.fst V.ι (FiniteEtale.Adic.baseMap f n)).appTop
          (c j i) * en n a i = 0) ∧
      (∀ (n : ℕ) (a : Γ(P.obj.left, ⊤)) (i : Fin r),
        en n ((FiniteEtale.Adic.coverMap f V P n).appTop a) i =
          (pullback.fst V.ι (FiniteEtale.Adic.baseMap f n)).appTop (e a i)) ∧
      (∀ (n : ℕ) (a : Γ(FiniteEtale.Adic.cover f V P (n + 1), ⊤)) (i : Fin r),
        en n ((FiniteEtale.Adic.coverTransition f V P n).appTop a) i =
          (pullback.lift (pullback.fst V.ι (FiniteEtale.Adic.baseMap f n))
            (pullback.snd V.ι (FiniteEtale.Adic.baseMap f n) ≫
              FiniteEtale.Adic.baseTransition f n)
            (by rw [Category.assoc, FiniteEtale.Adic.baseTransition_comp_baseMap]
                exact pullback.condition)).appTop (en (n + 1) a i)) := by
  classical
  let E := (Modules.pushforward P.obj.hom).obj (Modules.unit P.obj.left)
  let : IsFinite P.obj.hom := P.property
  let : Etale P.obj.hom := P.obj.prop
  let : (Modules.unit P.obj.left).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree
      (SheafOfModules.unit P.obj.left.ringCatSheaf)
      (h := SheafOfModules.instIsInvertibleUnit.{u, u, u})
  let : E.IsFiniteLocallyFree :=
    Modules.isFiniteLocallyFree_pushforward P.obj.hom (Modules.unit P.obj.left)
  obtain ⟨r, α, hα, hC, hαpb⟩ := Modules.exists_universally_mono_free V E
  let : Mono α := hα
  let : (cokernel α).IsFiniteLocallyFree := hC
  obtain ⟨t, β, hβ, _, _⟩ := Modules.exists_universally_mono_free V (cokernel α)
  let : Mono β := hβ
  let δ := cokernel.π α ≫ β
  let e : Γ(P.obj.left, ⊤) → Fin r → Γ(V.toScheme, ⊤) :=
    fun a i ↦ Modules.freeSectionsEquiv (ULift.{u} (Fin r)) (α.app ⊤ a) (ULift.up i)
  let en := FiniteEtale.Adic.coordinates f V P α
  let c : Fin t → Fin r → Γ(V.toScheme, ⊤) :=
    fun j i ↦ Modules.freeMatrix δ (ULift.up j) (ULift.up i)
  have hz : α ≫ δ = 0 := by simp [δ]
  have hbc (n : ℕ) : Function.Bijective
      ((FiniteEtale.Adic.pushforwardComparison f V P n).app ⊤) := by
    have sq : IsPullback (FiniteEtale.Adic.coverMap f V P n)
        (FiniteEtale.Adic.coverToBase f V P n) P.obj.hom
        (pullback.fst V.ι (FiniteEtale.Adic.baseMap f n)) := by
      refine IsPullback.of_bot ?_ (by simp [FiniteEtale.Adic.coverToBase])
        (IsPullback.of_hasPullback V.ι (FiniteEtale.Adic.baseMap f n))
      simpa only [FiniteEtale.Adic.coverToBase, pullback.lift_snd,
        FiniteEtale.Adic.coverMap] using
          (IsPullback.of_hasPullback (P.obj.hom ≫ V.ι) (FiniteEtale.Adic.baseMap f n))
    have : IsIso (FiniteEtale.Adic.pushforwardComparison f V P n) :=
      Modules.canonical_structure_baseChange_isIso P.obj.hom
        (FiniteEtale.Adic.coverToBase f V P n)
        (pullback.fst V.ι (FiniteEtale.Adic.baseMap f n))
        (FiniteEtale.Adic.coverMap f V P n) sq
    exact ConcreteCategory.bijective_of_isIso _
  have hproj := fun n a i ↦ adic_coordinates_projection f V P α n (hbc n) a i
  have htrans := FiniteEtale.Adic.pushforward_coordinates_transition f V P r α
  refine ⟨r, t, e, en, c, ?_, ?_, ?_, ?_, hproj, htrans⟩
  · intro a b hab
    apply injective_module_app α
    apply (Modules.freeSectionsEquiv (ULift.{u} (Fin r))).injective
    ext i
    exact congrFun hab i.down
  · intro n a b hab
    let g := pullback.fst V.ι (FiniteEtale.Adic.baseMap f n)
    let : Mono ((Modules.pullback g).map α) := hαpb _ g
    have hm : Function.Injective
        (((Modules.pullback g).map α ≫
          (Modules.pullbackFreeIso g (ULift.{u} (Fin r))).hom).app ⊤) :=
      injective_module_app _
    apply (Function.rightInverse_invFun (hbc n).2).injective
    apply hm
    apply (Modules.freeSectionsEquiv (ULift.{u} (Fin r))).injective
    ext i
    exact congrFun hab i.down
  · intro x hx
    let y := (Modules.freeSectionsEquiv (ULift.{u} (Fin r))).symm (fun i ↦ x i.down)
    have hδ : δ.app ⊤ y = 0 := by
      apply (Modules.freeSectionsEquiv (ULift.{u} (Fin t))).injective
      rw [Modules.freeSectionsEquiv_app, map_zero]
      ext j
      have hh := hx j.down
      rw [← (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r).sum_comp] at hh
      simpa [c, y, Matrix.mulVec, dotProduct] using hh
    have hπ : (cokernel.π α).app ⊤ y = 0 := by
      apply injective_module_app β
      simpa [δ, Modules.Hom.comp_app] using hδ
    obtain ⟨a, ha⟩ := lift_of_cokernel_app_zero α y hπ
    refine ⟨a, ?_⟩
    funext i
    change Modules.freeSectionsEquiv (ULift.{u} (Fin r)) (α.app ⊤ a) (ULift.up i) = x i
    rw [ha]
    simp [y]
  · intro n a j
    exact pullback_matrix_relation (pullback.fst V.ι (FiniteEtale.Adic.baseMap f n))
      α δ hz (FiniteEtale.Adic.liftSection f V P n a) j

end AlgebraicGeometry.Scheme
