/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.PicardCupProductMap
import WeilConjectures.AlgebraicGeometry.StalkFiniteFree
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Equal local ranks turn a split counit into an isomorphism

Source: Stacks Project, Tag 0BDP, final paragraph, the square dual-basis matrices.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem bijective_of_split_of_finrank_eq
    {R M N : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Free R M] [Module.Free R N] [Module.Finite R M] [Module.Finite R N]
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) (hab : b.comp a = LinearMap.id)
    (hr : Module.finrank R M = Module.finrank R N) : Function.Bijective a := by
  classical
  let e := LinearEquiv.ofFinrankEq M N hr
  have hb : Function.Surjective b := fun m ↦ ⟨a m, DFunLike.congr_fun hab m⟩
  have ht : Function.Injective (b.comp e.toLinearMap) :=
    Module.End.injective_of_surjective R M (hb.comp e.surjective)
  have hbi : Function.Injective b := by
    intro n n' h
    have he : e.symm n = e.symm n' := ht (by simpa using h)
    exact e.symm.injective he
  refine ⟨Function.LeftInverse.injective (g := b) (DFunLike.congr_fun hab), ?_⟩
  intro n
  refine ⟨b n, hbi ?_⟩
  exact DFunLike.congr_fun hab (b n)

private theorem isIso_of_splitMono_of_fixed_rank
    {Z : Scheme.{u}} {M N : Z.Modules} (a : M ⟶ N) (r : ℕ)
    [M.IsFiniteLocallyFreeOfRank r] [N.IsFiniteLocallyFreeOfRank r]
    [IsSplitMono a] : IsIso a := by
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N r
  apply Modules.isIso_of_bijective_stalkLinearMap
  intro z
  obtain ⟨hMf, hMn⟩ := Modules.stalk_isFiniteFree_of_isFiniteLocallyFree M z
  obtain ⟨hNf, hNn⟩ := Modules.stalk_isFiniteFree_of_isFiniteLocallyFree N z
  let F := RingedSpace.moduleStalkFunctor Z.toRingedSpace z
  have : IsSplitMono (F.map a) := inferInstance
  apply bijective_of_split_of_finrank_eq (a := (F.map a).hom)
    (b := (retraction (F.map a)).hom)
  · exact congrArg ModuleCat.Hom.hom (IsSplitMono.id (F.map a))
  · exact (Modules.finiteLocallyFreeOfRank_stalk_finrank M r z).trans
      (Modules.finiteLocallyFreeOfRank_stalk_finrank N r z).symm

/-- A split inclusion of the two pulled-back bundles is invertible when their ranks
agree on neighbourhoods in the base. Neither cup product nor an adjunction is needed.

Source: Stacks Project, Tag 0BDP, final paragraph, equal-size dual-basis matrices.
(blueprint: lem-sc-picard-split-mono-equal-ranks)

Proof: For each base point w choose U and r from hRanks. The canonical map
X_U to X_W is the base change of the open immersion U to W. Pullback composition
identifies the source restricted to X_U with p_U^*(N|_U), of rank r, and the target
with E|_X_U, also of rank r. Pulling back the retraction preserves its identity.
At each stalk we therefore have a split injection of finite free modules of rank r.
Identify them by any basis isomorphism. The resulting split endomorphism of a finite
free module over a commutative ring has its one-sided inverse on both sides; this
follows from the square-matrix determinant identity. Thus every stalk map is bijective,
and the restricted map is invertible. The X_U cover X_W, so pullback along this open
cover reflects isomorphisms. Rank zero and empty schemes are included. -/
theorem isIso_of_isSplitMono_of_picard_local_ranks
    {X S W : Scheme.{u}} (f : X ⟶ S) (E : X.Modules) (j : W ⟶ S) (N : W.Modules)
    (hRanks : ∀ w : W, ∃ U : W.Opens, w ∈ U ∧ ∃ r : ℕ,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj N) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (U.ι ≫ j))).obj E) r)
    (a : (Modules.tensorPullback (pullback.snd f j)).obj N ⟶
      (Modules.tensorPullback (pullback.fst f j)).obj E)
    [IsSplitMono a] : IsIso a := by
  classical
  choose U hw r hNr hMr using hRanks
  let p := pullback.snd f j
  let q := pullback.fst f j
  let d (w : W) := pullbackLeftPullbackSndIso f j (U w).ι
  let b (w : W) := (d w).inv ≫ pullback.fst p (U w).ι
  have hb₁ (w : W) : b w ≫ q = pullback.fst f ((U w).ι ≫ j) := by
    simp [b, d, p, q]
  have hb₂ (w : W) : b w ≫ p = pullback.snd f ((U w).ι ≫ j) ≫ (U w).ι := by
    simp [b, d, p]
  have (w : W) : IsOpenImmersion (b w) := by dsimp [b, d, p]; infer_instance
  apply Modules.isIso_of_isIso_pullback_map b
  · intro z
    obtain ⟨y, hy, hy'⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback p (U (p z)).ι) z ⟨p z, hw (p z)⟩ rfl
    refine ⟨p z, (d (p z)).hom y, ?_⟩
    rw [← Hom.comp_apply]
    simpa [b, Category.assoc] using hy
  · intro w
    let pU := pullback.snd f ((U w).ι ≫ j)
    let NU := (Modules.tensorPullback (U w).ι).obj N
    have : NU.IsFiniteLocallyFreeOfRank (r w) := hNr w
    let eN : (Modules.pullback (b w)).obj ((Modules.tensorPullback p).obj N) ≅
        (Modules.pullback pU).obj NU :=
      (Modules.picardTensorComparison (b w)).symm.app _ ≪≫
        (Modules.nonempty_tensorPullbackComp (b w) p).some.symm.app N ≪≫
        eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj N) (hb₂ w)) ≪≫
        (Modules.nonempty_tensorPullbackComp pU (U w).ι).some.app N ≪≫
        (Modules.picardTensorComparison pU).app NU
    let eM : (Modules.pullback (b w)).obj ((Modules.tensorPullback q).obj E) ≅
        (Modules.tensorPullback (pullback.fst f ((U w).ι ≫ j))).obj E :=
      (Modules.picardTensorComparison (b w)).symm.app _ ≪≫
        (Modules.nonempty_tensorPullbackComp (b w) q).some.symm.app E ≪≫
        eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj E) (hb₁ w))
    have hsource : ((Modules.pullback (b w)).obj
        ((Modules.tensorPullback p).obj N)).IsFiniteLocallyFreeOfRank (r w) :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso eN.symm
    have := hMr w
    have htarget : ((Modules.pullback (b w)).obj
        ((Modules.tensorPullback q).obj E)).IsFiniteLocallyFreeOfRank (r w) :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso eM.symm
    exact isIso_of_splitMono_of_fixed_rank ((Modules.pullback (b w)).map a) (r w)

end AlgebraicGeometry.Scheme
