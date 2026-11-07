import Langlands.GroupScheme.Reductive.SemilinearPinning
import Langlands.GroupScheme.Reductive.PinningScalarTowerIso

/-! # Coherence of actual semilinear pinned lifts -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

private theorem equivalence_algebraic {k K : Type u} [Field k] [Field K]
    (σ : k ≃+* K) :
    letI : Algebra k K := σ.toRingHom.toAlgebra
    Algebra.IsAlgebraic k K := by
  let : Algebra k K := σ.toRingHom.toAlgebra
  constructor
  intro x
  obtain ⟨y, rfl⟩ := σ.surjective x
  exact isAlgebraic_algebraMap y

attribute [local instance] towerAffine

section Composition
variable {k : Type u} [Field k]
    {G H C : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom C.X.hom]
    {p : SplitPinning G} {q : SplitPinning H} {r : SplitPinning C}

theorem Iso.trans_character (f : Iso p q) (g : Iso q r)
    (χ : characterLattice p.torus) :
    characterLattice.congr (f.trans g).torusIso χ =
      characterLattice.congr g.torusIso (characterLattice.congr f.torusIso χ) := by
  change (g.torusIso.inv ≫ f.torusIso.inv) ≫ χ = _
  exact Category.assoc _ _ _

end Composition

section RingEquiv
variable {k K L : Type u} [Field k] [Field K] [Field L]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {p : SplitPinning G} {q : SplitPinning H}

/-- Pull back a complete pinned isomorphism along a specified field equivalence. -/
def Iso.baseChangeAlong (f : Iso p q) (σ : k ≃+* K) :
    Iso (p.baseChangeAlong σ) (q.baseChangeAlong σ) := by
  letI : Algebra k K := σ.toRingHom.toAlgebra
  letI : Algebra.IsAlgebraic k K := equivalence_algebraic σ
  exact f.baseChange (K := K)

@[simp] theorem Iso.baseChangeAlong_torusIso (f : Iso p q) (σ : k ≃+* K) :
    (f.baseChangeAlong σ).torusIso =
      (CommGroupScheme.baseChange (Spec.map (CommRingCat.ofHom σ.toRingHom))).mapIso
        f.torusIso := rfl

@[simp] theorem Iso.baseChangeAlong_groupIso (f : Iso p q) (σ : k ≃+* K) :
    (f.baseChangeAlong σ).groupIso =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom σ.toRingHom))).mapIso
        f.groupIso := rfl

@[simp] theorem Iso.baseChangeAlong_indexEquiv (f : Iso p q) (σ : k ≃+* K) :
    (f.baseChangeAlong σ).indexEquiv = f.indexEquiv := rfl

theorem Iso.baseChangeAlong_character (f : Iso p q) (σ : k ≃+* K)
    (χ : characterLattice p.torus) :
    characterLattice.congr (f.baseChangeAlong σ).torusIso
        ((p.baseChangeAlongRootDatumEquiv σ).weightEquiv χ) =
      (q.baseChangeAlongRootDatumEquiv σ).weightEquiv
        (characterLattice.congr f.torusIso χ) := by
  change (CommGroupScheme.baseChange (Spec.map (CommRingCat.ofHom σ.toRingHom))).map
      f.torusIso.inv ≫ characterLattice.baseChange _ p.torus χ =
    characterLattice.baseChange _ q.torus (f.torusIso.inv ≫ χ)
  exact (characterLattice.baseChange_precomp _ _ _).symm

/-- The actual complete pinned comparison of two specified coefficient pullbacks. -/
def baseChangeAlongTowerIso (p : SplitPinning G) (σ : k ≃+* K) (τ : K ≃+* L) :
    Iso ((p.baseChangeAlong σ).baseChangeAlong τ)
      (p.baseChangeAlong (σ.trans τ)) := by
  letI : Algebra k K := σ.toRingHom.toAlgebra
  letI : Algebra K L := τ.toRingHom.toAlgebra
  letI : Algebra k L := (σ.trans τ).toRingHom.toAlgebra
  letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.IsAlgebraic k K := equivalence_algebraic σ
  letI : Algebra.IsAlgebraic K L := equivalence_algebraic τ
  letI : Algebra.IsAlgebraic k L := equivalence_algebraic (σ.trans τ)
  exact p.baseChangeTowerIso (K := K) (L := L)

@[simp] theorem baseChangeAlongTowerIso_indexEquiv (p : SplitPinning G)
    (σ : k ≃+* K) (τ : K ≃+* L) :
    (p.baseChangeAlongTowerIso σ τ).indexEquiv = Equiv.refl _ := rfl

theorem baseChangeAlongTowerIso_groupIso (p : SplitPinning G)
    (σ : k ≃+* K) (τ : K ≃+* L) :
    (p.baseChangeAlongTowerIso σ τ).groupIso =
      Descent.pullbackComparison
        (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (Spec.map (CommRingCat.ofHom τ.toRingHom))
        (Spec.map (CommRingCat.ofHom (σ.trans τ).toRingHom))
        (by rw [← Spec.map_comp]; rfl) G := rfl

theorem baseChangeAlongTowerIso_torusIso (p : SplitPinning G)
    (σ : k ≃+* K) (τ : K ≃+* L) :
    (p.baseChangeAlongTowerIso σ τ).torusIso =
      Descent.commPullbackComparison
        (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (Spec.map (CommRingCat.ofHom τ.toRingHom))
        (Spec.map (CommRingCat.ofHom (σ.trans τ).toRingHom))
        (by rw [← Spec.map_comp]; rfl) p.torus := rfl

theorem baseChangeAlongTowerIso_character (p : SplitPinning G)
    (σ : k ≃+* K) (τ : K ≃+* L) (χ : characterLattice p.torus) :
    characterLattice.congr (p.baseChangeAlongTowerIso σ τ).torusIso
        (((p.baseChangeAlong σ).baseChangeAlongRootDatumEquiv τ).weightEquiv
          ((p.baseChangeAlongRootDatumEquiv σ).weightEquiv χ)) =
      (p.baseChangeAlongRootDatumEquiv (σ.trans τ)).weightEquiv χ := by
  exact Descent.characterBaseChange_tower_inv
    (Spec.map (CommRingCat.ofHom σ.toRingHom))
    (Spec.map (CommRingCat.ofHom τ.toRingHom))
    (Spec.map (CommRingCat.ofHom (σ.trans τ).toRingHom))
    (by rw [← Spec.map_comp]; rfl) p.torus χ

end RingEquiv

section Automorphism
variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

theorem semilinearPinnedIso_character (σ : k ≃+* k) (e : p.basedRootDatumAut)
    (χ : characterLattice p.torus) :
    characterLattice.congr (p.semilinearPinnedIso σ e).torusIso
        ((p.baseChangeAlongRootDatumEquiv σ).weightEquiv χ) =
      e.val.weightEquiv χ := by
  have h := (p.baseChangeAlong σ).isoOfRootDatumEquiv_character p
    (p.semilinearRootDatumEquiv σ e) (p.semilinearRootDatumEquiv_simple_iff σ e)
  have hχ := DFunLike.congr_fun h
    ((p.baseChangeAlongRootDatumEquiv σ).weightEquiv χ)
  change characterLattice.congr (p.semilinearPinnedIso σ e).torusIso
      ((p.baseChangeAlongRootDatumEquiv σ).weightEquiv χ) =
    e.val.weightEquiv ((p.baseChangeAlongRootDatumEquiv σ).weightEquiv.symm
      ((p.baseChangeAlongRootDatumEquiv σ).weightEquiv χ)) at hχ
  exact hχ.trans (congrArg e.val.weightEquiv
    ((p.baseChangeAlongRootDatumEquiv σ).weightEquiv.symm_apply_apply χ))

@[simp] theorem semilinearPinnedIso_indexEquiv (σ : k ≃+* k)
    (e : p.basedRootDatumAut) :
    (p.semilinearPinnedIso σ e).indexEquiv = e.val.indexEquiv :=
  (p.baseChangeAlong σ).isoOfRootDatumEquiv_indexEquiv p _ _

/-- Semilinear pinned lifts compose through the canonical actual tower comparison.
The ring equivalence `σ.trans τ` applies σ first, and the based action applies e first. -/
theorem semilinearPinnedIso_comp (σ τ : k ≃+* k) (e d : p.basedRootDatumAut) :
    (p.baseChangeAlongTowerIso σ τ).trans
        (p.semilinearPinnedIso (σ.trans τ) (d * e)) =
      ((p.semilinearPinnedIso σ e).baseChangeAlong τ).trans
        (p.semilinearPinnedIso τ d) := by
  apply Iso.ext_torus_index
  · apply ((p.baseChangeAlong σ).baseChangeAlong τ).isSplitTorus.iso_ext_of_character_congr
    ext χ
    obtain ⟨ψ, rfl⟩ :=
      ((p.baseChangeAlong σ).baseChangeAlongRootDatumEquiv τ).weightEquiv.surjective χ
    obtain ⟨χ, rfl⟩ := (p.baseChangeAlongRootDatumEquiv σ).weightEquiv.surjective ψ
    rw [Iso.trans_character, Iso.trans_character, baseChangeAlongTowerIso_character,
      semilinearPinnedIso_character, Iso.baseChangeAlong_character,
      semilinearPinnedIso_character, semilinearPinnedIso_character]
    rfl
  · ext a
    simp only [Iso.trans, baseChangeAlongTowerIso_indexEquiv,
      Iso.baseChangeAlong_indexEquiv, semilinearPinnedIso_indexEquiv]
    rfl

/-- The same composition law on actual ambient group schemes. -/
theorem semilinearPinnedIso_comp_groupIso (σ τ : k ≃+* k)
    (e d : p.basedRootDatumAut) :
    (p.baseChangeAlongTowerIso σ τ).groupIso ≪≫
        (p.semilinearPinnedIso (σ.trans τ) (d * e)).groupIso =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).mapIso
          (p.semilinearPinnedIso σ e).groupIso ≪≫
        (p.semilinearPinnedIso τ d).groupIso :=
  congrArg (fun f => f.groupIso) (p.semilinearPinnedIso_comp σ τ e d)

end Automorphism
end Langlands.GroupScheme.SplitPinning
