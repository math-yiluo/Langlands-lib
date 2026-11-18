import Langlands.GroupScheme.Reductive.AffineWeilChartCombination
import Langlands.GroupScheme.Reductive.AffineWeilPairEtaleDescentStatement
import Langlands.GroupScheme.Reductive.AffineWeilPairSingleChartDescentStatement
import Langlands.GroupScheme.Reductive.WeilFactorUniquenessReduction
import Langlands.GroupScheme.Reductive.SeparablyClosedAlmostSimpleAbsoluteProof
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction
import Langlands.GroupScheme.AffineWeilBaseChange
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Reduction of étale pair descent to descent along one étale cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Langlands.GroupScheme

/-- Étale base change preserves almost simple geometric fibres. -/
theorem isAlmostSimple_geometricFiber_baseChange_of_etale {S T : Scheme.{u}} (b : T ⟶ S)
    [Etale b] {G : GroupScheme S} (hG : ∀ s, IsAlmostSimple (geometricFiber G s)) (t : T) :
    IsAlmostSimple (geometricFiber ((GroupScheme.baseChange b).obj G) t) := by
  let k := S.residueField (b t)
  let K := T.residueField t
  letI : Algebra k K := (b.residueFieldMap t).hom.toAlgebra
  haveI : Algebra.IsSeparable k K := inferInstance
  haveI : Algebra.IsAlgebraic k K := inferInstance
  letI : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  haveI : IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => ((algebraicClosureEmbedding k K).commutes x).symm)
  haveI : Algebra.IsAlgebraic k (AlgebraicClosure K) := Algebra.IsAlgebraic.trans k K _
  haveI : Algebra.IsAlgebraic (AlgebraicClosure k) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := k) (AlgebraicClosure k)
  have habs : IsAbsolutelyAlmostSimple (geometricFiber G (b t)) :=
    separablyClosedAlmostSimpleAbsolute _ _ (hG (b t))
  have hext := (habs.baseChange_of_algebraicExtension (K := AlgebraicClosure K)).1
  exact hext.of_iso ((RelativeLevi.geometricFiberBaseChangeIso b t).app G).symm

/-- Finitely many members of a covering family of étale algebras already cover. -/
theorem exists_finset_etale_cover {A : Type u} [CommRing A] {ι : Type u}
    (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
    [∀ i, Algebra.Etale A (R i)]
    (hcov : ∀ s : Spec (CommRingCat.of A), ∃ i,
      s ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (R i))))) :
    ∃ F : Finset ι, ∀ s : Spec (CommRingCat.of A), ∃ i ∈ F,
      s ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (R i)))) := by
  have hopen : ∀ i, IsOpen (Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (R i))))) := by
    intro i
    haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap A (R i)))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
    exact (Spec.map (CommRingCat.ofHom (algebraMap A (R i)))).isOpenMap.isOpen_range
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun i => Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (R i))))) hopen
    (fun s _ => Set.mem_iUnion.mpr (hcov s))
  refine ⟨F, fun s => ?_⟩
  have hs := hF (Set.mem_univ s)
  simp only [Set.mem_iUnion] at hs
  obtain ⟨i, hi, h⟩ := hs
  exact ⟨i, hi, h⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The right-hand coefficient of an étale base extension is étale over its left factor. -/
theorem etale_tensor_right (A R B : Type u) [CommRing A] [CommRing R] [CommRing B]
    [Algebra A R] [Algebra A B] [Algebra.Etale A R] : Algebra.Etale B (R ⊗[A] B) := by
  let e : B ⊗[A] R ≃ₐ[B] R ⊗[A] B :=
    { (Algebra.TensorProduct.comm A B R).toRingEquiv with
      commutes' := fun b => by
        change Algebra.TensorProduct.comm A B R (b ⊗ₜ 1) = 1 ⊗ₜ b
        rw [Algebra.TensorProduct.comm_tmul] }
  exact Algebra.Etale.of_equiv e

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The base change of a group over `Spec B` along `Spec (R ⊗[A] B) → Spec B` for an étale
`A`-algebra `R` is reductive with almost simple geometric fibres when the group is. -/
theorem factor_reductive_almostSimple {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (R : Type u) [CommRing R] [Algebra A R] [Algebra.Etale A R]
    {G' : GroupScheme (Spec (CommRingCat.of B))} (hred : IsReductive G')
    (hsimple : ∀ t, IsAlmostSimple (geometricFiber G' t)) :
    IsReductive ((GroupScheme.baseChange (Spec.algebraMap B (R ⊗[A] B))).obj G') ∧
      ∀ t, IsAlmostSimple (geometricFiber
        ((GroupScheme.baseChange (Spec.algebraMap B (R ⊗[A] B))).obj G') t) := by
  haveI : Algebra.Etale B (R ⊗[A] B) := etale_tensor_right A R B
  haveI : Etale (Spec.algebraMap B (R ⊗[A] B)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  exact ⟨hred.baseChange _, isAlmostSimple_geometricFiber_baseChange_of_etale _ hsimple⟩


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Recovery of a local pair from a global one.** If `G ≅ R_{B/A}(G')` and, over an étale
`A`-algebra `R`, `G_R ≅ R_{B'/R}(G₁)`, both pairs reductive with almost simple geometric
fibres, then `R ⊗[A] B ≃ B'` and `G'` base changes to `G₁`, by uniqueness of Weil pairs. -/
theorem exists_chart_comparison (hR : WeilFactorIdempotentRigidityStatement.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [Module.Projective A B] [Algebra.Etale A B]
    {G' : GroupScheme (Spec (CommRingCat.of B))} [IsAffine G'.X.left]
    [LocallyOfFiniteType G'.X.hom] (hred' : IsReductive G')
    (hsimple' : ∀ t, IsAlmostSimple (geometricFiber G' t))
    {G : GroupScheme (Spec (CommRingCat.of A))} (Φ : G ≅ AffineWeil.groupScheme A B G')
    (R : Type u) [CommRing R] [Algebra A R] [Algebra.Etale A R]
    (B' : Type u) [CommRing B'] [Algebra R B'] [Module.Finite R B'] [Module.Projective R B']
    [Algebra.Etale R B']
    {G₁ : GroupScheme (Spec (CommRingCat.of B'))} [IsAffine G₁.X.left]
    [LocallyOfFiniteType G₁.X.hom] (hred₁ : IsReductive G₁)
    (hsimple₁ : ∀ t, IsAlmostSimple (geometricFiber G₁ t))
    (ψ : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap A R)))).obj G ≅
      AffineWeil.groupScheme R B' G₁) :
    ∃ e : R ⊗[A] B ≃ₐ[R] B',
      Nonempty ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom
        ((e : R ⊗[A] B →+* B').comp
          (Algebra.TensorProduct.includeRight : B →ₐ[A] R ⊗[A] B).toRingHom)))).obj G' ≅
        G₁) := by
  have hfac := factor_reductive_almostSimple (A := A) R hred' hsimple'
  let Ψ : AffineWeil.groupScheme R (R ⊗[A] B) (AffineWeil.BaseChange.factor A B R G') ≅
      AffineWeil.groupScheme R B' G₁ :=
    (AffineWeil.BaseChange.iso A B R G').symm ≪≫
      (GroupScheme.baseChange (Spec.algebraMap A R)).mapIso Φ.symm ≪≫ ψ
  obtain ⟨α, ⟨f⟩⟩ := WeilFactor.exists_baseChange_iso_of_weilRestriction_iso hR hfac.1 hfac.2
    hred₁ hsimple₁ Ψ
  refine ⟨α.symm, ⟨?_⟩⟩
  have hcomp : Spec.map (CommRingCat.ofHom ((α.symm : R ⊗[A] B →+* B').comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] R ⊗[A] B).toRingHom)) =
      Spec.map (CommRingCat.ofHom (α.symm : R ⊗[A] B →+* B')) ≫
        Spec.algebraMap B (R ⊗[A] B) := by
    rw [Spec.algebraMap, ← Spec.map_comp]
    rfl
  have hid : Spec.map (CommRingCat.ofHom (α.symm : R ⊗[A] B →+* B')) ≫
      Spec.map (CommRingCat.ofHom (α : B' →+* R ⊗[A] B)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    simp
  exact eqToIso (congrArg (fun m => (GroupScheme.baseChange m).obj G') hcomp) ≪≫
    baseChangeCompIso (Spec.algebraMap B (R ⊗[A] B))
      (Spec.map (CommRingCat.ofHom (α.symm : R ⊗[A] B →+* B'))) G' ≪≫
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (α.symm : R ⊗[A] B →+* B')))).mapIso
      f.symm ≪≫
    (baseChangeCompIso (Spec.map (CommRingCat.ofHom (α : B' →+* R ⊗[A] B)))
      (Spec.map (CommRingCat.ofHom (α.symm : R ⊗[A] B →+* B'))) G₁).symm ≪≫
    eqToIso (congrArg (fun m => (GroupScheme.baseChange m).obj G₁) hid) ≪≫
    baseChangeIdIso G₁


/-- A global coefficient algebra is surjective over the base when it recovers surjective
local coefficient algebras on a covering family of charts. -/
theorem surjective_of_charts {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type u} (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
    (B' : ι → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra (R i) (B' i)]
    (hcov : ∀ s : Spec (CommRingCat.of A), ∃ i,
      s ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (R i)))))
    (hsurj : ∀ i, Surjective (Spec.map (CommRingCat.ofHom (algebraMap (R i) (B' i)))))
    (e : ∀ i, R i ⊗[A] B ≃ₐ[R i] B' i) :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  constructor
  intro s
  obtain ⟨i, r, rfl⟩ := hcov s
  obtain ⟨x, rfl⟩ := (hsurj i).surj r
  refine ⟨Spec.map (CommRingCat.ofHom (((e i) : R i ⊗[A] B →+* B' i).comp
    (Algebra.TensorProduct.includeRight : B →ₐ[A] R i ⊗[A] B).toRingHom)) x, ?_⟩
  have hring : (((e i) : R i ⊗[A] B →+* B' i).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] R i ⊗[A] B).toRingHom).comp
        (algebraMap A B) = (algebraMap (R i) (B' i)).comp (algebraMap A (R i)) := by
    ext a
    change e i ((1 : R i) ⊗ₜ[A] algebraMap A B a) =
      algebraMap (R i) (B' i) (algebraMap A (R i) a)
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one, ← (e i).commutes]
    rfl
  have hmap : Spec.map (CommRingCat.ofHom (((e i) : R i ⊗[A] B →+* B' i).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] R i ⊗[A] B).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap (R i) (B' i))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (R i))) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hring]
  rw [← Scheme.Hom.comp_apply, hmap, Scheme.Hom.comp_apply]

/-- **Étale pair descent from descent along one étale cover.** Assuming factor rigidity
and the single-cover descent statement, étale-locally given Weil-restriction presentations
with almost simple factors descend. -/
theorem affineWeilPairEtaleDescent_of_singleChart
    (hR : WeilFactorIdempotentRigidityStatement.{u})
    (hS : AffineWeilPairSingleChartDescentStatement.{u}) :
    AffineWeilPairEtaleDescentStatement.{u} := by
  classical
  intro A _ G _ _ ι R _ _ _ B' _ _ _ _ _ G₁ _ _ hcov hsurj hred hsimple hiso
  obtain ⟨F, hF⟩ := exists_finset_etale_cover R hcov
  let RJ : F → Type u := fun j => R j
  let BJ : F → Type u := fun j => B' j
  let HJ : ∀ j : F, GroupScheme (Spec (CommRingCat.of (BJ j))) := fun j => G₁ j
  letI := AffineWeil.ChartCombination.coefficientAlgebra RJ BJ
  haveI : Module.Finite (∀ j, RJ j) (∀ j, BJ j) :=
    AffineWeil.ChartCombination.coefficient_finite RJ BJ
  haveI : Module.Projective (∀ j, RJ j) (∀ j, BJ j) :=
    AffineWeil.ChartCombination.coefficient_projective RJ BJ
  haveI : Algebra.Etale (∀ j, RJ j) (∀ j, BJ j) :=
    AffineWeil.ChartCombination.coefficient_etale RJ BJ
  have hsurjA : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A (∀ j, RJ j)))) :=
    AffineWeil.ChartCombination.surjective_baseMap RJ (fun s => by
      obtain ⟨i, hi, h⟩ := hF s
      exact ⟨⟨i, hi⟩, h⟩)
  have φ := AffineWeil.ChartCombination.combinedIso RJ BJ HJ G (fun j => (hiso j).some)
  obtain ⟨B, _, _, _, _, _, G', _, _, hredG', hsimG', ⟨Φ⟩⟩ :=
    hS A (∀ j, RJ j) hsurjA G (∀ j, BJ j) (AffineWeil.ChartCombination.group BJ HJ)
      (AffineWeil.ChartCombination.isReductive BJ HJ (fun j => hred j))
      (AffineWeil.ChartCombination.isAlmostSimple_geometricFiber BJ HJ (fun j => hsimple j))
      ⟨φ⟩
  have hcmp := fun i => exists_chart_comparison hR hredG' hsimG' Φ (R i) (B' i) (hred i)
    (hsimple i) (hiso i).some
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, G',
    inferInstance, inferInstance, ?_, hredG', hsimG', ⟨Φ⟩, hcmp⟩
  exact surjective_of_charts R B' hcov hsurj (fun i => (hcmp i).choose)


end Langlands.GroupScheme
