import Langlands.GroupScheme.SimplyConnected.FactorialCellRing
import Langlands.GroupScheme.Reductive.AffineSplitRootSubgroupSpanning
import Langlands.GroupScheme.Reductive.AffineSplitRootPairLaws
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationProof
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationField
import Langlands.GroupScheme.Reductive.LocalSplitFieldComparison

/-! # Coordinate split data and big-cell charts over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitFactorial

open LocalSplitCell

/-- Coordinate split data of a reductive group `G` over a field `k`: a closed coordinate split
torus, maximal on the fibre, a finite reduced coordinate root datum of it with a base, and root
parametrizations which are Weyl-normalized at the simple roots. -/
structure CellData (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] where
  /-- The coordinate index of the torus. -/
  I : Type u
  [fintypeI : Fintype I]
  [decEqI : DecidableEq I]
  /-- The torus. -/
  i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G
  isReductive : IsReductive G
  isClosedSubgroup : IsClosedSubgroup i
  isFibrewiseMaximal : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i
  /-- The root index. -/
  J : Type u
  /-- The root datum. -/
  P : RootDatum J (I → ℤ) (I → ℤ)
  hP : IsFibrewiseRootDatumOf I G i P
  /-- The base. -/
  b : P.Base
  /-- The root parametrizations. -/
  u : J → (Ga k ⟶ G)
  hu : ∀ α, IsRootParametrization i (P.root α) (u α)
  weyl : ∀ a ∈ b.support,
    IsWeylPoint i (weylPoint (u a) (u (P.reflectionPerm a a))) (P.reflection a)

attribute [instance] CellData.fintypeI CellData.decEqI

namespace CellData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : CellData k G)

instance finiteJ : Finite D.J := D.hP.finite

instance isReduced : D.P.IsReduced := D.hP.isReduced

/-- The big-cell maps of this data are open immersions. -/
theorem isOpenImmersion_cellMap {m n : ℕ} (neg : Fin m ≃ {α // ¬ D.b.IsPos α})
    (pos : Fin n ≃ {α // D.b.IsPos α}) :
    IsOpenImmersion (cellMap D.i D.u (fun r => (neg r : D.J)) (fun r => (pos r : D.J))).left :=
  (affineSplitRootSubgroupSpanning k G D.isReductive D.I D.i D.isClosedSubgroup
    D.isFibrewiseMaximal D.J D.P D.hP D.u D.hu).1 D.b m n neg pos

/-! ### Charts -/

variable {m n : ℕ} (neg : Fin m ≃ {α // ¬ D.b.IsPos α}) (pos : Fin n ≃ {α // D.b.IsPos α})

/-- The big-cell chart `Spec k[v, w, t, t⁻¹] ⟶ G` for the given enumerations. -/
def chart : cellSpec k D.I m n ⟶ G.X :=
  cellCoordHom k D.I m n ≫ cellMap D.i D.u (fun r => (neg r : D.J)) (fun r => (pos r : D.J))

instance isOpenImmersion_chart : IsOpenImmersion (D.chart neg pos).left := by
  have h1 : IsOpenImmersion (cellMap D.i D.u (fun r => (neg r : D.J))
      (fun r => (pos r : D.J))).left := D.isOpenImmersion_cellMap neg pos
  have h2 : IsIso (cellCoordHom k D.I m n).left :=
    (inferInstance : IsIso ((Over.forget _).map (cellCoordHom k D.I m n)))
  change IsOpenImmersion ((cellCoordHom k D.I m n).left ≫ _)
  infer_instance

theorem comp_chart {W : Over (Spec (CommRingCat.of k))} (z : W ⟶ cellSpec k D.I m n) :
    z ≫ D.chart neg pos =
      cellPoint D.i D.u (fun r => (neg r : D.J)) (fun r => (pos r : D.J)) W
        (fun r => pointRing z (negVar k D.I m n r)) (z ≫ specTorus k D.I m n)
        (fun r => pointRing z (posVar k D.I m n r)) := by
  rw [chart, ← Category.assoc, comp_cellMap]
  have h := coordTriple_comp_cellCoordHom z
  simp only [LocalSplitBigCell.coordTriple, Prod.mk.injEq] at h
  rw [h.1, h.2.1, h.2.2]

/-! ### Subgroups directly spanned by root groups -/

/-- A set of roots that is closed under sums and contains no opposite pair. -/
def IsClosedRootSet (Ψ : Set D.J) : Prop :=
  (∀ a ∈ Ψ, ∀ c ∈ Ψ, ∀ d : D.J, D.P.root d = D.P.root a + D.P.root c → d ∈ Ψ) ∧
    ∀ a ∈ Ψ, ∀ c ∈ Ψ, D.P.root a + D.P.root c ≠ 0

theorem exists_rootSpan {Ψ : Set D.J} (hΨ : D.IsClosedRootSet Ψ) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
      (∀ (Z : Over (Spec (CommRingCat.of k)))
          (t : Z ⟶ (splitTorus (Spec (CommRingCat.of k)) D.I).X) (h : Z ⟶ H.X),
          ∃ h' : Z ⟶ H.X,
            (t ≫ D.i.hom.hom) * (h ≫ j.hom.hom) * (t ≫ D.i.hom.hom)⁻¹ = h' ≫ j.hom.hom) ∧
      ∀ (n : ℕ) (e : Fin n ≃ Ψ),
        ∃ φ : (VectorGroup.groupScheme (CommRingCat.of k) n).X ≅ H.X,
          φ.hom ≫ j.hom.hom =
            orderedProduct D.u (fun r => ((e r : Ψ) : D.J)) _
              (VectorGroup.coordinates (CommRingCat.of k) n _ (𝟙 _)).toAdd := by
  obtain ⟨H, j, -, -, ht, -, he⟩ := (affineSplitRootSubgroupSpanning k G D.isReductive D.I D.i
    D.isClosedSubgroup D.isFibrewiseMaximal D.J D.P D.hP D.u D.hu).2.2.1 Ψ hΨ.1 hΨ.2
  exact ⟨H, j, ht, he⟩

/-- The group directly spanned by the root groups of a closed set of roots. -/
def rootSpanGroup {Ψ : Set D.J} (hΨ : D.IsClosedRootSet Ψ) :
    GroupScheme (Spec (CommRingCat.of k)) :=
  Classical.choose (D.exists_rootSpan hΨ)

/-- Its inclusion. -/
def rootSpanHom {Ψ : Set D.J} (hΨ : D.IsClosedRootSet Ψ) : D.rootSpanGroup hΨ ⟶ G :=
  Classical.choose (Classical.choose_spec (D.exists_rootSpan hΨ))

theorem rootSpanHom_spec {Ψ : Set D.J} (hΨ : D.IsClosedRootSet Ψ) :
    (∀ (Z : Over (Spec (CommRingCat.of k)))
        (t : Z ⟶ (splitTorus (Spec (CommRingCat.of k)) D.I).X) (h : Z ⟶ (D.rootSpanGroup hΨ).X),
        ∃ h' : Z ⟶ (D.rootSpanGroup hΨ).X,
          (t ≫ D.i.hom.hom) * (h ≫ (D.rootSpanHom hΨ).hom.hom) * (t ≫ D.i.hom.hom)⁻¹ =
            h' ≫ (D.rootSpanHom hΨ).hom.hom) ∧
      ∀ (n : ℕ) (e : Fin n ≃ Ψ),
        ∃ φ : (VectorGroup.groupScheme (CommRingCat.of k) n).X ≅ (D.rootSpanGroup hΨ).X,
          φ.hom ≫ (D.rootSpanHom hΨ).hom.hom =
            orderedProduct D.u (fun r => ((e r : Ψ) : D.J)) _
              (VectorGroup.coordinates (CommRingCat.of k) n _ (𝟙 _)).toAdd :=
  Classical.choose_spec (Classical.choose_spec (D.exists_rootSpan hΨ))

/-- The subgroup functor directly spanned by the root groups of a closed set of roots. -/
def rootSpan {Ψ : Set D.J} (hΨ : D.IsClosedRootSet Ψ) : SubgroupFunctor G :=
  SubgroupFunctor.range (D.rootSpanHom hΨ)

theorem orderedProduct_mem_rootSpan {Ψ : Set D.J} (hΨ : D.IsClosedRootSet Ψ) {n : ℕ}
    (e : Fin n ≃ Ψ) (Z : Over (Spec (CommRingCat.of k))) (c : Fin n → Γ(Z.left, ⊤)) :
    orderedProduct D.u (fun r => ((e r : Ψ) : D.J)) Z c ∈ (D.rootSpan hΨ).carrier Z := by
  obtain ⟨φ, hφ⟩ := (D.rootSpanHom_spec hΨ).2 n e
  let x := (VectorGroup.coordinates (CommRingCat.of k) n Z).symm (Multiplicative.ofAdd c)
  refine ⟨x ≫ φ.hom, ?_⟩
  change (x ≫ φ.hom) ≫ (D.rootSpanHom hΨ).hom.hom = _
  rw [Category.assoc, hφ, comp_orderedProduct]
  congr 1
  funext r
  have h := VectorGroup.coordinates_comp x (𝟙 _)
  rw [Category.comp_id] at h
  rw [← congrFun h r, MulEquiv.apply_symm_apply]
  rfl

theorem exists_eq_orderedProduct {Ψ : Set D.J} (hΨ : D.IsClosedRootSet Ψ) {n : ℕ}
    (e : Fin n ≃ Ψ) {Z : Over (Spec (CommRingCat.of k))} {g : Z ⟶ G.X}
    (hg : g ∈ (D.rootSpan hΨ).carrier Z) :
    ∃ c : Fin n → Γ(Z.left, ⊤), orderedProduct D.u (fun r => ((e r : Ψ) : D.J)) Z c = g := by
  obtain ⟨h, hh⟩ := SubgroupFunctor.mem_range.1 hg
  subst hh
  obtain ⟨φ, hφ⟩ := (D.rootSpanHom_spec hΨ).2 n e
  refine ⟨(VectorGroup.coordinates (CommRingCat.of k) n Z (h ≫ φ.inv)).toAdd, ?_⟩
  have h1 := VectorGroup.coordinates_comp (h ≫ φ.inv) (𝟙 _)
  rw [Category.comp_id] at h1
  rw [h1, ← comp_orderedProduct, ← hφ, ← Category.assoc, Category.assoc h, Iso.inv_hom_id,
    Category.comp_id]

theorem rootPoint_mem_rootSpan {Ψ : Set D.J} (hΨ : D.IsClosedRootSet Ψ) {α : D.J} (hα : α ∈ Ψ)
    (Z : Over (Spec (CommRingCat.of k))) (c : Γ(Z.left, ⊤)) :
    rootPoint (D.u α) Z c ∈ (D.rootSpan hΨ).carrier Z := by
  classical
  have : Fintype Ψ := Fintype.ofFinite Ψ
  let e : Fin (Fintype.card Ψ) ≃ Ψ := (Fintype.equivFin Ψ).symm
  let r₀ := e.symm ⟨α, hα⟩
  have h := D.orderedProduct_mem_rootSpan hΨ e Z (Function.update 0 r₀ c)
  rw [orderedProduct, LocalWeylNormalization.list_prod_ofFn_eq _ r₀] at h
  · simpa [r₀] using h
  · intro r hr
    rw [Function.update_of_ne hr, Pi.zero_apply, rootPoint_zero]

theorem torus_conj_mem_rootSpan {Ψ : Set D.J} (hΨ : D.IsClosedRootSet Ψ)
    {Z : Over (Spec (CommRingCat.of k))} (t : Z ⟶ (splitTorus (Spec (CommRingCat.of k)) D.I).X)
    {g : Z ⟶ G.X} (hg : g ∈ (D.rootSpan hΨ).carrier Z) :
    (t ≫ D.i.hom.hom) * g * (t ≫ D.i.hom.hom)⁻¹ ∈ (D.rootSpan hΨ).carrier Z := by
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.1 hg
  obtain ⟨h', hh'⟩ := (D.rootSpanHom_spec hΨ).1 Z t h
  exact SubgroupFunctor.mem_range.2 ⟨h', hh'.symm⟩

end CellData

end Langlands.GroupScheme.SplitFactorial
