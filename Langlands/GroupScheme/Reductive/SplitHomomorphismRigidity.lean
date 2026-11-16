import Langlands.GroupScheme.Reductive.LocalSplitFlatBigCell
import Langlands.GroupScheme.Reductive.LocalSplitCellIsomorphism
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationStatement
import Langlands.GroupScheme.OpenCellGluing

/-! # Homomorphism rigidity from actual split root generators -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- Applying a group homomorphism to a cell applies it to every factor. -/
theorem cellMap_comp_hom (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (fam : J → (Ga R ⟶ G)) {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    (f : G ⟶ H) :
    cellMap i fam neg pos ≫ f.hom.hom =
      cellMap (i ≫ f) (fun α => fam α ≫ f) neg pos := by
  let Ψ : (cellObj R I m n ⟶ G.X) →* (cellObj R I m n ⟶ H.X) :=
    { toFun := fun x => x ≫ f.hom.hom
      map_one' := MonObj.one_comp _
      map_mul' := fun _ _ => MonObj.mul_comp _ _ _ }
  have h := map_comp_cellMap Ψ
    (i' := i ≫ f) (u' := fun α => fam α ≫ f)
    (fun t => by change t ≫ i.hom.hom ≫ f.hom.hom = _; rfl)
    (fun α c => (rootPoint_comp (fam α) f _ c).symm)
    neg pos (𝟙 _)
  simpa only [Ψ, MonoidHom.coe_mk, OneHom.coe_mk, Category.id_comp] using h

/-- Agreement on the torus and an open-cell root family determines a homomorphism.
The target need not be reductive or affine. -/
theorem hom_ext_of_open_cell (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (fam : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i fam neg pos).left]
    {f F : G ⟶ H} (ht : i ≫ f = i ≫ F)
    (hr : ∀ α, fam α ≫ f = fam α ≫ F) : f = F := by
  have := hG.smooth
  have := hG.geometricallyIrreducible
  apply CellGluing.hom_ext_cell (cellUnit R I m n)
    (cellUnit_comp_cellMap i fam neg pos)
  rw [cellMap_comp_hom, cellMap_comp_hom, ht]
  exact congrArg (fun v => cellMap (i ≫ F) v neg pos) (funext hr)

/-- Actual root parametrizations of a full fibrewise root datum determine
homomorphisms from a reductive group over any commutative ring. -/
theorem hom_ext_of_rootParametrizations [IsAffineHom G.X.hom]
    (hG : IsReductive G) (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (hP : IsFibrewiseRootDatumOf I G i P)
    (b : P.Base) (fam : J → (Ga R ⟶ G))
    (hfam : ∀ α, IsRootParametrization i (P.root α) (fam α))
    {f F : G ⟶ H} (ht : i ≫ f = i ≫ F)
    (hr : ∀ α, fam α ≫ f = fam α ≫ F) : f = F := by
  classical
  have : Finite J := hP.finite
  let neg := (Finite.equivFin {α // ¬ b.IsPos α}).symm
  let pos := (Finite.equivFin {α // b.IsPos α}).symm
  have := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b fam hfam neg pos
  exact hom_ext_of_open_cell hG i fam (fun k => (neg k : J))
    (fun k => (pos k : J)) ht hr

/-- Agreement on the torus, the simple-root maps, and the negative-simple
points at minus one. The negative-point condition is retained explicitly. -/
def AgreeOnWeylGenerators (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base) (u : J → (Ga R ⟶ G))
    (f F : G ⟶ H) : Prop :=
  i ≫ f = i ≫ F ∧
  (∀ a ∈ b.support, u a ≫ f = u a ≫ F) ∧
  ∀ a ∈ b.support,
    rootPoint (u (P.reflectionPerm a a)) (𝟙_ _) (-1) ≫ f.hom.hom =
      rootPoint (u (P.reflectionPerm a a)) (𝟙_ _) (-1) ≫ F.hom.hom

variable {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {u : J → (Ga R ⟶ G)} {f F : G ⟶ H}

/-- The two images of every simple Weyl point coincide. -/
theorem AgreeOnWeylGenerators.rootWeylPoint (h : AgreeOnWeylGenerators i P b u f F)
    {a : J} (ha : a ∈ b.support) :
    LocalSplitCell.rootWeylPoint P u a ≫ f.hom.hom =
      LocalSplitCell.rootWeylPoint P u a ≫ F.hom.hom := by
  have hs : rootPoint (u a) (𝟙_ _) 1 ≫ f.hom.hom =
      rootPoint (u a) (𝟙_ _) 1 ≫ F.hom.hom := by
    rw [← rootPoint_comp, ← rootPoint_comp, h.2.1 a ha]
  simp only [LocalSplitCell.rootWeylPoint, weylPoint, MonObj.mul_comp,
    h.2.2 a ha, hs]

/-- Equality on the Weyl generators propagates along every simple-root word. -/
theorem AgreeOnWeylGenerators.wordConj (h : AgreeOnWeylGenerators i P b u f F)
    (l : List J) (hl : ∀ a ∈ l, a ∈ b.support) {w : Ga R ⟶ G}
    (hw : w ≫ f = w ≫ F) :
    LocalSplitCell.wordConj P u l w ≫ f = LocalSplitCell.wordConj P u l w ≫ F := by
  apply hom_ext_rootPoint
  intro Z c
  induction l with
  | nil => rw [LocalSplitCell.wordConj, hw]
  | cons a l ih =>
    have hn : G.constantPoint (LocalSplitCell.rootWeylPoint P u a) Z ≫ f.hom.hom =
        G.constantPoint (LocalSplitCell.rootWeylPoint P u a) Z ≫ F.hom.hom := by
      rw [← toUnit_comp_eq_constantPoint, Category.assoc, Category.assoc,
        h.rootWeylPoint (hl a List.mem_cons_self)]
    have ht := ih (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    simp only [LocalSplitCell.wordConj, rootPoint_comp, GroupScheme.comp_innerIso_hom,
      MonObj.mul_comp, GrpObj.inv_comp]
    simp only [rootPoint_comp] at ht
    rw [hn, ht]

/-- The whole Weyl family has equal images. -/
theorem AgreeOnWeylGenerators.weylFamily (h : AgreeOnWeylGenerators i P b u f F)
    (W : ∀ α, SimpleWord P b α) (α : J) :
    LocalSplitCell.weylFamily P W u α ≫ f =
      LocalSplitCell.weylFamily P W u α ≫ F :=
  h.wordConj (W α).word (W α).word_mem (h.2.1 _ (W α).simple_mem)

/-- Weyl-normalized simple-root maps, the torus map and the negative-simple
points at minus one determine every homomorphism, over an arbitrary ring. -/
theorem hom_ext_of_weylGenerators [DecidableEq I] [IsAffineHom G.X.hom]
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (W : ∀ α, SimpleWord P b α)
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a))
    (hw : ∀ a ∈ b.support, IsWeylPoint i (LocalSplitCell.rootWeylPoint P u a) (P.reflection a))
    (h : AgreeOnWeylGenerators i P b u f F) : f = F :=
  hom_ext_of_rootParametrizations hG i hmax P hP b
    (LocalSplitCell.weylFamily P W u) (isRootParametrization_weylFamily hu hw W)
    h.1 (h.weylFamily W)

end Langlands.GroupScheme.LocalSplitCell
