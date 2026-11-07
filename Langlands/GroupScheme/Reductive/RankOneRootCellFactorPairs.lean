import Langlands.GroupScheme.Reductive.SplitRankOneRootCellProof
import Langlands.GroupScheme.Rational.RootFactorPairReflection
import Langlands.GroupScheme.Rational.RootSubgroupConjugation

/-! # Opposite factor pairs from a rank-one open cell -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RankOneRootCellRelation

open RootCell (crd)

variable {k : Type u} [Field k]

section RootMembership

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (α : characterLattice T) (x : Ga k ⟶ G)
  (hx : ∀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ T.X)
    (v : Z ⟶ (Ga k).X),
    (t ≫ i.hom.hom) * (v ≫ x.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
      VectorGroup.weightPointAction α Z t v ≫ x.hom.hom)

include hx

/-- Character equivariance of an additive parametrization supplies the actual
affine-line extension defining the root subgroup, on every test scheme. -/
theorem comp_mem_rootSubgroup {Z : Over (Spec (CommRingCat.of k))}
    (v : Z ⟶ (Ga k).X) :
    v ≫ x.hom.hom ∈ (RelativeRoot.subgroup i α).carrier Z := by
  let A := AffineLine.scheme (Spec (CommRingCat.of k))
  let f : Z ⊗ A ⟶ (Ga k).X :=
    gpt (AffineLine.homEquiv _ (snd Z A) * (fst Z A).left.appTop (crd v))
  refine ⟨f ≫ x.hom.hom, ?_, ?_⟩
  · have hf :
        Z ◁ ((CommGroupScheme.groupHom α).hom.hom ≫
          AffineLine.unitInclusion _) ≫ f =
        VectorGroup.weightPointAction α _ (snd Z T.X) (fst Z T.X ≫ v) := by
      rw [← gpt_crd (VectorGroup.weightPointAction α _ _ _),
        crd_weightPointAction, RootCell.crd_comp]
      dsimp only [f]
      rw [comp_gpt, map_mul, ← AffineLine.homEquiv_comp,
        whiskerLeft_snd, ← Category.assoc, AffineLine.homEquiv_comp_unitInclusion]
      congr 2
      have hfst := whiskerLeft_fst Z
        ((CommGroupScheme.groupHom α).hom.hom ≫ AffineLine.unitInclusion _)
      simpa only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
        congrArg (fun g : Z ⊗ T.X ⟶ Z => g.left.appTop (crd v)) hfst
    change _ ≫ (f ≫ x.hom.hom) = RelativeRoot.orbit i (v ≫ x.hom.hom)
    rw [← Category.assoc, hf, RelativeRoot.orbit,
      AutomorphicAction.conjugation_act, ← Category.assoc, hx]
  · rw [Dynamic.evalZero_comp]
    have hf0 : Dynamic.evalZero f = 1 := by
      dsimp only [Dynamic.evalZero, f]
      rw [comp_gpt, map_mul, ← AffineLine.homEquiv_comp,
        lift_snd, AffineLine.homEquiv_comp_zeroSection, zero_mul, gpt_zero]
    rw [hf0, MonObj.one_comp]

end RootMembership

namespace WeylData

variable (D : WeylData k)

/-- Rescale the positive root parametrization by a base unit. -/
def scalePositive (c : Γ((base k).left, ⊤)ˣ) : WeylData k where
  G := D.G
  T := D.T
  i := D.i
  xp := (scaleIso c).hom ≫ D.xp
  xm := D.xm
  α := D.α
  hxp Z t a := by
    simp only [Grp.comp_hom_hom, ← Category.assoc, comp_scaleIso_hom]
    rw [← CellData.A, ← CellData.A, ← CellData.I, CellData.I_mul_A,
      mul_inv_cancel_right, crd_weightPointAction]
    congr 1
    ring
  hxm := D.hxm
  open_cell := by
    have := D.open_cell
    have he : Dynamic.tripleCellMultiplication D.xm D.i ((scaleIso c).hom ≫ D.xp) =
        (_ ◁ (_ ◁ (scaleIso c).hom.hom.hom)) ≫ D.cellMul := by
      simp only [CellData.cellMul, Dynamic.tripleCellMultiplication,
        SubgroupFunctor.cellMultiplication, MonObj.comp_mul,
        whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, Grp.comp_hom_hom]
    rw [he, Over.comp_left]
    have : IsIso (_ ◁ (_ ◁ (scaleIso c).hom.hom.hom)).left :=
      (inferInstance : IsIso ((Over.forget _).map
        ((Ga k).X ◁ (D.T.X ◁ (scaleIso c).hom.hom.hom))))
    infer_instance
  h := D.h
  pair := D.pair
  n := D.n
  hn := D.hn
  hn2 := D.hn2
  irreducible := D.irreducible

/-- Every nonzero base coordinate, multiplied by the Weyl point, lies in the open cell. -/
theorem inCell_A_unit_mul_N (c : Γ((base k).left, ⊤)ˣ) :
    D.InCell (D.A (c : Γ((base k).left, ⊤)) * D.N (base k)) := by
  have h := (D.scalePositive c).inCell_A_one_mul_N
  obtain ⟨y, t, x, he⟩ := ((D.scalePositive c).inCell_iff _).mp h
  have hA {Z : Over (Spec (CommRingCat.of k))} (v : Γ(Z.left, ⊤)) :
      (D.scalePositive c).A v =
        D.A (pb Z (c : Γ((base k).left, ⊤)) * v) := by
    simp only [CellData.A, scalePositive, Grp.comp_hom_hom, ← Category.assoc,
      comp_scaleIso_hom, crd_gpt]
  have hp : pb (base k) (c : Γ((base k).left, ⊤)) = c := by
    change (toBase (base k)).left.appTop _ = _
    have hb : toBase (base k) = 𝟙 (base k) := (toBase_eq _).symm
    rw [hb]
    rfl
  rw [CellData.cellPt] at he
  rw [hA, hp, mul_one, hA, hp] at he
  exact (D.inCell_iff _).mpr ⟨y, t, (c : Γ((base k).left, ⊤)) * x, he⟩

variable [Mono D.i.hom.hom.left]

/-- The open-cell factorization of a nonzero positive root point times the
Weyl point yields an actual normalizing opposite factor pair. -/
theorem exists_oppositeFactorPair (c : Γ((base k).left, ⊤)ˣ) :
    ∃ p, RelativeRoot.IsOppositeFactorPair D.i D.α
      (D.A (c : Γ((base k).left, ⊤))) p := by
  obtain ⟨y, t, z, he⟩ := (D.inCell_iff _).mp (D.inCell_A_unit_mul_N c)
  simp only [N, constantPoint_self, CellData.cellPt] at he
  let n : normalizerPoints D.i := ⟨D.n, ⟨_, D.hn⟩⟩
  have hw : weylAction D.i n D.α = -D.α := by
    rw [weylAction_eq D.i (n := n)
      (σ := latticeReflectionIso D.α D.h D.pair) D.hn D.α]
    change characterAut (latticeReflectionIso D.α D.h D.pair) D.α = _
    rw [characterAut_latticeReflectionIso, D.pair, two_zsmul]
    abel
  have hA : D.A z ∈ (RelativeRoot.subgroup D.i D.α).carrier (base k) :=
    comp_mem_rootSubgroup D.i D.α D.xp D.hxp (gpt z)
  have hB : D.B y ∈ (RelativeRoot.subgroup D.i (-D.α)).carrier (base k) :=
    comp_mem_rootSubgroup D.i (-D.α) D.xm D.hxm (gpt y)
  have hconj := RelativeRoot.normalizer_conj_mem D.i D.α n
    (((RelativeRoot.subgroup D.i D.α).carrier (base k)).inv_mem hA)
  rw [hw, constantPoint_self] at hconj
  have ht : D.I t ∈ normalizerPoints D.i := by
    apply centralizerPoints_le_normalizerPoints D.i
    rw [mem_centralizerPoints, ← mem_torusCentralizer_base_iff]
    intro V b s
    change (b ≫ (t ≫ D.i.hom.hom)) * (s ≫ D.i.hom.hom) =
      (s ≫ D.i.hom.hom) * (b ≫ (t ≫ D.i.hom.hom))
    rw [← Category.assoc, ← MonObj.mul_comp, mul_comm (b ≫ t) s, MonObj.mul_comp]
  refine ⟨⟨(D.B y)⁻¹, D.n * (D.A z)⁻¹ * D.n⁻¹⟩,
    ((RelativeRoot.subgroup D.i (-D.α)).carrier (base k)).inv_mem hB, hconj, ?_⟩
  have hp : (D.B y)⁻¹ * D.A (c : Γ((base k).left, ⊤)) *
        (D.n * (D.A z)⁻¹ * D.n⁻¹) = D.I t * D.n⁻¹ := by
    calc
      _ = (D.B y)⁻¹ * (D.A (c : Γ((base k).left, ⊤)) * D.n) *
          (D.A z)⁻¹ * D.n⁻¹ := by group
      _ = _ := by rw [he]; group
  rw [hp]
  exact (normalizerPoints D.i).mul_mem ht ((normalizerPoints D.i).inv_mem n.property)

end WeylData

end RankOneRootCellRelation

end Langlands.GroupScheme
