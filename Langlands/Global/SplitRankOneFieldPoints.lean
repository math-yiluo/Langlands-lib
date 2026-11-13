import Langlands.Global.SplitRankOneCellData
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.Torus.RationalCharacterSeparation
import Langlands.Geometry.Building.ChamberGenerationOpenCell
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.GroupScheme.Reductive.RationalPointDensityProof
import Langlands.GroupScheme.MatrixRepresentation.VectorGroupPolynomial
import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.MultiplicativePointTopology

/-! # Field points of a split rank-one group act on the binary form by similitudes

For every field `L` containing `F`, every `L`-point `g` of `G` acts on the binary form
`ν(X, Y) = Σ X^(k-l) Y^l w_l` of the cell data through a `GL₂`-substitution and a scalar,
with multiplier `c` satisfying `c ^ d = η(g) ^ 2`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.SplitRankOne

open Langlands.GroupScheme
open Langlands.GroupScheme.MatrixRepresentation
open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}

section BaseChange

variable (L : Type u) [Field L] [Algebra F L]

/-- The projection from the base change of `G` to `G`. -/
abbrev baseProj (G : GroupScheme (Spec (CommRingCat.of F))) :
    (GaloisPointComparison.baseChanged F L G).X.left ⟶ G.X.left :=
  pullback.fst G.X.hom (GaloisPointComparison.baseMap F L)

/-- The base change of a morphism `f : X ⟶ G.X`, as an object over `Spec L`. -/
abbrev cellBC {X : Over (Spec (CommRingCat.of F))} (f : X ⟶ G.X) :
    Over (Spec (CommRingCat.of L)) :=
  Over.mk (pullback.snd f.left (baseProj L G) ≫
    (GaloisPointComparison.baseChanged F L G).X.hom)

/-- The base-changed morphism into the base change of `G`. -/
abbrev cellBCMap {X : Over (Spec (CommRingCat.of F))} (f : X ⟶ G.X) :
    cellBC L f ⟶ (GaloisPointComparison.baseChanged F L G).X :=
  Over.homMk (pullback.snd f.left (baseProj L G)) rfl

/-- An `L`-rational point of the base-changed source gives an `L`-coefficient point of the
source. -/
def cellPointDescend {X : Over (Spec (CommRingCat.of F))} (f : X ⟶ G.X)
    (x : RationalPoint L (cellBC L f)) :
    (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F L)) ⟶ X :=
  Over.homMk (x.left ≫ pullback.fst f.left (baseProj L G)) (by
    have hx : x.left ≫ pullback.snd f.left (baseProj L G) ≫
        pullback.snd G.X.hom (GaloisPointComparison.baseMap F L) = 𝟙 _ := Over.w x
    have hf : f.left ≫ G.X.hom = X.hom := Over.w f
    change (x.left ≫ pullback.fst f.left (baseProj L G)) ≫ X.hom =
      GaloisPointComparison.baseMap F L
    rw [← hf, Category.assoc, pullback.condition_assoc, pullback.condition,
      ← Category.assoc, ← Category.assoc, Category.assoc x.left, hx, Category.id_comp])

theorem baseChangeCoeffEquiv_cellBCMap {X : Over (Spec (CommRingCat.of F))} (f : X ⟶ G.X)
    (x : RationalPoint L (cellBC L f)) :
    GaloisPointComparison.baseChangeCoeffEquiv F L G (x ≫ cellBCMap L f) =
      cellPointDescend L f x ≫ f := by
  apply Over.OverMorphism.ext
  rw [GaloisPointComparison.baseChangeCoeffEquiv_left]
  change (x.left ≫ pullback.snd f.left (baseProj L G)) ≫ baseProj L G =
    (x.left ≫ pullback.fst f.left (baseProj L G)) ≫ f.left
  rw [Category.assoc, Category.assoc, pullback.condition]

/-- **Two-cell decomposition of field points.** Every `L`-point of a connected reductive
group over an infinite field is a quotient of two `L`-points of any open cell containing a
rational point. -/
theorem exists_points_mul_eq_of_openImmersion [Infinite F] (hG : IsConnectedReductive G)
    {X : Over (Spec (CommRingCat.of F))} (f : X ⟶ G.X) [IsOpenImmersion f.left]
    (x₀ : RationalPoint F X) (g : G.affinePoints (CommAlgCat.of F L)) :
    ∃ p q : (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F L)) ⟶ X,
      (p ≫ f) * g = q ≫ f := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have : GeometricallyIntegral G.X.hom :=
    smoothConnectedAffineGeometry.1 F G hG.smooth hG.isAffineHom hG.connectedSpace
  have : IrreducibleSpace (GaloisPointComparison.baseChanged F L G).X.left :=
    inferInstanceAs (IrreducibleSpace ↥(pullback G.X.hom (GaloisPointComparison.baseMap F L)))
  have hdense : HasDenseRationalPoints L (GaloisPointComparison.baseChanged F L G).X := by
    refine (RationalCharacterSeparation.dense_iUnion_range_rationalExtend F L G
      (reductiveRationalPointDensity F G hG)).mono ?_
    refine Set.iUnion_subset fun z => ?_
    exact Set.subset_iUnion (fun p : RationalPoint L _ => Set.range p.left) _
  let e := GaloisPointComparison.rationalExtend F L G (x₀ ≫ f)
  have he : e.left ≫ baseProj L G = GaloisPointComparison.baseMap F L ≫ x₀.left ≫ f.left :=
    GaloisPointComparison.rationalExtend_fst F L G (x₀ ≫ f)
  let x₀L : RationalPoint L (cellBC L f) :=
    Over.homMk (pullback.lift (GaloisPointComparison.baseMap F L ≫ x₀.left) e.left
      (by rw [Category.assoc, he])) (by
        change pullback.lift _ _ _ ≫ pullback.snd f.left (baseProj L G) ≫
          (GaloisPointComparison.baseChanged F L G).X.hom = 𝟙 _
        rw [pullback.lift_snd_assoc]
        exact Over.w e)
  have : IsOpenImmersion (cellBCMap L f).left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd f.left (baseProj L G)))
  obtain ⟨x, y, hxy⟩ := exists_cell_points_mul_eq_of_dense hdense (cellBCMap L f) x₀L
    ((GaloisPointComparison.baseChangeCoeffEquiv F L G).symm g)
  refine ⟨cellPointDescend L f x, cellPointDescend L f y, ?_⟩
  have h := congrArg (GaloisPointComparison.baseChangeCoeffEquiv F L G) hxy
  rwa [map_mul, MulEquiv.apply_symm_apply, baseChangeCoeffEquiv_cellBCMap,
    baseChangeCoeffEquiv_cellBCMap] at h

end BaseChange

section Similitude

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {n : Type} [Fintype n] [DecidableEq n]
  {ρ : MatrixRepresentation G n} {j : n} {i : T.toGrp ⟶ G} {α : characterLattice T}
  (L : Type u) [Field L] [Algebra F L]

/-- Evaluation of a rational character of `G` on coefficient points, in the units of the
coefficient algebra. -/
def etaUnits (eta : rationalCharacters G) (A : CommAlgCat.{u} F) : G.affinePoints A →* Aˣ :=
  (GroupScheme.Gm.affineUnitsEquiv (CommRingCat.of F) A).toMonoidHom.comp
    (G.affinePointsTarget eta.toMul A)

/-- The value of `eta` on a torus point is the value of its restriction to the torus. -/
theorem etaUnits_torus (eta : rationalCharacters G) (A : CommAlgCat.{u} F)
    (τ : GroupScheme.affinePoints T.toGrp A) :
    etaUnits eta A (τ ≫ i.hom.hom) = Lie.characterValue (torusCharacterRestrict i eta) τ :=
  rfl

/-- A rational character is trivial on the points of a root map. -/
theorem etaUnits_root (eta : rationalCharacters G) (A : CommAlgCat.{u} F)
    (x : VectorGroup.groupScheme (CommRingCat.of F) 1 ⟶ G)
    (v : GroupScheme.affinePoints (VectorGroup.groupScheme (CommRingCat.of F) 1) A) :
    etaUnits eta A (v ≫ x.hom.hom) = 1 := by
  have h := (VectorGroup.isUnipotent F 1).comp_eq_one_of_isSplitTorus isSplitTorus_gm
    (x ≫ eta.toMul) _ v
  change GroupScheme.Gm.affineUnitsEquiv (CommRingCat.of F) A
    ((v ≫ x.hom.hom) ≫ eta.toMul.hom.hom) = 1
  rw [Category.assoc, ← Grp.comp_hom_hom, h, map_one]

/-- The field points of `G` acting on the binary form of the cell data by `GL₂`-similitudes
whose multiplier `c` satisfies `c ^ d = eta(g) ^ 2`. -/
def similitudeSubgroup (D : CellData ρ j i α) :
    Subgroup (G.affinePoints (CommAlgCat.of F L)) where
  carrier := {g | ∃ c : L, IsBinarySimilitude D.k (wvec ρ j D.xm L)
      (ρ.affineMatrix (CommAlgCat.of F L) g : Matrix n n L) c ∧
      c ^ D.d = ((etaUnits D.eta (CommAlgCat.of F L) g : Lˣ) : L) ^ 2}
  mul_mem' := by
    rintro g h ⟨c₁, h₁, hc₁⟩ ⟨c₂, h₂, hc₂⟩
    refine ⟨c₁ * c₂, ?_, ?_⟩
    · rw [map_mul, Units.val_mul]
      exact h₁.mul h₂
    · rw [map_mul, Units.val_mul, mul_pow, mul_pow, hc₁, hc₂]
  one_mem' := ⟨1, by rw [map_one, Units.val_one]; exact isBinarySimilitude_one _ _, by simp⟩
  inv_mem' := by
    rintro g ⟨c, hg, hc⟩
    refine ⟨c⁻¹, hg.inv ?_, ?_⟩
    · rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    · rw [inv_pow, hc, map_inv, Units.val_inv_eq_inv_val, inv_pow]

variable [Infinite F] [Infinite L]

theorem CellData.lower_mem (D : CellData ρ j i α)
    (v : GroupScheme.affinePoints (VectorGroup.groupScheme (CommRingCat.of F) 1)
      (CommAlgCat.of F L)) :
    v ≫ D.xm.hom.hom ∈ similitudeSubgroup L D := by
  obtain ⟨t, rfl⟩ := VectorGroup.affinePoint_surjective (R := CommRingCat.of F) (d := 1)
    (CommAlgCat.of F L) v
  have ht : VectorGroup.affinePoint (R := CommRingCat.of F) (CommAlgCat.of F L) t =
      gaPoint (CommAlgCat.of F L) (t 0) := by
    congr 1
    funext r
    rw [Subsingleton.elim r 0]
  refine ⟨1, ?_, ?_⟩
  · rw [ht, ← affineMatrix_restrict, ← lowerMat_eq]
    exact D.hyp.isBinarySimilitude_lower L (t 0)
  · rw [etaUnits_root]
    simp

theorem CellData.raise_mem (D : CellData ρ j i α)
    (v : GroupScheme.affinePoints (VectorGroup.groupScheme (CommRingCat.of F) 1)
      (CommAlgCat.of F L)) :
    v ≫ D.xp.hom.hom ∈ similitudeSubgroup L D := by
  obtain ⟨t, rfl⟩ := VectorGroup.affinePoint_surjective (R := CommRingCat.of F) (d := 1)
    (CommAlgCat.of F L) v
  have ht : VectorGroup.affinePoint (R := CommRingCat.of F) (CommAlgCat.of F L) t =
      gaPoint (CommAlgCat.of F L) (t 0) := by
    congr 1
    funext r
    rw [Subsingleton.elim r 0]
  refine ⟨1, ?_, ?_⟩
  · rw [ht, ← affineMatrix_restrict, ← raiseMat_eq]
    exact D.hyp.isBinarySimilitude_raise L (t 0)
  · rw [etaUnits_root]
    simp

theorem CellData.torus_mem (D : CellData ρ j i α)
    (τ : GroupScheme.affinePoints T.toGrp (CommAlgCat.of F L)) :
    τ ≫ i.hom.hom ∈ similitudeSubgroup L D := by
  refine ⟨((Lie.characterValue D.lam τ : Lˣ) : L) ^ 2 *
    (((Lie.characterValue α τ : Lˣ) : L)⁻¹) ^ D.k, ?_, ?_⟩
  · rw [← affineMatrix_restrict]
    exact D.hyp.isBinarySimilitude_torus L τ
  · have hrel : (Lie.characterValue (D.d • D.lam) τ : Lˣ) =
        Lie.characterValue (torusCharacterRestrict i D.eta + D.b • α) τ := by rw [D.rel]
    rw [characterValue_nsmul', characterValue_add', characterValue_nsmul'] at hrel
    have hL := congrArg (fun u : Lˣ => (u : L)) hrel
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hL
    rw [etaUnits_torus]
    have ha : ((Lie.characterValue α τ : Lˣ) : L) ≠ 0 := Units.ne_zero _
    rw [mul_pow, ← pow_mul, mul_comm 2 D.d, pow_mul, hL, inv_pow, inv_pow, ← pow_mul, mul_comm D.k D.d,
      D.dk, mul_pow, ← pow_mul, mul_comm D.b 2, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha),
      mul_one]

theorem CellData.cell_mem (D : CellData ρ j i α)
    (p : (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F L)) ⟶
      (VectorGroup.groupScheme (CommRingCat.of F) 1).X ⊗
        (T.X ⊗ (VectorGroup.groupScheme (CommRingCat.of F) 1).X)) :
    p ≫ Dynamic.tripleCellMultiplication D.xm i D.xp ∈ similitudeSubgroup L D := by
  have hp : p = lift (p ≫ fst _ _) (lift (p ≫ snd _ _ ≫ fst _ _) (p ≫ snd _ _ ≫ snd _ _)) := by
    ext <;> simp
  rw [hp, Dynamic.lift_tripleCellMultiplication]
  exact mul_mem (D.lower_mem L _) (mul_mem (D.torus_mem L _) (D.raise_mem L _))

end Similitude

/-- **Field points act by similitudes.** For every field `L ⊇ F`, every `L`-point of `G`
acts on the binary form of the cell data by a `GL₂`-substitution and a scalar, with
multiplier `c` satisfying `c ^ d = eta(g) ^ 2`. -/
theorem CellData.exists_similitude {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {n : Type} [Fintype n] [DecidableEq n] {ρ : MatrixRepresentation G n} {j : n}
    {i : T.toGrp ⟶ G} {α : characterLattice T} [Infinite F]
    (hG : IsConnectedReductive G) (D : CellData ρ j i α)
    (L : Type u) [Field L] [Algebra F L] (g : G.affinePoints (CommAlgCat.of F L)) :
    ∃ c : L, IsBinarySimilitude D.k (wvec ρ j D.xm L)
      (ρ.affineMatrix (CommAlgCat.of F L) g : Matrix n n L) c ∧
      c ^ D.d = ((etaUnits D.eta (CommAlgCat.of F L) g : Lˣ) : L) ^ 2 := by
  have : Infinite L := Infinite.of_injective (algebraMap F L) (algebraMap F L).injective
  have := D.openCell
  let x₀ : RationalPoint F ((VectorGroup.groupScheme (CommRingCat.of F) 1).X ⊗
      (T.X ⊗ (VectorGroup.groupScheme (CommRingCat.of F) 1).X)) := lift 1 (lift 1 1)
  obtain ⟨p, q, hpq⟩ := exists_points_mul_eq_of_openImmersion L hG
    (Dynamic.tripleCellMultiplication D.xm i D.xp) x₀ g
  have hg : g = (p ≫ Dynamic.tripleCellMultiplication D.xm i D.xp)⁻¹ *
      (q ≫ Dynamic.tripleCellMultiplication D.xm i D.xp) := by
    rw [← hpq, inv_mul_cancel_left]
  have hmem : g ∈ similitudeSubgroup L D := by
    rw [hg]
    exact mul_mem (inv_mem (D.cell_mem L p)) (D.cell_mem L q)
  exact hmem

end Langlands.Global.SplitRankOne
