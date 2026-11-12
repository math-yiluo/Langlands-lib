import Langlands.GroupScheme.MatrixRepresentation.DynamicExtremalLines
import Langlands.GroupScheme.MatrixRepresentation.SchemeAction
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-! # Orbit weight bounds for actual dynamic-parabolic eigenlines -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G U P : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- On every scheme test, the orbit of the selected coordinate vector has no
coordinate with weight strictly above its original weight. -/
def HasOrbitWeightUpperBound (ρ : MatrixRepresentation G n) (e : n → ℤ) (j : n) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of k))) (g : Z ⟶ G.X) (a : n),
    e j < e a → (ρ.pointMatrix Z g : Matrix n n Γ(Z.left, ⊤)) a j = 0

variable (ρ : MatrixRepresentation G n)
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (e : n → ℤ) (hχ : χ ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)

include hχ in
/-- The opposite dynamic unipotent has identity entries whenever the row
weight is at least the column weight, including equal-weight blocks. -/
theorem pointMatrix_entry_eq_one_of_mem_opposite_unipotent
    {Z : Over (Spec (CommRingCat.of k))} {g : Z ⟶ G.X}
    (hg : g ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).carrier Z)
    {a b : n} (hab : e b ≤ e a) :
    (ρ.pointMatrix Z g : Matrix n n Γ(Z.left, ⊤)) a b = (1 : Matrix n n Γ(Z.left, ⊤)) a b := by
  have h := Dynamic.unipotent_le_comap
    (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ) ρ Z hg
  rw [SubgroupFunctor.mem_comap, Category.assoc, hχ,
    GeneralLinear.inv_comp_diagonalCocharacter, GeneralLinear.unipotent_diagonalCocharacter,
    GeneralLinear.mem_blockUnipotent] at h
  exact h a b (neg_le_neg hab)

variable (iU : U ⟶ G) (iP : P ⟶ G)
  (hU : (Dynamic.unipotent
    (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy iU)
  (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)

include hχ hU in
/-- On the actual opposite cell, a parabolic eigenline has no coordinate
strictly above its own cocharacter weight. -/
theorem oppositeCell_entry_eq_zero_of_preservesCoordinateLine (j : n)
    (hline : (ρ.restrict iP).PreservesCoordinateLine j)
    {a : n} (ha : e j < e a) :
    (ρ.pointMatrix (U.X ⊗ P.X)
      ((fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)) :
        Matrix n n Γ((U.X ⊗ P.X).left, ⊤)) a j = 0 := by
  let Z := U.X ⊗ P.X
  let u : Z ⟶ G.X := fst U.X P.X ≫ iU.hom.hom
  let p : Z ⟶ G.X := snd U.X P.X ≫ iP.hom.hom
  have hu : u ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).carrier Z :=
    (hU.pointsEquiv Z (fst U.X P.X)).property
  obtain ⟨c, hc⟩ := hline Z (snd U.X P.X)
  rw [pointMatrix_restrict] at hc
  have huz := ρ.pointMatrix_entry_eq_one_of_mem_opposite_unipotent χ e hχ hu ha.le
  have hne : a ≠ j := fun h => ha.ne (congrArg e h).symm
  rw [Matrix.one_apply_ne hne] at huz
  have hact := congrFun (congrArg
    (fun v : n → Γ(Z.left, ⊤) => (ρ.pointMatrix Z u : Matrix n n Γ(Z.left, ⊤)) *ᵥ v) hc) a
  simp only [Matrix.mulVec_smul, Matrix.mulVec_single_one, Matrix.col_apply,
    Pi.smul_apply, smul_eq_mul, huz, mul_zero] at hact
  change (ρ.pointMatrix Z (u * p) : Matrix n n Γ(Z.left, ⊤)) a j = 0
  rw [map_mul, Units.val_mul, Matrix.mul_apply]
  simpa only [Matrix.mulVec, dotProduct, Matrix.col_apply, p] using hact

include hχ hU hP in
/-- Density of the published opposite open cell extends its weight bound to
the entire smooth connected affine group, on every scheme test. -/
theorem hasOrbitWeightUpperBound_of_parabolic_eigenline
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (j : n) (hline : (ρ.restrict iP).PreservesCoordinateLine j) :
    ρ.HasOrbitWeightUpperBound e j := by
  have hgeom : GeometricallyIntegral G.X.hom :=
    smoothConnectedAffineGeometry.1 k G inferInstance inferInstance inferInstance
  have : IsIntegral G.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom
  let c : U.X ⊗ P.X ⟶ G.X :=
    (fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)
  have hc : IsOpenImmersion c.left := oppositeCellStatement k G χ U P iU iP hU hP
  have hne : (Set.range c.left).Nonempty := by
    let z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X ⊗ P.X := lift 1 1
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
    exact ⟨c.left (z.left x), ⟨z.left x, rfl⟩⟩
  have : IsDominant c.left :=
    ⟨c.left.isOpenEmbedding.isOpen_range.dense hne⟩
  intro Z g a ha
  let f : G.X ⟶ coefficientSpace Unit (CommRingCat.of k) :=
    coefficientPoint G.X (fun _ => (ρ.pointMatrix G.X (𝟙 _) :
      Matrix n n Γ(G.X.left, ⊤)) a j)
  let z : G.X ⟶ coefficientSpace Unit (CommRingCat.of k) := coefficientPoint G.X 0
  have he : f = z := by
    apply Over.OverMorphism.ext
    apply ext_of_isDominant_of_isSeparated (coefficientSpace Unit (CommRingCat.of k)).hom
      ((Over.w f).trans (Over.w z).symm) c.left
    change (c ≫ f).left = (c ≫ z).left
    congr 1
    apply coefficientCoordinates_injective
    ext b
    have hm := ρ.pointMatrix_naturality c (𝟙 G.X)
    have hz := ρ.oppositeCell_entry_eq_zero_of_preservesCoordinateLine χ e hχ iU iP hU j hline ha
    simpa only [f, z, coefficientCoordinates_comp, coefficientCoordinates_coefficientPoint,
      Category.comp_id, Pi.zero_apply, map_zero, Matrix.GeneralLinearGroup.map_apply,
      Matrix.map_apply] using (congrArg (fun M : GL n Γ((U.X ⊗ P.X).left, ⊤) =>
        (M : Matrix n n Γ((U.X ⊗ P.X).left, ⊤)) a j) hm).symm.trans hz
  have hz := congrArg (fun q => coefficientCoordinates q ()) he
  simp only [f, z, coefficientCoordinates_coefficientPoint, Pi.zero_apply] at hz
  have hm := ρ.pointMatrix_naturality g (𝟙 G.X)
  have h := congrArg (fun M : GL n Γ(Z.left, ⊤) => (M : Matrix n n Γ(Z.left, ⊤)) a j) hm
  simpa only [Category.comp_id, Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply,
    hz, map_zero] using h

end Langlands.GroupScheme.MatrixRepresentation
