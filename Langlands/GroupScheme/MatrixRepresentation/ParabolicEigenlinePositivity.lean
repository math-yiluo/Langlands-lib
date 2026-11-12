import Langlands.GroupScheme.MatrixRepresentation.OpposingCocharacterOrbitWeights
import Langlands.GroupScheme.Rational.RankOneNormKernelReflection

/-! # Strictly positive weights of proper parabolic coordinate eigenlines -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G U P : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The subgroup preserves the selected line and the entire group does not. -/
def HasProperParabolicEigenline (ρ : MatrixRepresentation G n) (iP : P ⟶ G) (j : n) : Prop :=
  (ρ.restrict iP).PreservesCoordinateLine j ∧ ¬ρ.PreservesCoordinateLine j

variable (ρ : MatrixRepresentation G n)

/-- Vanishing on one dominant test detects preservation of a coordinate line
in a representation of a reduced group. -/
theorem preservesCoordinateLine_of_dominant_test [IsReduced G.X.left]
    (j : n) {C : Over (Spec (CommRingCat.of k))} (c : C ⟶ G.X)
    [IsDominant c.left]
    (hz : ∀ a : n, a ≠ j →
      (ρ.pointMatrix C c : Matrix n n Γ(C.left, ⊤)) a j = 0) :
    ρ.PreservesCoordinateLine j := by
  apply preservesCoordinateLine_of_column_eq_zero
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
    simpa only [f, z, coefficientCoordinates_comp, coefficientCoordinates_coefficientPoint,
      Category.comp_id, Pi.zero_apply, map_zero, Matrix.GeneralLinearGroup.map_apply,
      Matrix.map_apply] using (congrArg (fun M : GL n Γ(C.left, ⊤) =>
        (M : Matrix n n Γ(C.left, ⊤)) a j) hm).symm.trans (hz a ha)
  have hz := congrArg (fun q => coefficientCoordinates q ()) he
  simp only [f, z, coefficientCoordinates_coefficientPoint, Pi.zero_apply] at hz
  have hm := ρ.pointMatrix_naturality g (𝟙 G.X)
  have h := congrArg (fun M : GL n Γ(Z.left, ⊤) =>
    (M : Matrix n n Γ(Z.left, ⊤)) a j) hm
  simpa only [Category.comp_id, Matrix.GeneralLinearGroup.map_apply,
    Matrix.map_apply, hz, map_zero] using h

variable
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (iU : U ⟶ G) (iP : P ⟶ G)
  (hU : (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).IsRepresentedBy iU)
  (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)

include hU hP in
/-- If the parabolic and its opposite unipotent both preserve the line, their
dense open cell makes the whole group preserve it. -/
theorem preservesCoordinateLine_of_oppositeCell
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (j : n) (hlineU : (ρ.restrict iU).PreservesCoordinateLine j)
    (hlineP : (ρ.restrict iP).PreservesCoordinateLine j) :
    ρ.PreservesCoordinateLine j := by
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
  have : IsDominant c.left := ⟨c.left.isOpenEmbedding.isOpen_range.dense hne⟩
  apply ρ.preservesCoordinateLine_of_dominant_test j c
  intro a ha
  let Z := U.X ⊗ P.X
  obtain ⟨u, hu⟩ := hlineU Z (fst U.X P.X)
  obtain ⟨p, hp⟩ := hlineP Z (snd U.X P.X)
  rw [pointMatrix_restrict] at hu hp
  have hact : (ρ.pointMatrix Z c : Matrix n n Γ(Z.left, ⊤)) *ᵥ Pi.single j 1 =
      ((p * u : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) •
        (Pi.single j 1 : n → Γ(Z.left, ⊤)) := by
    rw [show ρ.pointMatrix Z c =
      ρ.pointMatrix Z (fst U.X P.X ≫ iU.hom.hom) *
        ρ.pointMatrix Z (snd U.X P.X ≫ iP.hom.hom) from map_mul _ _ _,
      Units.val_mul, ← Matrix.mulVec_mulVec, hp, Matrix.mulVec_smul, hu,
      smul_smul, Units.val_mul]
  have h := congrFun hact a
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
    Pi.single_eq_of_ne ha, smul_eq_mul, mul_zero] using h

variable (e : n → ℤ)
  (hχ : χ ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)

include hχ hU in
/-- A zero original weight together with the lower orbit bound makes the
opposite unipotent preserve the selected line. -/
theorem oppositeUnipotent_preservesCoordinateLine_of_weight_zero
    (j : n) (hzero : e j = 0) (hlower : ρ.HasOrbitWeightLowerBound e j) :
    (ρ.restrict iU).PreservesCoordinateLine j := by
  apply preservesCoordinateLine_of_column_eq_zero
  intro Z u a ha
  rw [pointMatrix_restrict]
  by_cases hea : e a < 0
  · exact hlower Z (u ≫ iU.hom.hom) a (by omega)
  · have hu : u ≫ iU.hom.hom ∈
        (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).carrier Z :=
      (hU.pointsEquiv Z u).property
    have he := ρ.pointMatrix_entry_eq_one_of_mem_opposite_unipotent χ e hχ hu
      (a := a) (b := j) (by omega)
    simpa only [Matrix.one_apply_ne ha] using he

include hχ hU hP in
/-- For a reversible cocharacter, a parabolic eigenline which is not a global
eigenline has strictly positive weight. -/
theorem weight_pos_of_proper_parabolic_eigenline_of_reversesCocharacter
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (j : n) (hline : ρ.HasProperParabolicEigenline iP j)
    {s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hs : ReversesCocharacter χ s) : 0 < e j := by
  have hupper := ρ.hasOrbitWeightUpperBound_of_parabolic_eigenline
    χ e hχ iU iP hU hP j hline.1
  have hnonneg := ρ.weight_nonneg_of_orbit_upperBound_of_reversesCocharacter
    χ e hχ j hupper hs
  by_contra hn
  have hzero : e j = 0 := by omega
  have hlower := ρ.hasOrbitWeightLowerBound_of_reversesCocharacter χ e hχ j hupper hs
  exact hline.2 (ρ.preservesCoordinateLine_of_oppositeCell χ iU iP hU hP j
    (ρ.oppositeUnipotent_preservesCoordinateLine_of_weight_zero χ iU hU e hχ j hzero hlower)
    hline.1)

section TorusNormalizer

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

omit [Mono i.hom.hom.left] in
/-- Integral torus-cocharacter reversal is actual conjugation to the opposite
cocharacter in the ambient group. -/
theorem reversesCocharacter_of_normalizingAut_neg
    (ζ : cocharacterLattice T) (s : normalizerPoints i)
    (hs : cocharacterAut (normalizingAut i s) ζ = -ζ) :
    ReversesCocharacter (CommGroupScheme.groupHom ζ ≫ i) s.val := by
  change (CommGroupScheme.groupHom ζ ≫ i) ≫ (G.innerIso s.val).hom =
    CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫
      (CommGroupScheme.groupHom ζ ≫ i)
  rw [Category.assoc, isNormalizingPoint_normalizingAut i s, ← Category.assoc]
  have he : ζ ≫ (normalizingAut i s).hom = -ζ := hs
  have hinv : Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ ζ = -ζ := by
    simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
  change CommGroupScheme.groupHom (ζ ≫ (normalizingAut i s).hom) ≫ i =
    CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ ζ) ≫ i
  rw [he, hinv]

/-- The actual rank-one Weyl norm-kernel direction gives strictly positive
weight to every proper parabolic coordinate eigenline. -/
theorem weight_pos_of_rankOne_normKernel_parabolic_eigenline
    [IsAffineHom G.X.hom] [Fintype (relativeWeylGroup i)]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α})
    (iU : U ⟶ G) (iP : P ⟶ G)
    (hU : (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom (normKernelCocharacter i ν) ≫ i))).IsRepresentedBy iU)
    (hP : (Dynamic.parabolic
      (CommGroupScheme.groupHom (normKernelCocharacter i ν) ≫ i)).IsRepresentedBy iP)
    (e : n → ℤ)
    (hχ : (CommGroupScheme.groupHom (normKernelCocharacter i ν) ≫ i) ≫ ρ =
      GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
    (j : n) (hline : ρ.HasProperParabolicEigenline iP j) : 0 < e j := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨s, hs⟩ := hasReversingNormalizer_normKernelCocharacter i hG hi ν hν α hα
  exact ρ.weight_pos_of_proper_parabolic_eigenline_of_reversesCocharacter
    _ iU iP hU hP e hχ j hline
    (reversesCocharacter_of_normalizingAut_neg i _ s hs)

end TorusNormalizer

end Langlands.GroupScheme.MatrixRepresentation
