import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Rational.BruhatStructuralReduction

/-! # Rational Bruhat contractions for smooth affine groups -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

namespace Dynamic

/-- The canonical opposite-cell lift, using the proved opposite-cell theorem. -/
def smoothAffineOppositeCellOrbitLift
    {C : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : C.toGrp ⟶ G)
    (a b : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ C.toGrp)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X}
    (he : IsOrbitExtension (a ≫ i) g e) (he0 : evalZero e = 1) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶
        (Affine.unipotentScheme (CommGroupScheme.groupHom
          (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ (b ≫ i))).X ⊗
        (Affine.parabolicScheme (b ≫ i)).X :=
  oppositeCellOrbitLift oppositeCellStatement i a b he he0

/-- Multiplication of the lifted factors recovers the entire orbit extension. -/
@[reassoc]
theorem smoothAffineOppositeCellOrbitLift_fac
    {C : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : C.toGrp ⟶ G)
    (a b : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ C.toGrp)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X}
    (he : IsOrbitExtension (a ≫ i) g e) (he0 : evalZero e = 1) :
    let ψminus := CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ (b ≫ i)
    smoothAffineOppositeCellOrbitLift i a b he he0 ≫
      ((fst _ _ ≫ (Affine.unipotentHom ψminus).hom.hom) *
        (snd _ _ ≫ (Affine.parabolicHom (b ≫ i)).hom.hom)) = e :=
  oppositeCellOrbitLift_fac oppositeCellStatement i a b he he0

/-- Identity-limit orbits factor through the opposite cell of any cocharacter
of the same commutative source. -/
theorem hasProductContraction_of_smooth_affine
    {C : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : C.toGrp ⟶ G)
    (a b : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ C.toGrp)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : g ∈ (unipotent (a ≫ i)).carrier (Over.mk (𝟙 _))) :
    HasProductContraction (a ≫ i)
      (unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ (b ≫ i)))
      (parabolic (b ≫ i)) g := by
  obtain ⟨e, he, he0⟩ := hg
  exact hasProductContraction_of_represented_lift (a ≫ i) _ _
    (Affine.isRepresentedBy_unipotentHom _)
    (Affine.isRepresentedBy_parabolicHom _)
    he he0 (smoothAffineOppositeCellOrbitLift i a b he he0)
    (smoothAffineOppositeCellOrbitLift_fac i a b he he0)

end Dynamic

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Every smooth affine ambient group has the normalizer-indexed contractions. -/
theorem hasNormalizerProductContractions_of_smooth_affine :
    HasNormalizerProductContractions i ν := by
  intro n u
  let ξ := cocharacterAut (normalizingAut i n) ν
  have hξ : CommGroupScheme.groupHom ξ ≫ i =
      (CommGroupScheme.groupHom ν ≫ i) ≫
        (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom :=
    groupHom_cocharacterAut_comp i n ν
  have h := Dynamic.hasProductContraction_of_smooth_affine i
    (CommGroupScheme.groupHom ν) (CommGroupScheme.groupHom ξ) u.property
  simpa only [hξ] using h

/-- For a smooth affine group, the centralizer identity and actual parabolic
covering suffice for rational Bruhat decomposition. -/
theorem hasRationalBruhatDecomposition_of_parabolicCovering
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hcover : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ∃ n ∈ normalizerPoints i,
        ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
        ∃ q ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
          g = p * n * q) :
    HasRationalBruhatDecomposition i ν := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact hasRationalBruhatDecomposition_of_parabolicCovering_and_productContractions i ν
    hZ hcover (hasNormalizerProductContractions_of_smooth_affine i ν)

/-- Four explicit structural propositions suffice; opposite-cell geometry is
supplied by its published proof. -/
theorem rationalBruhatStatement_of_centralizer_and_parabolic_inputs
    (hCentralizer : GenericCentralizerStatement.{u})
    (hMinimal : GenericMinimalParabolicStatement.{u})
    (hCommon : ParabolicIntersectionCentralizerStatement.{u})
    (hInside : MinimalParabolicSplitTorusConjugacyStatement.{u}) :
    RationalBruhatStatement.{u} := by
  intro k _ G hG T i hi ν hν
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  exact hasRationalBruhatDecomposition_of_parabolicCovering i ν
    (hCentralizer k G hG T i hi ν hν)
    (rationalBruhatCovering_of_structural hMinimal hCommon hInside k G hG T i hi ν hν)

end Langlands.GroupScheme
