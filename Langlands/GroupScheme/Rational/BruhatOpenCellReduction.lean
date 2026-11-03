import Langlands.GroupScheme.Dynamic.OpenProductContraction
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Rational.BruhatContractionReduction

/-! # Rational Bruhat contraction inputs from the opposite open cell -/

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

/-- The actual lift of an identity-limit orbit extension through the
canonical opposite cell of a cocharacter in the same commutative group. -/
def oppositeCellOrbitLift
    (hcell : OppositeCellStatement.{u})
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
        (Affine.parabolicScheme (b ≫ i)).X := by
  let ψ := b ≫ i
  let invGm := CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1))
  let ψminus := invGm ≫ ψ
  let iU := Affine.unipotentHom ψminus
  let iP := Affine.parabolicHom ψ
  have hU : (unipotent ψminus).IsRepresentedBy iU :=
    Affine.isRepresentedBy_unipotentHom ψminus
  have hP : (parabolic ψ).IsRepresentedBy iP :=
    Affine.isRepresentedBy_parabolicHom ψ
  let : IsOpenImmersion
      ((fst _ _ ≫ iU.hom.hom) * (snd _ _ ≫ iP.hom.hom)).left :=
    hcell k G ψ _ _ iU iP hU hP
  have hNU : (SubgroupFunctor.range iU).IsNormalizedBy
      (SubgroupFunctor.range (a ≫ i)) := by
    rw [hU.2]
    simpa only [ψminus, ψ, Category.assoc] using
      unipotent_isNormalizedBy_range_of_common_commutativeGroup i a (invGm ≫ b)
  have hNP : (SubgroupFunctor.range iP).IsNormalizedBy
      (SubgroupFunctor.range (a ≫ i)) := by
    rw [hP.2]
    exact parabolic_isNormalizedBy_range_of_common_commutativeGroup i a b
  exact openProductOrbitLift (a ≫ i) iU iP hNU hNP he he0

/-- The canonical lift recovers the supplied extension after multiplication. -/
@[reassoc]
theorem oppositeCellOrbitLift_fac
    (hcell : OppositeCellStatement.{u})
    {C : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : C.toGrp ⟶ G)
    (a b : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ C.toGrp)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X}
    (he : IsOrbitExtension (a ≫ i) g e) (he0 : evalZero e = 1) :
    let ψminus := CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ (b ≫ i)
    oppositeCellOrbitLift hcell i a b he he0 ≫
      ((fst _ _ ≫ (Affine.unipotentHom ψminus).hom.hom) *
        (snd _ _ ≫ (Affine.parabolicHom (b ≫ i)).hom.hom)) = e := by
  dsimp only
  let ψ := b ≫ i
  let ψminus := CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ ψ
  let iU := Affine.unipotentHom ψminus
  let iP := Affine.parabolicHom ψ
  let : IsOpenImmersion
      ((fst _ _ ≫ iU.hom.hom) * (snd _ _ ≫ iP.hom.hom)).left :=
    hcell k G ψ _ _ iU iP
      (Affine.isRepresentedBy_unipotentHom ψminus)
      (Affine.isRepresentedBy_parabolicHom ψ)
  unfold oppositeCellOrbitLift
  exact openProductOrbitLift_fac _ _ _ _ _ _ _

/-- The opposite-cell theorem puts a contraction through the opposite cell
of any cocharacter in the same commutative group. -/
theorem hasProductContraction_of_oppositeCell
    (hcell : OppositeCellStatement.{u})
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
    he he0 (oppositeCellOrbitLift hcell i a b he he0)
    (oppositeCellOrbitLift_fac hcell i a b he he0)

end Dynamic

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The genuine opposite-cell theorem supplies all normalizer-indexed
product contractions required by the Weyl factorization reduction. -/
theorem hasNormalizerProductContractions_of_oppositeCell
    (hcell : OppositeCellStatement.{u}) :
    HasNormalizerProductContractions i ν := by
  intro n u
  let ξ := cocharacterAut (normalizingAut i n) ν
  have hξ : CommGroupScheme.groupHom ξ ≫ i =
      (CommGroupScheme.groupHom ν ≫ i) ≫
        (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom :=
    groupHom_cocharacterAut_comp i n ν
  have h := Dynamic.hasProductContraction_of_oppositeCell hcell i
    (CommGroupScheme.groupHom ν) (CommGroupScheme.groupHom ξ) u.property
  simpa only [hξ] using h

/-- An opposite open cell also gives multiplication injectivity on all tests. -/
theorem hasInjectiveOppositeCellMultiplication_of_oppositeCell
    (hcell : OppositeCellStatement.{u}) :
    HasInjectiveOppositeCellMultiplication i ν := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χminus := CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  exact hasInjectiveOppositeCellMultiplication_of_openImmersion i ν
    (Dynamic.Affine.unipotentScheme χminus) (Dynamic.Affine.parabolicScheme χ)
    (Dynamic.Affine.unipotentHom χminus) (Dynamic.Affine.parabolicHom χ)
    (Dynamic.Affine.isRepresentedBy_unipotentHom χminus)
    (Dynamic.Affine.isRepresentedBy_parabolicHom χ)
    (hcell k G χ _ _ _ _
      (Dynamic.Affine.isRepresentedBy_unipotentHom χminus)
      (Dynamic.Affine.isRepresentedBy_parabolicHom χ))

/-- Opposite-cell geometry and the whole-torus centralizer identity give
the unipotent Weyl factorization. -/
theorem hasUnipotentWeylFactorization_of_oppositeCell
    (hcell : OppositeCellStatement.{u})
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i) :
    HasUnipotentWeylFactorization i ν :=
  hasUnipotentWeylFactorization_of_productContractions i ν hZ
    (fun ξ => hasInjectiveOppositeCellMultiplication_of_oppositeCell i ξ hcell)
    (hasNormalizerProductContractions_of_oppositeCell i ν hcell)

/-- The opposite-cell theorem discharges the geometric contraction inputs
in the rational Bruhat assembly; centralizer identity and covering remain. -/
theorem hasRationalBruhatDecomposition_of_oppositeCell
    (hcell : OppositeCellStatement.{u})
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hcover : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ∃ (n : normalizerPoints i)
        (u v : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i)),
        g = u * n * v) :
    HasRationalBruhatDecomposition i ν :=
  hasRationalBruhatDecomposition_of_productContractions i ν hZ hcover
    (fun ξ => hasInjectiveOppositeCellMultiplication_of_oppositeCell i ξ hcell)
    (hasNormalizerProductContractions_of_oppositeCell i ν hcell)

end Langlands.GroupScheme
