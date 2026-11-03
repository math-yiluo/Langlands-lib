import Langlands.GroupScheme.Dynamic.NormalizedLimits
import Langlands.GroupScheme.Dynamic.OppositeCellContraction
import Langlands.GroupScheme.Rational.BruhatNormalizerReduction
import Langlands.GroupScheme.Rational.BruhatOppositeCellReduction
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Weyl factorization from opposite-cell contractions -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section CentralizerTransport

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
  (i : T.toGrp ⟶ G)

/-- A normalizing base point preserves the whole-group centralizer under
inner conjugation, on every test scheme. -/
theorem torusCentralizer_comap_innerIso_normalizer (n : normalizerPoints i) :
    (torusCentralizer i).comap (G.innerIso (n : Over.mk (𝟙 S) ⟶ G.X)).hom =
      torusCentralizer i := by
  apply SubgroupFunctor.ext
  intro X
  apply Subgroup.ext
  intro g
  rw [SubgroupFunctor.mem_comap, comp_innerIso_hom]
  have hn : G.constantPoint n X ∈ (torusNormalizer i).carrier X :=
    (normalizerPointsRestrict i X n).property
  constructor
  · intro hg
    have h := torusCentralizer_isNormalizedBy_torusNormalizer i X _ _
      (((torusNormalizer i).carrier X).inv_mem hn) hg
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
      inv_mul_cancel, mul_one] using h
  · intro hg
    exact torusCentralizer_isNormalizedBy_torusNormalizer i X _ _ hn hg

/-- A cocharacter whose centralizer is the whole-torus centralizer retains
that property after conjugation by an actual normalizing point. -/
theorem centralizer_conjugate_eq_torusCentralizer (χ : (Gm S).toGrp ⟶ G)
    (hZ : Dynamic.centralizer χ = torusCentralizer i) (n : normalizerPoints i) :
    Dynamic.centralizer (χ ≫ (G.innerIso (n : Over.mk (𝟙 S) ⟶ G.X)).hom) =
      torusCentralizer i := by
  rw [Dynamic.centralizer_eq_comap_of_iso _ (G.innerIso
    (n : Over.mk (𝟙 S) ⟶ G.X)).symm]
  change (Dynamic.centralizer ((χ ≫ (G.innerIso
    (n : Over.mk (𝟙 S) ⟶ G.X)).hom) ≫
      (G.innerIso (n : Over.mk (𝟙 S) ⟶ G.X)).inv)).comap
        (G.innerIso (n : Over.mk (𝟙 S) ⟶ G.X)).inv = torusCentralizer i
  rw [Dynamic.comp_hom_comp_inv, hZ, ← innerIso_inv_hom]
  exact torusCentralizer_comap_innerIso_normalizer i n⁻¹

/-- Conjugate-unipotent membership can be pulled back by conjugation with
the inverse base point. -/
theorem mem_unipotent_conjugate_iff_inv_conj (χ : (Gm S).toGrp ⟶ G)
    (n g : Over.mk (𝟙 S) ⟶ G.X) :
    g ∈ (Dynamic.unipotent (χ ≫ (G.innerIso n).hom)).carrier (Over.mk (𝟙 S)) ↔
      n⁻¹ * g * n ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 S)) := by
  have h := Dynamic.mem_unipotent_conj χ n (x := n⁻¹ * g * n)
  simpa only [constantPoint_self, mul_assoc, mul_inv_cancel_left,
    mul_inv_cancel_right, mul_inv_cancel, mul_one] using h.symm

end CentralizerTransport

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Every dynamic-unipotent rational point has a contraction factoring
through the opposite product cell for each normalizer-conjugate cocharacter. -/
def HasNormalizerProductContractions : Prop :=
  let χ := CommGroupScheme.groupHom ν ≫ i
  ∀ (n : normalizerPoints i) (u : RationalPoint.unipotent χ),
    let ψ := χ ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom
    let ψminus := CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ ψ
    Dynamic.HasProductContraction χ (Dynamic.unipotent ψminus) (Dynamic.parabolic ψ)
      (u : Over.mk (𝟙 _) ⟶ G.X)

variable [IsAffine G.X.left]

/-- Opposite-cell contraction splitting supplies the Weyl factorization
used in the normalizer-separation proof. -/
theorem hasUnipotentWeylFactorization_of_productContractions
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hcell : ∀ ξ : cocharacterLattice T, HasInjectiveOppositeCellMultiplication i ξ)
    (hcontractions : HasNormalizerProductContractions i ν) :
    HasUnipotentWeylFactorization i ν := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  let invGm := CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1))
  intro n u
  let ψ := χ ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom
  let ξ := cocharacterAut (normalizingAut i n) ν
  have hξ : CommGroupScheme.groupHom ξ ≫ i = ψ :=
    groupHom_cocharacterAut_comp i n ν
  have hA : (Dynamic.unipotent (invGm ≫ ψ)).IsNormalizedBy
      (SubgroupFunctor.range χ) := by
    have h := Dynamic.unipotent_isNormalizedBy_range_of_common_commutativeGroup
      i (CommGroupScheme.groupHom ν) (invGm ≫ CommGroupScheme.groupHom ξ)
    simpa only [Category.assoc, hξ] using h
  have hB : (Dynamic.parabolic ψ).IsNormalizedBy (SubgroupFunctor.range χ) := by
    rw [← hξ]
    exact Dynamic.parabolic_isNormalizedBy_range_of_common_commutativeGroup
      i (CommGroupScheme.groupHom ν) (CommGroupScheme.groupHom ξ)
  have hinj : ∀ X : Over (Spec (CommRingCat.of k)), Function.Injective
      (fun z : (Dynamic.unipotent (invGm ≫ ψ)).carrier X ×
        (Dynamic.parabolic ψ).carrier X => (z.1 : X ⟶ G.X) * z.2) := by
    have h := hcell ξ
    change ∀ X : Over (Spec (CommRingCat.of k)), Function.Injective
      (fun z : (Dynamic.unipotent (invGm ≫ (CommGroupScheme.groupHom ξ ≫ i))).carrier X ×
        (Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)).carrier X =>
          (z.1 : X ⟶ G.X) * z.2) at h
    rw [hξ] at h
    exact h
  obtain ⟨a, b, ha, hb, haχ, hbχ, hu⟩ :=
    Dynamic.HasProductContraction.exists_unipotent_factors χ
      (Dynamic.unipotent (invGm ≫ ψ)) (Dynamic.parabolic ψ)
      hA hB hinj (hcontractions n u)
  have hZψχ : Dynamic.centralizer ψ ≤ Dynamic.centralizer χ := by
    rw [centralizer_conjugate_eq_torusCentralizer i χ hZ n, hZ]
  have hbψ : b ∈ (Dynamic.unipotent ψ).carrier (Over.mk (𝟙 _)) :=
    Dynamic.mem_unipotent_of_mem_unipotent_of_mem_parabolic χ ψ hZψχ hbχ hb
  refine ⟨⟨a, haχ⟩, ⟨b, hbχ⟩, hu, ?_, ?_⟩
  · apply (mem_unipotent_conjugate_iff_inv_conj (invGm ≫ χ) n a).mp
    simpa only [Category.assoc] using ha
  · exact (mem_unipotent_conjugate_iff_inv_conj χ n b).mp hbψ

/-- The contraction-derived Weyl factorization combines with the opposite-cell
intersection theorem to separate normalizing points. -/
theorem hasUnipotentNormalizerSeparation_of_productContractions
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hcell : ∀ ξ : cocharacterLattice T, HasInjectiveOppositeCellMultiplication i ξ)
    (hcontractions : HasNormalizerProductContractions i ν) :
    HasUnipotentNormalizerSeparation i ν :=
  hasUnipotentNormalizerSeparation_of_weylFactorization_of_oppositeCell i ν
    (hasUnipotentWeylFactorization_of_productContractions i ν hZ hcell hcontractions)
    (fun n a b hn => normalizer_eq_one_of_injectiveOppositeCell i ν (hcell ν) n a b hn)

/-- Unipotent covering and the contraction inputs give the actual rational
Bruhat decomposition through the published normalizer-separation assembly. -/
theorem hasRationalBruhatDecomposition_of_productContractions
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hcover : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ∃ (n : normalizerPoints i)
        (u v : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i)),
        g = u * n * v)
    (hcell : ∀ ξ : cocharacterLattice T, HasInjectiveOppositeCellMultiplication i ξ)
    (hcontractions : HasNormalizerProductContractions i ν) :
    HasRationalBruhatDecomposition i ν :=
  hasRationalBruhatDecomposition_of_unipotent_covering_and_separation i ν hZ hcover
    (hasUnipotentNormalizerSeparation_of_productContractions i ν hZ hcell hcontractions)

/-- The two Levi factorizations absorb the centralizer factors into the
normalizer and convert parabolic covering into unipotent covering. -/
theorem unipotentNormalizerCovering_of_parabolicNormalizerCovering
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hcover : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ∃ n ∈ normalizerPoints i,
        ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
        ∃ q ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
          g = p * n * q) :
    ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ∃ (n : normalizerPoints i)
        (u v : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i)),
        g = u * n * v := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  intro g
  obtain ⟨n, hn, p, hp, q, hq, heq⟩ := hcover g
  obtain ⟨⟨u, a⟩, ⟨hu, ha, hpa⟩, _⟩ :=
    RationalPoint.existsUnique_unipotent_mul_levi χ hp
  obtain ⟨⟨b, v⟩, ⟨hb, hv, hqb⟩, _⟩ :=
    RationalPoint.existsUnique_levi_mul_unipotent χ hq
  have hZpts := rationalLevi_eq_centralizerPoints_of_eq i ν hZ
  have haZ : a ∈ centralizerPoints i := hZpts ▸ ha
  have hbZ : b ∈ centralizerPoints i := hZpts ▸ hb
  let aN : normalizerPoints i := ⟨a, centralizerPoints_le_normalizerPoints i haZ⟩
  let bN : normalizerPoints i := ⟨b, centralizerPoints_le_normalizerPoints i hbZ⟩
  refine ⟨aN * ⟨n, hn⟩ * bN, ⟨u, hu⟩, ⟨v, hv⟩, ?_⟩
  simpa only [hpa, hqb, aN, bN, Subgroup.coe_mul, mul_assoc] using heq

/-- In an affine ambient group, parabolic covering and genuine opposite-cell
product contractions give the rational Bruhat decomposition. -/
theorem hasRationalBruhatDecomposition_of_parabolicCovering_and_productContractions
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hcover : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ∃ n ∈ normalizerPoints i,
        ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
        ∃ q ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
          g = p * n * q)
    (hcontractions : HasNormalizerProductContractions i ν) :
    HasRationalBruhatDecomposition i ν :=
  hasRationalBruhatDecomposition_of_productContractions i ν hZ
    (unipotentNormalizerCovering_of_parabolicNormalizerCovering i ν hZ hcover)
    (fun ξ => hasInjectiveOppositeCellMultiplication_of_isAffine i ξ) hcontractions

end Langlands.GroupScheme
