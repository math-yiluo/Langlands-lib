import Langlands.Representation.Families.InducedTwistPersistenceWall
import Langlands.Representation.Exponents.LeviSecondAdjointnessStatement
import Langlands.GroupScheme.Rational.ParabolicGallery
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterDensity

/-! # Transport of an exponent along a rank-one gallery

Fix an embedded rational Levi `j : L → G`, a central `b_L : B → L` and an admissible `Z`.
`PersistenceInvariant j b_L Z χ F` says that some actual rational parabolic `R` with range `F`
and Levi embedding `j` has `χ` as a `B`-exponent of `r_R(Z)`. One rank-one wall carries the
invariant from the far vertex to the near vertex (`persistenceInvariant_of_wall`), and a
finite gallery carries it along all its walls, for every point off one nonzero polynomial
on `X(M)` (`exists_polynomial_persistenceInvariant_of_gallery`).
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.InducedTwistPersistence

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

section Points

variable {k : Type u} [Field k]

/-- If `range q = F.comap f` and `range r = F`, then on rational points
`(q ≫ f)(Q(k)) = f(M(k)) ∩ r(R(k))`. -/
theorem pointImage_comp_eq_inf_of_range_eq_comap
    {G M Q R : GroupScheme (Spec (CommRingCat.of k))} (q : Q ⟶ M) (f : M ⟶ G) (r : R ⟶ G)
    {F : SubgroupFunctor G} (hq : SubgroupFunctor.range q = F.comap f)
    (hr : SubgroupFunctor.range r = F) :
    pointImage (q ≫ f) = pointImage f ⊓ pointImage r := by
  rw [pointImage_eq_range_carrier, pointImage_eq_range_carrier, pointImage_eq_range_carrier, hr]
  ext x
  rw [Subgroup.mem_inf, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y ≫ q.hom.hom ∈ (F.comap f).carrier _ := by
      rw [← hq]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    have hy' := SubgroupFunctor.mem_comap.mp hy
    refine ⟨⟨y ≫ q.hom.hom, by rw [Grp.comp_hom_hom, Category.assoc]⟩, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact hy'
  · rintro ⟨⟨z, rfl⟩, hz⟩
    have hz' : z ∈ (F.comap f).carrier _ := SubgroupFunctor.mem_comap.mpr hz
    rw [← hq] at hz'
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hz'
    exact ⟨y, by rw [Grp.comp_hom_hom, Category.assoc]⟩

/-- Containment of ranges gives containment of rational point images. -/
theorem pointImage_le_of_range_le {G P R : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (r : R ⟶ G) {F : SubgroupFunctor G} (hr : SubgroupFunctor.range r = F)
    (hF : F ≤ SubgroupFunctor.range p) : pointImage r ≤ pointImage p := by
  rw [pointImage_eq_range_carrier, pointImage_eq_range_carrier, hr]
  exact hF _

end Points

section Gallery

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance persistenceGalleryAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {L : GroupScheme (Spec (CommRingCat.of k))} {B : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Some actual rational parabolic with range `F` and Levi embedding `j` has `χ` as an
exponent of the central `b_L : B → L` on the Jacquet module of `Z`. -/
def PersistenceInvariant (j : L ⟶ G) (bL : B.toGrp ⟶ L)
    (Z : SmoothRep.{0, u, w} ℂ (rationalPoints G)) (χ : rationalPoints B.toGrp →* ℂˣ)
    (F : SubgroupFunctor G) : Prop :=
  ∃ (R N : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G) (lR : L ⟶ R) (nR : N ⟶ R)
    (hr : IsParabolicSubgroup r) (hlR : IsRationalLeviSubgroup lR)
    (hnR : LeviSubgroup.IsGeometricUnipotentRadical nR)
    (hmulR : IsIso (subgroupMultiplication lR nR)),
    lR ≫ r = j ∧ SubgroupFunctor.range r = F ∧
      letI := leviPointTopology lR hlR
      IsGeneralizedEigencharacter
        (((leviJacquetFunctor r lR nR hr hnR hlR hmulR).obj Z).representation.comp
          (rationalPoints.map bL)) χ

set_option maxHeartbeats 1000000 in
/-- **One wall.** Across a rank-one wall from `F` (the side of `d.q`) to `F'`, the invariant
passes from `F'` to `F`, given second adjointness, finite length of all Jacquet modules of
`Z` along parabolics with Levi `j`, and irreducibility of `i^{M₁}_{Q₁}(C)` for the irreducible
subrepresentations `C` with exponent `χ` of those Jacquet modules. -/
theorem persistenceInvariant_of_wall (hG : IsConnectedReductive G)
    (hadj : LeviSecondAdjointnessStatement.{u, v})
    {j : L ⟶ G} {F F' : SubgroupFunctor G} (hF : IsRationalParabolicWithLevi j F)
    (d : RationalRankOneWallData j F F')
    {N₁ V₁ V₁' : GroupScheme (Spec (CommRingCat.of k))}
    (n₁ : N₁ ⟶ d.P) (hn₁ : LeviSubgroup.IsGeometricUnipotentRadical n₁)
    (hmul₁ : IsIso (subgroupMultiplication d.m n₁))
    (v₁ : V₁ ⟶ d.Q) (hv₁ : LeviSubgroup.IsGeometricUnipotentRadical v₁)
    (hmulQ₁ : IsIso (subgroupMultiplication d.l v₁))
    (v₁' : V₁' ⟶ d.Q') (hv₁' : LeviSubgroup.IsGeometricUnipotentRadical v₁')
    (hmulQ₁' : IsIso (subgroupMultiplication d.l' v₁'))
    {bL : B.toGrp ⟶ L} (hbL : IsCentral bL) (χ : rationalPoints B.toGrp →* ℂˣ)
    (Z : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) (hZ : Z.IsAdmissible)
    (hfl : ∀ (R N : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G) (lR : L ⟶ R)
      (nR : N ⟶ R) (hr : IsParabolicSubgroup r) (hlR : IsRationalLeviSubgroup lR)
      (hnR : LeviSubgroup.IsGeometricUnipotentRadical nR)
      (hmulR : IsIso (subgroupMultiplication lR nR)), lR ≫ r = j →
      letI := leviPointTopology lR hlR
      haveI := leviPoints_locallyCompactSpace r lR hr hlR
      haveI := leviPoints_nonarchimedeanGroup r lR hr hlR
      ((leviJacquetFunctor r lR nR hr hnR hlR hmulR).obj Z).HasFiniteLength)
    (hirr : haveI := d.levi.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints d.M) := leviPointTopology d.m d.levi
      haveI := leviPoints_locallyCompactSpace d.p d.m d.parabolic d.levi
      haveI := leviPoints_nonarchimedeanGroup d.p d.m d.parabolic d.levi
      letI := leviPointTopology d.l d.innerLevi
      ∀ C : SmoothRep.{0, u, max u v} ℂ (rationalPoints L), C.IsIrreducible →
        ∀ (R N : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G) (lR : L ⟶ R)
          (nR : N ⟶ R) (hr : IsParabolicSubgroup r) (hlR : IsRationalLeviSubgroup lR)
          (hnR : LeviSubgroup.IsGeometricUnipotentRadical nR)
          (hmulR : IsIso (subgroupMultiplication lR nR)), lR ≫ r = j →
          (∃ jC : C ⟶ (leviJacquetFunctor r lR nR hr hnR hlR hmulR).obj Z,
            Function.Injective (SmoothRep.hom jC)) →
          IsGeneralizedEigencharacter (C.representation.comp (rationalPoints.map bL)) χ →
          ((leviInductionFunctor d.q d.l v₁ d.innerParabolic hv₁ d.innerLevi hmulQ₁).obj
            C).IsIrreducible)
    (h : PersistenceInvariant j bL Z χ F') : PersistenceInvariant j bL Z χ F := by
  obtain ⟨R', NR', r', lR', nR', hr', hlR', hnR', hmulR', hR'j, hR'F, hexp⟩ := h
  obtain ⟨R, r, lR, hr, hlR, hRj, hRF⟩ := hF
  obtain ⟨NR, nR, hnR, hmulR⟩ := hlR.exists_unipotentRadical
  have hM₁ := d.levi.isConnectedReductive
  have := hM₁.isAffineHom
  let : TopologicalSpace (rationalPoints d.M) := leviPointTopology d.m d.levi
  have := leviPoints_locallyCompactSpace d.p d.m d.parabolic d.levi
  have := leviPoints_nonarchimedeanGroup d.p d.m d.parabolic d.levi
  have hopp : pointImage d.q ⊓ pointImage d.q' = pointImage (d.l ≫ d.q) := by
    rw [pointImage_eq_range_carrier, pointImage_eq_range_carrier, pointImage_eq_range_carrier,
      ← d.opposite]
    rfl
  obtain ⟨adj⟩ := hadj k d.M hM₁ d.Q d.Q' L V₁ V₁' d.q d.l v₁ d.innerParabolic d.innerLevi
    hv₁ hmulQ₁ d.q' d.l' v₁' d.innerParabolic' d.innerLevi' hv₁' hmulQ₁' d.commonLevi hopp
  refine ⟨R, NR, r, lR, nR, hr, hlR, hnR, hmulR, hRj, hRF, ?_⟩
  exact isGeneralizedEigencharacter_wall hG d.p d.m n₁ d.parabolic d.levi hn₁ hmul₁
    d.q d.l v₁ d.innerParabolic d.innerLevi hv₁ hmulQ₁
    d.q' d.l' v₁' d.innerParabolic' d.innerLevi' hv₁' hmulQ₁'
    r lR nR hr hlR hnR hmulR r' lR' nR' hr' hlR' hnR' hmulR'
    (pointImage_le_of_range_le d.p r hRF d.contained)
    (by rw [← Category.assoc]; exact d.levi_comp.trans hRj.symm)
    (pointImage_comp_eq_inf_of_range_eq_comap d.q (d.m ≫ d.p) r d.intersection hRF)
    (pointImage_le_of_range_le d.p r' hR'F d.contained')
    (by rw [← Category.assoc, d.commonLevi]; exact d.levi_comp.trans hR'j.symm)
    (pointImage_comp_eq_inf_of_range_eq_comap d.q' (d.m ≫ d.p) r' d.intersection' hR'F)
    adj hbL χ Z hZ (hfl R' NR' r' lR' nR' hr' hlR' hnR' hmulR' hR'j) hexp
    (fun C hC hjC hCχ => hirr C hC R' NR' r' lR' nR' hr' hlR' hnR' hmulR' hR'j hjC hCχ)

variable {M : GroupScheme (Spec (CommRingCat.of k))} [IsAffine M.X.left]

local instance persistenceGalleryMTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology k M.X

omit [T2Space k] in
/-- The principal open set of a product is the intersection of the principal open sets. -/
theorem mem_rationalUnramifiedPrincipalOpen_mul (hM : IsConnectedReductive M)
    (g₁ g₂ : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ)
    (ψ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul)) :
    ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hM (g₁ * g₂) ↔
      ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hM g₁ ∧
        ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hM g₂ := by
  simp only [Plancherel.mem_rationalUnramifiedPrincipalOpen, map_mul, ne_eq, mul_eq_zero, not_or]

/-- **Gallery.** Let `Z ψ s` be a family of admissible representations, indexed by
`ψ ∈ X(M)` and `s ∈ Ix ψ`, with exponents `χ ψ s`. Suppose that for every wall of the
gallery, with `b` noncentral in the wall Levi, and every radical of its near inner
parabolic, there is a nonzero polynomial off whose zero set the irreducibility hypothesis of
`persistenceInvariant_of_wall` holds for the whole family. Then there is one nonzero
polynomial off whose zero set the invariant passes from the far end of the gallery to the
near end. -/
theorem exists_polynomial_persistenceInvariant_of_gallery (hG : IsConnectedReductive G)
    (hadj : LeviSecondAdjointnessStatement.{u, v}) (hM : IsConnectedReductive M)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {b : A.toGrp ⟶ L} {j : L ⟶ G}
    {bL : B.toGrp ⟶ L} (hbL : IsCentral bL)
    {Ix : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul) → Type w}
    (Z : ∀ ψ, Ix ψ → SmoothRep.{0, u, max u v} ℂ (rationalPoints G))
    (χ : ∀ ψ, Ix ψ → rationalPoints B.toGrp →* ℂˣ)
    (hZ : ∀ ψ s, (Z ψ s).IsAdmissible)
    (hfl : ∀ ψ s, ∀ (R N : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G) (lR : L ⟶ R)
      (nR : N ⟶ R) (hr : IsParabolicSubgroup r) (hlR : IsRationalLeviSubgroup lR)
      (hnR : LeviSubgroup.IsGeometricUnipotentRadical nR)
      (hmulR : IsIso (subgroupMultiplication lR nR)), lR ≫ r = j →
      letI := leviPointTopology lR hlR
      haveI := leviPoints_locallyCompactSpace r lR hr hlR
      haveI := leviPoints_nonarchimedeanGroup r lR hr hlR
      ((leviJacquetFunctor r lR nR hr hnR hlR hmulR).obj (Z ψ s)).HasFiniteLength)
    (hwall : ∀ (F F' : SubgroupFunctor G) (d : RationalRankOneWallData j F F'),
      ¬ IsCentral (b ≫ d.l ≫ d.q) →
      ∀ (V₁ : GroupScheme (Spec (CommRingCat.of k))) (v₁ : V₁ ⟶ d.Q)
        (hv₁ : LeviSubgroup.IsGeometricUnipotentRadical v₁)
        (hmulQ₁ : IsIso (subgroupMultiplication d.l v₁)),
        ∃ g : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, g ≠ 0 ∧
          ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hM g, ∀ s : Ix ψ,
            haveI := d.levi.isConnectedReductive.isAffineHom
            letI : TopologicalSpace (rationalPoints d.M) := leviPointTopology d.m d.levi
            haveI := leviPoints_locallyCompactSpace d.p d.m d.parabolic d.levi
            haveI := leviPoints_nonarchimedeanGroup d.p d.m d.parabolic d.levi
            letI := leviPointTopology d.l d.innerLevi
            ∀ C : SmoothRep.{0, u, max u v} ℂ (rationalPoints L), C.IsIrreducible →
              ∀ (R N : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G) (lR : L ⟶ R)
                (nR : N ⟶ R) (hr : IsParabolicSubgroup r) (hlR : IsRationalLeviSubgroup lR)
                (hnR : LeviSubgroup.IsGeometricUnipotentRadical nR)
                (hmulR : IsIso (subgroupMultiplication lR nR)), lR ≫ r = j →
                (∃ jC : C ⟶ (leviJacquetFunctor r lR nR hr hnR hlR hmulR).obj (Z ψ s),
                  Function.Injective (SmoothRep.hom jC)) →
                IsGeneralizedEigencharacter (C.representation.comp (rationalPoints.map bL))
                  (χ ψ s) →
                ((leviInductionFunctor d.q d.l v₁ d.innerParabolic hv₁ d.innerLevi
                  hmulQ₁).obj C).IsIrreducible)
    {F F' : SubgroupFunctor G}
    (hgal : Relation.ReflTransGen (IsRationalRankOneWallAvoiding b j) F F') :
    ∃ g : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, g ≠ 0 ∧
      ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hM g, ∀ s : Ix ψ,
        PersistenceInvariant j bL (Z ψ s) (χ ψ s) F' →
          PersistenceInvariant j bL (Z ψ s) (χ ψ s) F := by
  induction hgal using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨1, one_ne_zero, fun _ _ _ h => h⟩
  | head hstep _ ih =>
    obtain ⟨g₀, hg₀, hg₀D⟩ := ih
    obtain ⟨hF, -, d, hd⟩ := hstep
    obtain ⟨N₁, n₁, hn₁, hmul₁⟩ := d.levi.exists_unipotentRadical
    obtain ⟨V₁, v₁, hv₁, hmulQ₁⟩ := d.innerLevi.exists_unipotentRadical
    obtain ⟨V₁', v₁', hv₁', hmulQ₁'⟩ := d.innerLevi'.exists_unipotentRadical
    obtain ⟨g₁, hg₁, hg₁D⟩ := hwall _ _ d hd V₁ v₁ hv₁ hmulQ₁
    refine ⟨g₀ * g₁, mul_ne_zero hg₀ hg₁, fun ψ hψ s hs => ?_⟩
    rw [mem_rationalUnramifiedPrincipalOpen_mul] at hψ
    exact persistenceInvariant_of_wall hG hadj hF d n₁ hn₁ hmul₁ v₁ hv₁ hmulQ₁ v₁' hv₁'
      hmulQ₁' hbL (χ ψ s) (Z ψ s) (hZ ψ s) (hfl ψ s) (hg₁D ψ hψ.2 s) (hg₀D ψ hψ.1 s hs)

end Gallery

end Langlands.InducedTwistPersistence
