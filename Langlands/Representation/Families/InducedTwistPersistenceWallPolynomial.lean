import Langlands.Representation.Families.InducedTwistPersistenceAssembly
import Langlands.Representation.Classification.SegmentHeadSupportGeneric
import Langlands.Representation.Classification.CuspidalProductContragredient

/-! # One polynomial for each rank-one wall

Let `σ` be a supercuspidal irreducible representation of `L(k)`, let `R₀` be a parabolic of
`G` with Levi `L`, and let `Z ψ s` be a family of representations of `G(k)` whose Jacquet
modules along every parabolic `R` with Levi `L` are subquotients of `r_R(i_{R₀}(σψ))`.
For a rank-one wall at which `A_M` is not central, `exists_polynomial_wall_isIrreducible`
gives one nonzero polynomial on `X(M)` off whose zero set the irreducibility hypothesis of the
wall step holds for the whole family. It takes the product over the finitely many
representatives of `N_G(L)(k)/L(k)` of the polynomials of
`exists_polynomial_isIrreducible_wall`.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.InducedTwistPersistence

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

section Subquotient

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance persistenceSubquotientAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- If `I ↪ T`, then the Jacquet module of a quotient of `I` is a subquotient of the Jacquet
module of `T`. -/
theorem isSubquotient_leviJacquet_quotient_of_injective
    {I T : SmoothRep.{0, u, v} ℂ (rationalPoints G)} (ιI : I ⟶ T)
    (hιI : Function.Injective (SmoothRep.hom ιI)) (S : Subrepresentation I.representation)
    {R L N : GroupScheme (Spec (CommRingCat.of k))} (r : R ⟶ G) (lR : L ⟶ R) (nR : N ⟶ R)
    (hr : IsParabolicSubgroup r) (hlR : IsRationalLeviSubgroup lR)
    (hnR : LeviSubgroup.IsGeometricUnipotentRadical nR)
    (hmulR : IsIso (subgroupMultiplication lR nR)) :
    letI := leviPointTopology lR hlR
    SmoothRep.IsSubquotient ((leviJacquetFunctor r lR nR hr hnR hlR hmulR).obj
        (SmoothRep.quotient I S))
      ((leviJacquetFunctor r lR nR hr hnR hlR hmulR).obj T) := by
  let := leviPointTopology lR hlR
  exact SmoothRep.isSubquotient_iff_exists.mpr ⟨_,
    (leviJacquetFunctor r lR nR hr hnR hlR hmulR).map ιI,
    (leviJacquetFunctor r lR nR hr hnR hlR hmulR).map (SmoothRep.mkQ I S),
    leviJacquetFunctor_map_injective r lR nR hr hlR hnR hmulR ιI hιI,
    leviJacquet_map_surjective r lR nR hr hlR hnR hmulR _ (SmoothRep.mkQ_surjective I S)⟩

end Subquotient

section WallPolynomial

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance persistenceWallPolynomialAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {M L : GroupScheme (Spec (CommRingCat.of k))} [IsAffine M.X.left] [IsAffine L.X.left]

local instance persistenceWallPolynomialMTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology k M.X

local instance persistenceWallPolynomialLTopology : TopologicalSpace (rationalPoints L) :=
  rationalPointTopology k L.X

set_option maxHeartbeats 2000000 in
/-- **One polynomial per wall.** See the module docstring. The twists `θ ψ` of `σ` are the
restrictions of `ψ` to `L(k)`, and `χ0 ψ` is an `A_L`-exponent of `σ ⊗ θ ψ`. -/
theorem exists_polynomial_wall_isIrreducible
    (hVI : Renard.AlgebraicFamily.GenericInducedIrreducibilityStatement.{u, max u v})
    (hWS : Plancherel.WallUnramifiedTwistSurjectivityStatement.{u})
    (hG : IsConnectedReductive G)
    {P Q R₀ NR₀ : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (q : Q ⟶ M) (lQ : L ⟶ Q) (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    {A B : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) {b : A.toGrp ⟶ L} (hba : b ≫ lQ ≫ q = a)
    {bL : B.toGrp ⟶ L} (hbL : IsSplitComponent bL)
    (r₀ : R₀ ⟶ G) (lR₀ : L ⟶ R₀) (nR₀ : NR₀ ⟶ R₀) (hr₀ : IsParabolicSubgroup r₀)
    (hlR₀ : IsRationalLeviSubgroup lR₀) (hnR₀ : LeviSubgroup.IsGeometricUnipotentRadical nR₀)
    (hmulR₀ : IsIso (subgroupMultiplication lR₀ nR₀)) (hR₀j : lR₀ ≫ r₀ = lQ ≫ q ≫ l ≫ p)
    {nW : ℕ} (gW : Fin nW → rationalPoints G) (φW : Fin nW → (L ≅ L))
    (hφW : ∀ j, (φW j).hom ≫ lR₀ ≫ r₀ = lR₀ ≫ r₀ ≫ (G.innerIso (gW j)).hom)
    (hgW : ∀ (w : rationalPoints G) (φ' : L ≅ L),
      φ'.hom ≫ lR₀ ≫ r₀ = lR₀ ≫ r₀ ≫ (G.innerIso w).hom →
        ∃ (j : Fin nW) (m : rationalPoints L), w = gW j * rationalPoints.map (lR₀ ≫ r₀) m)
    (σ : SmoothRep.{0, u, v} ℂ (rationalPoints L)) (hσ : σ.IsIrreducible)
    (θ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul) → (rationalPoints L →* ℂˣ))
    (hθ : ∀ ψ, IsOpen ((θ ψ).ker : Set (rationalPoints L)))
    (hθψ : ∀ ψ z, (θ ψ z : ℂ) = ψ.val (rationalPoints.map (lQ ≫ q) z))
    (hσθsc : ∀ ψ, haveI := hlR₀.isConnectedReductive.isAffineHom
      letI := leviPointTopology lR₀ hlR₀
      haveI := leviPoints_locallyCompactSpace r₀ lR₀ hr₀ hlR₀
      haveI := leviPoints_nonarchimedeanGroup r₀ lR₀ hr₀ hlR₀
      ∀ (P' L' U' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ L) (l' : L' ⟶ P') (u' : U' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hu' : LeviSubgroup.IsGeometricUnipotentRadical u')
        (hmul' : IsIso (subgroupMultiplication l' u')),
        ¬ IsIso p' →
          Subsingleton ((jacquetFunctor p' l' u' hp' hu' hl' hmul').obj
            (σ.twist (θ ψ) (hθ ψ))))
    (χ0 : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul) → rationalPoints B.toGrp →* ℂˣ)
    (hχ0 : ∀ ψ, IsGeneralizedEigencharacter
      ((σ.twist (θ ψ) (hθ ψ)).representation.comp (rationalPoints.map bL)) (χ0 ψ))
    {Ix : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul) → Type w}
    (Z : ∀ ψ, Ix ψ → SmoothRep.{0, u, max u v} ℂ (rationalPoints G))
    (hsub : ∀ ψ s, ∀ (R N : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G) (lR : L ⟶ R)
      (nR : N ⟶ R) (hr : IsParabolicSubgroup r) (hlR : IsRationalLeviSubgroup lR)
      (hnR : LeviSubgroup.IsGeometricUnipotentRadical nR)
      (hmulR : IsIso (subgroupMultiplication lR nR)), lR ≫ r = lQ ≫ q ≫ l ≫ p →
      letI := leviPointTopology lR hlR
      SmoothRep.IsSubquotient ((leviJacquetFunctor r lR nR hr hnR hlR hmulR).obj (Z ψ s))
        ((leviJacquetFunctor.{u, max u v} r lR nR hr hnR hlR hmulR).obj
          ((leviInductionFunctor r₀ lR₀ nR₀ hr₀ hnR₀ hlR₀ hmulR₀).obj (σ.twist (θ ψ) (hθ ψ)))))
    {F F' : SubgroupFunctor G} (d : RationalRankOneWallData (lQ ≫ q ≫ l ≫ p) F F')
    (hd : ¬ IsCentral (b ≫ d.l ≫ d.q))
    {V₁ : GroupScheme (Spec (CommRingCat.of k))} (v₁ : V₁ ⟶ d.Q)
    (hv₁ : LeviSubgroup.IsGeometricUnipotentRadical v₁)
    (hmulQ₁ : IsIso (subgroupMultiplication d.l v₁)) :
    ∃ g : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, g ≠ 0 ∧
      ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive g,
        ∀ s : Ix ψ,
          haveI := d.levi.isConnectedReductive.isAffineHom
          letI : TopologicalSpace (rationalPoints d.M) := leviPointTopology d.m d.levi
          haveI := leviPoints_locallyCompactSpace d.p d.m d.parabolic d.levi
          haveI := leviPoints_nonarchimedeanGroup d.p d.m d.parabolic d.levi
          letI := leviPointTopology d.l d.innerLevi
          ∀ C : SmoothRep.{0, u, max u v} ℂ (rationalPoints L), C.IsIrreducible →
            ∀ (R N : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G) (lR : L ⟶ R)
              (nR : N ⟶ R) (hr : IsParabolicSubgroup r) (hlR : IsRationalLeviSubgroup lR)
              (hnR : LeviSubgroup.IsGeometricUnipotentRadical nR)
              (hmulR : IsIso (subgroupMultiplication lR nR)), lR ≫ r = lQ ≫ q ≫ l ≫ p →
              (∃ jC : C ⟶ (leviJacquetFunctor r lR nR hr hnR hlR hmulR).obj (Z ψ s),
                Function.Injective (SmoothRep.hom jC)) →
              IsGeneralizedEigencharacter (C.representation.comp (rationalPoints.map bL))
                (χ0 ψ) →
              ((leviInductionFunctor d.q d.l v₁ d.innerParabolic hv₁ d.innerLevi
                hmulQ₁).obj C).IsIrreducible := by
  classical
  have hM := hl.isConnectedReductive
  have hM₁ := d.levi.isConnectedReductive
  have := hM₁.isAffineHom
  have : IsAffine d.M.X.left := isAffine_of_isAffineHom d.M.X.hom
  let : TopologicalSpace (rationalPoints d.M) := leviPointTopology d.m d.levi
  have := leviPoints_locallyCompactSpace d.p d.m d.parabolic d.levi
  have := leviPoints_nonarchimedeanGroup d.p d.m d.parabolic d.levi
  have hsurj := hWS k G hG P M Q L d.P d.M d.Q p l q lQ d.p d.m d.q d.l hp hl hq hlQ
    d.parabolic d.levi d.innerParabolic d.innerLevi
    (by simpa only [Category.assoc] using d.levi_comp.symm) d.proper d.maximal A a b ha hba hd
  have hgen := fun jj => exists_polynomial_isIrreducible_wall hVI hM hM₁ d.q d.l v₁
    d.innerParabolic d.innerLevi hv₁ hmulQ₁ (lQ ≫ q) hsurj (φW jj) hbL σ hσ
  choose gs hgs0 hgsD using hgen
  refine ⟨∏ jj, gs jj, Finset.prod_ne_zero_iff.mpr fun jj _ => hgs0 jj, ?_⟩
  intro ψ hψ s C hC R N r lR nR hr hlR hnR hmulR hj hjC hCχ
  obtain ⟨jC, hjC⟩ := hjC
  have hψj := (mem_rationalUnramifiedPrincipalOpen_prod l hl Finset.univ gs ψ).mp hψ
  obtain ⟨-, hXsc, hXcl⟩ := pieces_of_supercuspidal_normalizer r₀ lR₀ nR₀ hr₀ hlR₀ hnR₀
    hmulR₀ r lR nR hr hlR hnR hmulR hG (hj.trans hR₀j.symm) gW φW hφW hgW
    (σ.twist (θ ψ) (hθ ψ)) ((SmoothRep.isIrreducible_twist_iff _ _ σ).mpr hσ) (hσθsc ψ)
  have hCX := Classification.SegmentHeadSupport.isSubquotient_trans
    (SmoothRep.IsSubrepresentation.isSubquotient ⟨jC, hjC⟩)
    (hsub ψ s R N r lR nR hr hlR hnR hmulR hj)
  obtain ⟨jj, hE⟩ := hXcl C hC hCX
  have := d.innerLevi.isConnectedReductive.isAffineHom
  have := leviPoints_locallyCompactSpace d.q d.l d.innerParabolic d.innerLevi
  have := leviPoints_nonarchimedeanGroup d.q d.l d.innerParabolic d.innerLevi
  exact hgsD jj ψ (hψj jj (Finset.mem_univ _)) (θ ψ) (hθ ψ) (hθψ ψ) C hC
    (IsSupercuspidal.of_isSubquotient hCX hXsc) hE (χ0 ψ) (hχ0 ψ) hCχ

end WallPolynomial

end Langlands.InducedTwistPersistence
