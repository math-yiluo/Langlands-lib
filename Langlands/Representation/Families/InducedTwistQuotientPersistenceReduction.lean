import Langlands.Representation.Families.InducedTwistPersistenceWallPolynomial
import Langlands.Representation.Families.InducedTwistQuotientExponentStatements
import Langlands.Representation.Families.InducedTwistsDetectionOpposite
import Langlands.Representation.Exponents.LeviCuspidalEmbeddingProof
import Langlands.Representation.Exponents.LeviParabolicExtensionProof
import Langlands.Representation.Classification.CuspidalProductContragredient
import Langlands.GroupScheme.Rational.ParabolicGalleryStatement

/-! # Persistence of the inducing exponent, from four named inputs

The persistence proposition `InducedTwistQuotientPersistenceStatement` follows from
Renard VI.8.5 (generic irreducibility of induction from a maximal parabolic), the
surjectivity of the unramified twists at a rank-one wall, the existence of rank-one galleries
avoiding the walls at which `A_M` stays central, and second adjointness.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme
  Langlands.InducedTwistPersistence

set_option maxHeartbeats 600000 in
/-- **Persistence, conditional form.** Renard VI.8.5 (at carrier universe `max u v`), wall
twist surjectivity, galleries avoiding the walls where `A_M` stays central, and second
adjointness imply `InducedTwistQuotientPersistenceStatement`. -/
theorem inducedTwistQuotientPersistence_of_statements
    (hVI : GenericInducedIrreducibilityStatement.{u, max u v})
    (hWS : Plancherel.WallUnramifiedTwistSurjectivityStatement.{u})
    (hgal : RationalParabolicGalleryAvoidingStatement.{u})
    (hadj : LeviSecondAdjointnessStatement.{u, v}) :
    InducedTwistQuotientPersistenceStatement.{u, v} := by
  intro k _ _ _ _ _ G hG _ _ P M U p l r hp hl hr hmul A a ha ρ hρ hρadm
  classical
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have hM := hl.isConnectedReductive
  have := hM.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  -- a supercuspidal `σ` of a Levi `L` of a parabolic `Q` of `M` with `ρ ↪ i^M_Q(σ)`
  obtain ⟨Q, L, V, q, lQ, vQ, hq, hlQ, hvQ, hmulQ, -, -, σ, hσ, hσsc, ⟨qJ, hqJ⟩, ⟨fc, hfc⟩⟩ :=
    leviCuspidalEmbedding k M hM ρ hρ
  have hL : IsConnectedReductive L := hlQ.isConnectedReductive
  have := hL.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  -- the split components
  obtain ⟨B, bL, b, e, hbL, hba, hbs, hbc, he⟩ := exists_splitComponent_factor hM q lQ hq hlQ ha
  have he₂ : e ≫ bL ≫ lQ ≫ q = a := by rw [← Category.assoc, he, hba]
  -- `σ` is admissible
  have hJadm : ((leviJacquetFunctor q lQ vQ hq hvQ hlQ hmulQ).obj ρ).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv _ (leviPointsEquiv q lQ hq hlQ)
      (arbitraryParabolicJacquetAdmissibility k M hM Q L V q lQ vQ hq hlQ hvQ hmulQ ρ hρadm)
  have hσadm : σ.IsAdmissible :=
    isAdmissible_of_surjective_coefficients (exists_compact_openSubgroup_le _) qJ hqJ hJadm
  -- the unramified twists of `σ`
  let θ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul) → (rationalPoints L →* ℂˣ) :=
    fun ψ => leviRestrictedCharacter q lQ (ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom
  have hθ : ∀ ψ, IsOpen ((θ ψ).ker : Set (rationalPoints L)) := fun ψ =>
    isOpen_ker_leviRestrictedCharacter q lQ hq hlQ (ψ : rationalPoints M →ₜ* ℂˣ)
  have hσθirr : ∀ ψ, (σ.twist (θ ψ) (hθ ψ)).IsIrreducible := fun ψ =>
    (SmoothRep.isIrreducible_twist_iff _ _ σ).mpr hσ
  have hσθadm : ∀ ψ, (σ.twist (θ ψ) (hθ ψ)).IsAdmissible := fun ψ =>
    (SmoothRep.isAdmissible_twist_iff _ _ σ).mpr hσadm
  have hσθsc : ∀ ψ, IsSupercuspidal (σ.twist (θ ψ) (hθ ψ)) := by
    intro ψ P' L' U' p' l' u' hp' hl' hu' hmul' hproper
    have h := properJacquet_subsingleton_unramifiedTwist
      (Plancherel.rationalUnramifiedCharacterRestrict (lQ ≫ q) ψ) σ hσsc P' L' U' p' l' u'
      hp' hl' hu' hmul' hproper
    have hθeq : (Plancherel.rationalUnramifiedCharacterRestrict (lQ ≫ q) ψ).val.toMonoidHom =
        θ ψ := MonoidHom.ext fun _ => rfl
    rw [twist_eq_of_eq σ hθeq _ (hθ ψ)] at h
    exact h
  -- the exponents of the twists on `A_L`
  have hexχ : ∀ ψ, ∃ χ : rationalPoints B.toGrp →* ℂˣ, IsGeneralizedEigencharacter
      ((σ.twist (θ ψ) (hθ ψ)).representation.comp (rationalPoints.map bL)) χ := fun ψ =>
    exists_isGeneralizedEigencharacter_of_isAdmissible (rationalPoints.map bL)
      hbL.1.2.map_mem_center _ (hσθirr ψ) (hσθadm ψ)
  choose χ0 hχ0 using hexχ
  -- `ρψ ↪ i^M_Q(σψ)`
  have hfψ : ∀ ψ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul),
      ∃ f : (ρ.twist ψ.val.toMonoidHom
          (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).representation.IntertwiningMap
        ((leviInductionFunctor q lQ vQ hq hvQ hlQ hmulQ).obj
          (σ.twist (θ ψ) (hθ ψ))).representation, Function.Injective f := by
    intro ψ
    exact ⟨(SmoothRep.hom (leviInductionUnramifiedTwistIso q lQ vQ hq hvQ hlQ hmulQ ψ σ).inv).comp
      (Langlands.twistIntertwining _ fc),
      ((SmoothRep.mono_iff_injective
        (leviInductionUnramifiedTwistIso q lQ vQ hq hvQ hlQ hmulQ ψ σ).inv).mp
          inferInstance).comp hfc⟩
  choose fψ hfψ using hfψ
  have hρψirr : ∀ ψ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul),
      (ρ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).IsIrreducible :=
    fun ψ => (SmoothRep.isIrreducible_twist_iff _ _ ρ).mpr hρ
  have hρψadm : ∀ ψ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul),
      (ρ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).IsAdmissible :=
    fun ψ => (SmoothRep.isAdmissible_twist_iff _ _ ρ).mpr hρadm
  have hfψ0 : ∀ ψ, fψ ψ ≠ 0 := fun ψ => by
    have := nontrivial_of_isIrreducible (hρψirr ψ)
    exact intertwiningMap_ne_zero_of_injective _ (hfψ ψ)
  -- parabolics of `G` with Levi `L`, inside `P` and inside the opposite of `P`
  obtain ⟨R₀, NR₀, r₀, lR₀, nR₀, hr₀, hlR₀, hnR₀, hmulR₀, hR₀j, hR₀P, hR₀Q⟩ :=
    leviParabolicExtension k G hG P M U p l r hp hl hr hmul Q L V q lQ vQ hq hlQ hvQ hmulQ
  obtain ⟨Pb, Nb, pb, mb, nb, -, hpb, hmb, hnb, hmulb, hmbc, hopp, -, -, -⟩ :=
    InducedTwistsDetection.exists_opposite_parabolic hG hp hl
  obtain ⟨R₁, NR₁, r₁, lR₁, nR₁, hr₁, hlR₁, hnR₁, hmulR₁, hR₁j, hR₁P, hR₁Q⟩ :=
    leviParabolicExtension k G hG Pb M Nb pb mb nb hpb hmb hnb hmulb Q L V q lQ vQ hq hlQ hvQ
      hmulQ
  have hR₁j' : lR₁ ≫ r₁ = lQ ≫ q ≫ l ≫ p := by rw [hR₁j, hmbc]
  -- representatives of `N_G(L)(k)/L(k)`
  obtain ⟨nW, gW, hφex, hgW⟩ := leviNormalizerFiniteQuotient k G hG R₀ L r₀ lR₀ hr₀ hlR₀
  choose φW hφW using hφex
  -- `i_P(ρψ) ↪ i_{R₀}(σψ)`
  obtain ⟨⟨eI⟩, -⟩ := leviParabolicTransitivity.{u, v} k G hG R₀ L NR₀ P M U Q V
    r₀ lR₀ nR₀ hr₀ hlR₀ hnR₀ hmulR₀ p l r hp hl hr hmul q lQ vQ hq hlQ hvQ hmulQ
    (pointImage_le_of_range_le p r₀ rfl hR₀P) hR₀j.symm (pointImage_eq_inf_of_range_eq_inf hR₀Q)
  have hι : ∀ ψ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul),
      ∃ ιψ : (leviInductionFunctor p l r hp hr hl hmul).obj
          (ρ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)) ⟶
        (leviInductionFunctor r₀ lR₀ nR₀ hr₀ hnR₀ hlR₀ hmulR₀).obj (σ.twist (θ ψ) (hθ ψ)),
        Function.Injective (SmoothRep.hom ιψ) := by
    intro ψ
    exact ⟨SmoothRep.ofHom ((SmoothRep.hom (eI.app (σ.twist (θ ψ) (hθ ψ))).inv).comp
        (leviInductionMap p l r hp hl hr hmul (fψ ψ))),
      ((SmoothRep.mono_iff_injective (eI.app (σ.twist (θ ψ) (hθ ψ))).inv).mp
          inferInstance).comp
        (leviInductionMap_injective p l r hp hl hr hmul _ (hfψ ψ))⟩
  choose ιI hιI using hι
  -- admissibility of the quotients
  have hZadm : ∀ (ψ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul))
      (S : Subrepresentation ((leviInductionFunctor p l r hp hr hl hmul).obj
        (ρ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).representation),
      (SmoothRep.quotient _ S).IsAdmissible := fun ψ S =>
    isAdmissible_of_surjective_coefficients (exists_compact_openSubgroup_le _)
      (SmoothRep.hom (SmoothRep.mkQ _ S)) (SmoothRep.mkQ_surjective _ S)
      (leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement
        arbitraryParabolicQuotientCompact hG p l r hp hl hr hmul _ (hρψadm ψ))
  -- the gallery from the opposite side to `R₀`
  have hbj : b ≫ lQ ≫ q ≫ l ≫ p = a ≫ l ≫ p := by
    rw [← hba]
    simp only [Category.assoc]
  have hcentr : torusCentralizer (a ≫ l ≫ p) = SubgroupFunctor.range (l ≫ p) :=
    ha.torusCentralizer_comp_eq_of_parabolicDynamic parabolicDynamic hG hp hl
  have hgalF := (hgal k G hG L A (lQ ≫ q ≫ l ≫ p) b hbs hbc _ _
    ⟨R₀, r₀, lR₀, hr₀, hlR₀, hR₀j, rfl⟩ ⟨R₁, r₁, lR₁, hr₁, hlR₁, hR₁j', rfl⟩ (by
      rw [hbj, hcentr, subgroupFunctor_inf_comm, ← hR₀Q, subgroupFunctor_inf_comm, ← hmbc]
      exact hR₁Q)).2.2
  let Ix := fun ψ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul) =>
    {S : Subrepresentation ((leviInductionFunctor p l r hp hr hl hmul).obj
      (ρ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).representation //
        S ≠ ⊤}
  let Zf : ∀ ψ, Ix ψ → SmoothRep.{0, u, max u v} ℂ (rationalPoints G) :=
    fun ψ S => SmoothRep.quotient _ S.1
  have hsub : ∀ ψ (S : Ix ψ), ∀ (R N : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G)
      (lR : L ⟶ R) (nR : N ⟶ R) (hr : IsParabolicSubgroup r) (hlR : IsRationalLeviSubgroup lR)
      (hnR : LeviSubgroup.IsGeometricUnipotentRadical nR)
      (hmulR : IsIso (subgroupMultiplication lR nR)), lR ≫ r = lQ ≫ q ≫ l ≫ p →
      letI := leviPointTopology lR hlR
      SmoothRep.IsSubquotient ((leviJacquetFunctor r lR nR hr hnR hlR hmulR).obj (Zf ψ S))
        ((leviJacquetFunctor.{u, max u v} r lR nR hr hnR hlR hmulR).obj
          ((leviInductionFunctor r₀ lR₀ nR₀ hr₀ hnR₀ hlR₀ hmulR₀).obj
            (σ.twist (θ ψ) (hθ ψ)))) :=
    fun ψ S R'' NR'' r'' lR'' nR'' hr'' hlR'' hnR'' hmulR'' _ =>
      isSubquotient_leviJacquet_quotient_of_injective (ιI ψ) (hιI ψ) S.1
        r'' lR'' nR'' hr'' hlR'' hnR'' hmulR''
  obtain ⟨g, hg0, hgD⟩ : ∃ g : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, g ≠ 0 ∧
      ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hM g,
        ∀ S : {S : Subrepresentation ((leviInductionFunctor p l r hp hr hl hmul).obj
            (ρ.twist ψ.val.toMonoidHom
              (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).representation // S ≠ ⊤},
          PersistenceInvariant (lQ ≫ q ≫ l ≫ p) bL (SmoothRep.quotient _ S.1) (χ0 ψ)
              (SubgroupFunctor.range r₁) →
            PersistenceInvariant (lQ ≫ q ≫ l ≫ p) bL (SmoothRep.quotient _ S.1) (χ0 ψ)
              (SubgroupFunctor.range r₀) := by
    refine exists_polynomial_persistenceInvariant_of_gallery (M := M) hG hadj hM hbL.1.2
      (Ix := Ix) Zf (fun ψ _ => χ0 ψ) (fun ψ S => hZadm ψ S.1) ?_ ?_ hgalF
    · -- finite length along every parabolic with Levi `L`
      intro ψ S R'' NR'' r'' lR'' nR'' hr'' hlR'' hnR'' hmulR'' h''
      exact SmoothRep.hasFiniteLength_of_isSubquotient
        (pieces_of_supercuspidal_normalizer r₀ lR₀ nR₀ hr₀ hlR₀ hnR₀ hmulR₀
          r'' lR'' nR'' hr'' hlR'' hnR'' hmulR'' hG (h''.trans hR₀j.symm) gW φW hφW hgW
          (σ.twist (θ ψ) (hθ ψ)) (hσθirr ψ) (hσθsc ψ)).1
        (hsub ψ S R'' NR'' r'' lR'' nR'' hr'' hlR'' hnR'' hmulR'' h'')
    · -- one polynomial per wall
      intro F₁ F₁' d hd V₁ v₁ hv₁ hmulQ₁
      exact exists_polynomial_wall_isIrreducible hVI hWS hG p l hp hl q lQ hq hlQ ha hba hbL
        r₀ lR₀ nR₀ hr₀ hlR₀ hnR₀ hmulR₀ hR₀j gW φW hφW hgW σ hσ θ hθ (fun _ _ => rfl)
        (fun ψ => hσθsc ψ) χ0 hχ0 (Ix := Ix) Zf hsub d hd v₁ hv₁ hmulQ₁
  -- conclusion
  refine ⟨g, hg0, fun ψ hψ S hS => ?_⟩
  have hstart := persistenceInvariant_opposite hG hadj p l r hp hl hr hmul pb mb nb hpb hmb hnb
    hmulb hmbc hopp q lQ vQ hq hlQ hvQ hmulQ r₁ lR₁ nR₁ hr₁ hlR₁ hnR₁ hmulR₁ hR₁j' hR₁P hR₁Q
    hbL.1.2 _ (hρψirr ψ) (hρψadm ψ) (σ.twist (θ ψ) (hθ ψ)) (hσθirr ψ) (fψ ψ) (hfψ0 ψ) (χ0 ψ)
    (hχ0 ψ) S hS
  have hend := isGeneralizedEigencharacter_of_persistenceInvariant hG p l r hp hl hr hmul
    q lQ vQ hq hlQ hvQ hmulQ hR₀P hR₀Q ha hbL e he₂ _ (hZadm ψ S) (χ0 ψ)
    (hgD ψ hψ ⟨S, hS⟩ hstart)
  refine ⟨(χ0 ψ).comp (rationalPoints.map e), ?_, hend⟩
  exact isGeneralizedEigencharacter_of_leviJacquet_restrict q lQ vQ hq hlQ hvQ hmulQ ha hbL
    (rationalPoints.map e)
    (fun t => by rw [← pointMap_comp_apply, ← pointMap_comp_apply, he₂]) _ (hρψadm ψ) (χ0 ψ)
    (isGeneralizedEigencharacter_jacquet_of_ne_zero_induction q lQ vQ hq hlQ hvQ hmulQ hM
      hbL.1.2 _ (hρψadm ψ) (σ.twist (θ ψ) (hθ ψ)) (hσθirr ψ) (fψ ψ) (hfψ0 ψ) (χ0 ψ) (hχ0 ψ))

end Langlands.Renard.AlgebraicFamily
