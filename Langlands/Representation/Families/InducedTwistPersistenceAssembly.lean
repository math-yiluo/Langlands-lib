import Langlands.Representation.Families.InducedTwistPersistenceGallery
import Langlands.Representation.Families.InducedTwistPersistenceGenericity
import Langlands.Representation.Exponents.LeviInductionEmbeddings
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Smooth.ConstituentSupport
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Smooth.Admissibility.CoefficientQuotient
import Langlands.Representation.Exponents.UnramifiedTwistRadicals
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Representation.Exponents.LeviNormalizerBridge

/-! # The two ends of the gallery, and helpers for the assembly

* `exists_splitComponent_factor`: a split component `A_M` of `M` lies centrally in every Levi
  `L` of a parabolic of `M`, and factors through a split component `A_L` of `L`.
* `persistenceInvariant_opposite`: second adjointness puts the exponent of the inducing data
  into the Jacquet module of a quotient along a parabolic inside the opposite of `P`.
* `isGeneralizedEigencharacter_of_persistenceInvariant`: an exponent along a parabolic inside
  `P` restricts to an `A_M`-exponent of `r_P`.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.InducedTwistPersistence

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

section Helpers

/-- An equality of ranges with an intersection gives the same equality of rational point
images. -/
theorem pointImage_eq_inf_of_range_eq_inf {k : Type u} [Field k]
    {G X Y Z : GroupScheme (Spec (CommRingCat.of k))} {x : X ⟶ G} {y : Y ⟶ G} {z : Z ⟶ G}
    (h : SubgroupFunctor.range x = SubgroupFunctor.range y ⊓ SubgroupFunctor.range z) :
    pointImage x = pointImage y ⊓ pointImage z := by
  rw [pointImage_eq_range_carrier, pointImage_eq_range_carrier, pointImage_eq_range_carrier, h]
  rfl

/-- In a locally compact nonarchimedean group, compact open subgroups are cofinal among the
open subgroups. -/
theorem exists_compact_openSubgroup_le (H : Type*) [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [NonarchimedeanGroup H] (K : OpenSubgroup H) :
    ∃ V : OpenSubgroup H, IsCompact (V : Set H) ∧ V ≤ K := by
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (1 : H)
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _
    (Filter.inter_mem hC K.mem_nhds_one)
  exact ⟨V, hCc.of_isClosed_subset V.isClosed (hV.trans Set.inter_subset_left),
    fun x hx => (hV hx).2⟩

/-- Twisting by equal characters gives equal representations. -/
theorem twist_eq_of_eq {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    (A : SmoothRep.{0, u, v} ℂ Γ) {χ₁ χ₂ : Γ →* ℂˣ} (h : χ₁ = χ₂)
    (h₁ : IsOpen (χ₁.ker : Set Γ)) (h₂ : IsOpen (χ₂.ker : Set Γ)) :
    A.twist χ₁ h₁ = A.twist χ₂ h₂ := by
  subst h
  rfl

/-- An injective intertwiner out of a nonzero representation is nonzero. -/
theorem intertwiningMap_ne_zero_of_injective {Γ : Type*} [Group Γ] {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Nontrivial V]
    {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) : f ≠ 0 := by
  intro h0
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact hx (hf (by rw [h0]; rfl))

/-- An irreducible admissible representation has an exponent for every central subgroup. -/
theorem exists_isGeneralizedEigencharacter_of_isAdmissible {Γ : Type u} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] {T : Type*} [Group T] (ιT : T →* Γ)
    (hιT : ∀ t, ιT t ∈ Subgroup.center Γ) (Y : SmoothRep.{0, u, v} ℂ Γ) (hY : Y.IsIrreducible)
    (hadm : Y.IsAdmissible) :
    ∃ χ : T →* ℂˣ, IsGeneralizedEigencharacter (Y.representation.comp ιT) χ := by
  obtain ⟨χc, -, hχc⟩ := (admissibleSchur_centralCharacter Y.representation hadm hY).exists
  have := nontrivial_of_isIrreducible (ρ := Y.representation) hY
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  exact ⟨χc.comp (ιT.codRestrict _ hιT),
    isGeneralizedEigencharacter_of_eigenvector _ _ hy fun t => hχc ⟨ιT t, hιT t⟩ y⟩

end Helpers

section Torus

variable {k : Type u} [Field k] {M : GroupScheme (Spec (CommRingCat.of k))}

/-- A split component `A_M` of `M` factors centrally through every Levi `L` of a parabolic
of `M`, and then through a split component `A_L` of `L`. -/
theorem exists_splitComponent_factor (hM : IsConnectedReductive M)
    {Q L : GroupScheme (Spec (CommRingCat.of k))} (q : Q ⟶ M) (lQ : L ⟶ Q)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) :
    ∃ (B : CommGroupScheme (Spec (CommRingCat.of k))) (bL : B.toGrp ⟶ L)
      (b : A.toGrp ⟶ L) (e : A.toGrp ⟶ B.toGrp),
      IsSplitComponent bL ∧ b ≫ lQ ≫ q = a ∧ IsSplitSubtorus b ∧ IsCentral b ∧
        e ≫ bL = b := by
  have hL := hlQ.isConnectedReductive
  have := hL.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have := hL.smooth
  have := hM.isAffineHom
  obtain ⟨B, bL, hbL⟩ := exists_isSplitComponent L
  have hcent : torusCentralizer (bL ≫ lQ ≫ q) = SubgroupFunctor.range (lQ ≫ q) :=
    hbL.torusCentralizer_comp_eq_of_parabolicDynamic parabolicDynamic hM hq hlQ
  have hle : SubgroupFunctor.range a ≤ SubgroupFunctor.range (lQ ≫ q) := by
    rw [← hcent]
    refine le_trans ?_ (center_le_torusCentralizer _)
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact ha.1.2 T y
  have hc : IsClosedSubgroup (lQ ≫ q) := hlQ.isClosedSubgroup.comp hq.isClosedSubgroup
  obtain ⟨b, hb, hba⟩ := ha.1.1.factorInClosedSubgroup hc hle
  have : Mono (lQ ≫ q).hom.hom.left := hc.mono
  have hbc : IsCentral b :=
    IsCentral.of_comp (Over.mono_of_mono_left _) (by rw [hba]; exact ha.1.2)
  obtain ⟨e, he⟩ := hbL.exists_factor ha.1.1.1 hbc
  exact ⟨B, bL, b, e, hbL, hba, hb, hbc, he⟩

end Torus

section Ends

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance persistenceAssemblyAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

set_option maxHeartbeats 1000000 in
/-- **Start.** Let `P̄` be opposite to `P = MN` with the same Levi `M`, let `Q = LV` be a
parabolic of `M`, and let `R` be a parabolic of `G` with Levi `L`, contained in `P̄`, with
`R ∩ M = Q`. Given second adjointness, an irreducible admissible `τ` of `M(k)` and a nonzero
map `τ → i^M_Q(Y)` with `Y` irreducible, every exponent of `Y` on a central `b_L` is an
exponent of `r_R(i_P(τ)/S)` for every proper invariant subspace `S`. -/
theorem persistenceInvariant_opposite (hG : IsConnectedReductive G)
    (hadj : LeviSecondAdjointnessStatement.{u, v})
    {P Pbar M N Nbar Q L V R NR : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (n : N ⟶ P) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l) (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication l n))
    (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar) (hpbar : IsParabolicSubgroup pbar)
    (hmbar : IsRationalLeviSubgroup mbar) (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hmulbar : IsIso (subgroupMultiplication mbar nbar))
    (hmc : mbar ≫ pbar = l ≫ p) (hopp : pointImage p ⊓ pointImage pbar = pointImage (l ≫ p))
    (q : Q ⟶ M) (lQ : L ⟶ Q) (vQ : V ⟶ Q) (hq : IsParabolicSubgroup q)
    (hlQ : IsRationalLeviSubgroup lQ) (hvQ : LeviSubgroup.IsGeometricUnipotentRadical vQ)
    (hmulQ : IsIso (subgroupMultiplication lQ vQ))
    (r : R ⟶ G) (lR : L ⟶ R) (nR : NR ⟶ R) (hr : IsParabolicSubgroup r)
    (hlR : IsRationalLeviSubgroup lR) (hnR : LeviSubgroup.IsGeometricUnipotentRadical nR)
    (hmulR : IsIso (subgroupMultiplication lR nR))
    (hRL : lR ≫ r = lQ ≫ q ≫ l ≫ p)
    (hRP : SubgroupFunctor.range r ≤ SubgroupFunctor.range pbar)
    (hRQ : SubgroupFunctor.range (q ≫ mbar ≫ pbar) =
      SubgroupFunctor.range (mbar ≫ pbar) ⊓ SubgroupFunctor.range r)
    {B : CommGroupScheme (Spec (CommRingCat.of k))} {bL : B.toGrp ⟶ L} (hbL : IsCentral bL)
    (τ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hτ : letI := leviPointTopology l hl; τ.IsIrreducible)
    (hτadm : letI := leviPointTopology l hl; τ.IsAdmissible)
    (Y : letI := leviPointTopology lQ hlQ; SmoothRep.{0, u, v} ℂ (rationalPoints L))
    (hY : letI := leviPointTopology lQ hlQ; Y.IsIrreducible)
    (f : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      letI := leviPointTopology lQ hlQ
      τ.representation.IntertwiningMap
        ((leviInductionFunctor q lQ vQ hq hvQ hlQ hmulQ).obj Y).representation)
    (hf : f ≠ 0) (χ : rationalPoints B.toGrp →* ℂˣ)
    (hχ : letI := leviPointTopology lQ hlQ
      IsGeneralizedEigencharacter (Y.representation.comp (rationalPoints.map bL)) χ)
    (S : letI := leviPointTopology l hl
      Subrepresentation ((leviInductionFunctor p l n hp hn hl hmul).obj τ).representation)
    (hS : S ≠ ⊤) :
    PersistenceInvariant (lQ ≫ q ≫ l ≫ p) bL (SmoothRep.quotient _ S) χ
      (SubgroupFunctor.range r) := by
  have hM := hl.isConnectedReductive
  have := hM.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  obtain ⟨adj⟩ := hadj k G hG P Pbar M N Nbar p l n hp hl hn hmul pbar mbar nbar hpbar hmbar
    hnbar hmulbar hmc hopp
  obtain ⟨jj, hjj⟩ := exists_injective_oppositeJacquet_of_quotient p l n hp hl hn hmul
    pbar mbar nbar hpbar hmbar hnbar hmulbar adj τ hτ S hS
  let Yb := (leviJacquetFunctor pbar mbar nbar hpbar hnbar hmbar hmulbar).obj
    (SmoothRep.quotient _ S)
  let ℓ : SmoothRep.universeLift.{u} τ ⟶ Yb :=
    SmoothRep.ofHom (jj.comp (SmoothRep.universeLiftEquiv.{u} τ).symm.toIntertwiningMap)
  have hℓ : Function.Injective (SmoothRep.hom ℓ) :=
    hjj.comp (SmoothRep.universeLiftEquiv.{u} τ).symm.injective
  have hτadm' : (SmoothRep.universeLift.{u} τ).IsAdmissible :=
    (SmoothRep.isAdmissible_universeLift_iff τ).mpr hτadm
  have hf' : f.comp (SmoothRep.universeLiftEquiv.{u} τ).symm.toIntertwiningMap ≠ 0 := by
    intro h0
    apply hf
    ext x
    have h := congrArg (fun g => g (SmoothRep.universeLiftEquiv.{u} τ x)) h0
    exact h
  have h1 := isGeneralizedEigencharacter_jacquet_of_ne_zero_induction q lQ vQ hq hlQ hvQ hmulQ
    hM hbL (SmoothRep.universeLift.{u} τ) hτadm' Y hY _ hf' χ hχ
  have h2 := isGeneralizedEigencharacter_of_injective (rationalPoints.map bL)
    (SmoothRep.hom ((leviJacquetFunctor q lQ vQ hq hvQ hlQ hmulQ).map ℓ))
    (leviJacquetFunctor_map_injective q lQ vQ hq hlQ hvQ hmulQ ℓ hℓ) χ h1
  obtain ⟨-, ⟨eJ⟩⟩ := leviParabolicTransitivity.{u, max u v} k G hG R L NR Pbar M Nbar Q V
    r lR nR hr hlR hnR hmulR pbar mbar nbar hpbar hmbar hnbar hmulbar q lQ vQ hq hlQ hvQ hmulQ
    (pointImage_le_of_range_le pbar r rfl hRP) (by rw [hmc, hRL])
    (pointImage_eq_inf_of_range_eq_inf hRQ)
  refine ⟨R, NR, r, lR, nR, hr, hlR, hnR, hmulR, hRL, rfl, ?_⟩
  exact isGeneralizedEigencharacter_of_injective (rationalPoints.map bL)
    (SmoothRep.hom (eJ.app (SmoothRep.quotient _ S)).inv)
    ((SmoothRep.mono_iff_injective _).mp inferInstance) χ h2

set_option maxHeartbeats 1000000 in
/-- **End.** If the invariant holds for a parabolic image `F` inside `P` with `F ∩ M = Q`,
then the restriction of its exponent along `A_M → A_L` is an `A_M`-exponent of `r_P(Z)`. -/
theorem isGeneralizedEigencharacter_of_persistenceInvariant (hG : IsConnectedReductive G)
    {P M N Q L V : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (n : N ⟶ P) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l) (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication l n))
    (q : Q ⟶ M) (lQ : L ⟶ Q) (vQ : V ⟶ Q) (hq : IsParabolicSubgroup q)
    (hlQ : IsRationalLeviSubgroup lQ) (hvQ : LeviSubgroup.IsGeometricUnipotentRadical vQ)
    (hmulQ : IsIso (subgroupMultiplication lQ vQ))
    {F : SubgroupFunctor G} (hFP : F ≤ SubgroupFunctor.range p)
    (hFQ : SubgroupFunctor.range (q ≫ l ≫ p) = SubgroupFunctor.range (l ≫ p) ⊓ F)
    {A B : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M} {bL : B.toGrp ⟶ L}
    (ha : IsSplitComponent a) (hbL : IsSplitComponent bL) (e : A.toGrp ⟶ B.toGrp)
    (he : e ≫ bL ≫ lQ ≫ q = a)
    (Z : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) (hZ : Z.IsAdmissible)
    (χ : rationalPoints B.toGrp →* ℂˣ)
    (h : PersistenceInvariant (lQ ≫ q ≫ l ≫ p) bL Z χ F) :
    letI := leviPointTopology l hl
    IsGeneralizedEigencharacter
      (((leviJacquetFunctor p l n hp hn hl hmul).obj Z).representation.comp
        (rationalPoints.map a)) (χ.comp (rationalPoints.map e)) := by
  have hM := hl.isConnectedReductive
  have := hM.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  obtain ⟨R, NR, r, lR, nR, hr, hlR, hnR, hmulR, hRj, hRF, hexp⟩ := h
  have hRQ : SubgroupFunctor.range (q ≫ l ≫ p) =
      SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range r := by
    rw [hRF]
    exact hFQ
  obtain ⟨-, ⟨eJ⟩⟩ := leviParabolicTransitivity.{u, max u v} k G hG R L NR P M N Q V
    r lR nR hr hlR hnR hmulR p l n hp hl hn hmul q lQ vQ hq hlQ hvQ hmulQ
    (pointImage_le_of_range_le p r hRF hFP) hRj.symm (pointImage_eq_inf_of_range_eq_inf hRQ)
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
  have h1 := isGeneralizedEigencharacter_of_injective (rationalPoints.map bL)
    (SmoothRep.hom (eJ.app Z).hom) ((SmoothRep.mono_iff_injective _).mp inferInstance) χ hexp
  have hPadm : ((leviJacquetFunctor p l n hp hn hl hmul).obj Z).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv _ (leviPointsEquiv p l hp hl)
      (arbitraryParabolicJacquetAdmissibility k G hG P M N p l n hp hl hn hmul Z hZ)
  exact isGeneralizedEigencharacter_of_leviJacquet_restrict q lQ vQ hq hlQ hvQ hmulQ ha hbL
    (rationalPoints.map e)
    (fun t => by rw [← pointMap_comp_apply, ← pointMap_comp_apply, he]) _ hPadm χ h1

end Ends

end Langlands.InducedTwistPersistence
