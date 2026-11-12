import Langlands.Representation.Aubert.General.RationalSameLeviGenericIrreducibilityFromInputsStatement
import Langlands.Representation.Aubert.General.RationalRankOneMaximalLeviBridge
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization
import Langlands.Representation.Exponents.ArbitraryParabolicConjugation
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.Rational.SplitUnipotentRationalDetection
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Reductive.RationalPointDensityProof
import Langlands.Representation.Aubert.General.ConjugateInduction
import Langlands.Representation.Aubert.General.RationalLeviCharacterDensity
import Langlands.Representation.Aubert.General.RepresentedStandardCuspidality
import Langlands.Representation.Aubert.General.RationalRootAssociationCuspidalityTransport
import Langlands.Representation.CuspidalSupport.GroupTransport

/-! # Generic irreducibility for two same-Levi inductions from Renard VI.8.4 and Konno 4.2 -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

open GroupScheme RepresentedParabolic
open Langlands.AlgebraicGeometry.PointTopology

section Density

variable {k : Type u} [Field k] [Infinite k]
  {A B G : GroupScheme (Spec (CommRingCat.of k))}

/-- Over an infinite field, a homomorphism out of a connected reductive group whose
rational points land in the rational points of a closed subgroup lands in it on every
test scheme. -/
theorem range_le_of_pointImage_le [IsAffine G.X.left] (hA : IsConnectedReductive A)
    (a : A ⟶ G) {b : B ⟶ G} (hb : IsClosedSubgroup b) (h : pointImage a ≤ pointImage b) :
    SubgroupFunctor.range a ≤ SubgroupFunctor.range b := by
  have := hA.smooth
  have : IsClosedImmersion b.hom.hom.left := hb
  have hdet : RationalPointsDetectFunctions A.X :=
    RationalDensity.rationalPointsDetectFunctions_of_smooth
      (reductiveRationalPointDensity k A hA)
  obtain ⟨l, hl⟩ := RationalDensity.RationalPointsDetectFunctions.exists_factor hdet
    b.hom.hom a.hom.hom fun x => by
      obtain ⟨y, hy⟩ := h (show rationalPoints.map a x ∈ pointImage a from ⟨x, rfl⟩)
      exact ⟨y, hy⟩
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ l, by rw [Category.assoc, hl]⟩

/-- Over an infinite field, two connected reductive closed subgroups whose rational
points are conjugate by `g` have isomorphic sources, compatibly with conjugation by `g`. -/
theorem exists_iso_comp_innerIso_of_pointImage [IsAffine G.X.left]
    (hA : IsConnectedReductive A) (hB : IsConnectedReductive B)
    {a : A ⟶ G} {b : B ⟶ G} (ha : IsClosedSubgroup a) (hb : IsClosedSubgroup b)
    (g : rationalPoints G)
    (hab : ∀ x : rationalPoints G, x ∈ pointImage a ↔ g⁻¹ * x * g ∈ pointImage b) :
    ∃ e : A ≅ B, e.hom ≫ b ≫ (G.innerIso g).hom = a := by
  have hb' : IsClosedSubgroup (b ≫ (G.innerIso g).hom) := hb.comp_iso _
  have hpt : pointImage a = pointImage (b ≫ (G.innerIso g).hom) := by
    ext x
    rw [mem_pointImage_comp_innerIso]
    exact hab x
  have hrange : SubgroupFunctor.range a = SubgroupFunctor.range (b ≫ (G.innerIso g).hom) :=
    le_antisymm (range_le_of_pointImage_le hA a hb' hpt.le)
      (range_le_of_pointImage_le hB _ ha hpt.ge)
  exact ⟨ha.sourceIsoOfRangeEq hb' hrange, ha.sourceIsoOfRangeEq_hom_comp hb' hrange⟩

end Density

section Comparison

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance sameLeviAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- The actual normalized induction from a represented parabolic is irreducible exactly
when the normalized induction from any decomposition with the same point images is, for
representations identified by an equivariant linear equivalence. -/
theorem leviInduction_isIrreducible_iff_of_pointImage
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r))
    {P' N U' : Subgroup (rationalPoints G)} (h : IsSemidirectDecomposition P' N U')
    (hU' : IsClosed (U' : Set (rationalPoints G)))
    (hP : pointImage p = P') (hN : pointImage (l ≫ p) = N) (hU : pointImage (r ≫ p) = U')
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (B : SmoothRep.{0, u, v} ℂ N) (f : A ≃ₗ[ℂ] B) (φ : rationalPoints M → N)
    (hφ : ∀ m, (φ m : rationalPoints G) = rationalPoints.map (l ≫ p) m)
    (hf : letI := leviPointTopology l hl
      ∀ (m : rationalPoints M) (x : A), f (A.representation m x) = B.representation (φ m) (f x)) :
    letI := leviPointTopology l hl
    ((leviInductionFunctor p l r hp hr hl hmul).obj A).IsIrreducible ↔
      ((normalizedInductionFunctor h hU').obj B).IsIrreducible := by
  let := leviPointTopology l hl
  rw [leviInductionFunctor_obj]
  refine RepresentedParabolic.normalizedInduction_isIrreducible_congr hP hN hU _ _ h hU' _ B f ?_
  intro m x
  refine (hf ((leviPointsEquiv p l hp hl).symm m) x).trans ?_
  congr 2
  apply Subtype.ext
  rw [hφ, ← leviPointsEquiv_apply_coe p l hp hl, ContinuousMulEquiv.apply_symm_apply]

end Comparison

section Generic

open Plancherel

/-- Renard VI.8.4 together with the existence of one irreducible induced twist gives a
nonzero principal open locus of irreducible induced twists, for an irreducible admissible
representation of the rational points of an actual rational Levi. -/
theorem exists_generic_leviInduction_isIrreducible
    (hOpen : Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement.{u, v})
    (hExist : Renard.AlgebraicFamily.IrreducibleInducedTwistExistenceStatement.{u, v})
    {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      {P M U : GroupScheme (Spec (CommRingCat.of k))}
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible → ρ.IsAdmissible →
        ∃ f : MvPolynomial (Fin (rationalImageRank M)) ℂ, f ≠ 0 ∧
          ∀ ψ ∈ rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
            ((leviInductionFunctor p l r hp hr hl hmul).obj
              (ρ.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ))).IsIrreducible := by
  intro _ _ P M U p l r hp hl hr hmul ρ hρ hadm
  obtain ⟨ψ₀, hψ₀⟩ := hExist k G hG P M U p l r hp hl hr hmul ρ hρ hadm
  obtain ⟨f, hf₀, hf⟩ := hOpen k G hG P M U p l r hp hl hr hmul ρ hρ ψ₀ hψ₀
  refine ⟨f, ?_, hf⟩
  rintro rfl
  have := (mem_rationalUnramifiedPrincipalOpen M hl.isConnectedReductive 0 ψ₀).mp hf₀
  simp at this

end Generic

namespace RationalPointFamily

open Plancherel

set_option maxHeartbeats 800000 in
/-- The same-Levi generic irreducibility target follows from Renard VI.8.4 and the
existence of one irreducible induced unramified twist (Konno Theorem 4.2). -/
theorem rationalSameLeviGenericInductionIrreducibility_of_inputs
    (hOpen : Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement.{u, v})
    (hExist : Renard.AlgebraicFamily.IrreducibleInducedTwistExistenceStatement.{u, v}) :
    RationalSameLeviGenericInductionIrreducibilityStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi _ _ _ ν hν hStandard hU I J g hIJ hLJ σ hirr hadm
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := pointTopology
  let : T2Space k := BruhatTits.localField_t2Space k
  obtain ⟨ϖ, hϖ⟩ := Valuation.IsNontrivial.exists_one_lt (v := ValuativeRel.valuation k)
  have : Infinite k := by
    refine Infinite.of_injective (fun n : ℕ => ϖ ^ n) ?_
    intro m n hmn
    apply (pow_right_strictMono₀ hϖ).injective
    simpa only [map_pow] using congrArg (ValuativeRel.valuation k) hmn
  obtain ⟨hpJ, hlJ, hrJ, hmulJ⟩ :=
    standard_representatives_geometric_of_standardCocharacter i ν hStandard hG hi hν J
  obtain ⟨hpI, hlI, hrI, hmulI⟩ :=
    standard_representatives_geometric_of_standardCocharacter i ν hStandard hG hi hν I
  let : TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν J))) :=
    leviPointTopology _ hlJ
  have hpt (K : Finset (SimpleRoot i ν)) :
      pointImage (Standard.leviHom i ν (rootSet i ν K)) = levi i ν K :=
    congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _)))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν K)).2
  have hPpt (K : Finset (SimpleRoot i ν)) :
      pointImage (Standard.parabolicHom i ν (rootSet i ν K)) = parabolic i ν K :=
    congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _)))
      (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν K)).2
  -- The actual Levi scheme of `J` is the conjugate of the one of `I`.
  obtain ⟨e, he⟩ := exists_iso_comp_innerIso_of_pointImage hLJ hlI.isConnectedReductive
    (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J))
    (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)) g
    (fun x => by rw [hpt J, hpt I]; exact hIJ x)
  -- The conjugate parabolic `g P_I g⁻¹`, with Levi source the Levi scheme of `J`.
  let p' := Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom
  let l' := e.hom ≫ Standard.leviToParabolic i ν (rootSet i ν I)
  let r' := Standard.unipotentToParabolic i ν (rootSet i ν I)
  have hp' : IsParabolicSubgroup p' := hpI.comp_iso _
  have hl' : IsRationalLeviSubgroup l' := hlI.iso_comp e
  have hmul' : IsIso (subgroupMultiplication l' r') := isIso_subgroupMultiplication_iso_comp e hmulI
  have hlp' : l' ≫ p' = Standard.leviHom i ν (rootSet i ν J) := by
    simp only [l', p', Category.assoc]
    rw [← Category.assoc (Standard.leviToParabolic i ν (rootSet i ν I)),
      Standard.leviToParabolic_comp, he]
  -- The representation of the Levi scheme's own points.
  let ρ := SmoothRep.pullback (leviRationalPointHomeomorph i ν J) σ
  have hρ : ρ.IsIrreducible :=
    (SmoothRep.isIrreducible_pullbackFunctor_obj_iff _ σ).mpr hirr
  have hρadm : ρ.IsAdmissible :=
    Langlands.isAdmissible_comp_continuousMulEquiv σ.representation _ hadm
  obtain ⟨f₁, hf₁, h₁⟩ := exists_generic_leviInduction_isIrreducible hOpen hExist hG
    (Standard.parabolicHom i ν (rootSet i ν J)) (Standard.leviToParabolic i ν (rootSet i ν J))
    (Standard.unipotentToParabolic i ν (rootSet i ν J)) hpJ hlJ hrJ hmulJ ρ hρ hρadm
  obtain ⟨f₂, hf₂, h₂⟩ := exists_generic_leviInduction_isIrreducible hOpen hExist hG
    p' l' r' hp' hl' hrI hmul' ρ hρ hρadm
  refine ⟨f₁ * f₂, mul_ne_zero hf₁ hf₂, fun χ hχ => ?_⟩
  let ψ := (leviRationalUnramifiedCharacterHomeomorph i ν J).symm χ
  have hψ : ψ ∈ rationalUnramifiedPrincipalOpen (Standard.leviScheme i ν (rootSet i ν J)) hLJ
      (f₁ * f₂) := hχ
  rw [mem_rationalUnramifiedPrincipalOpen, map_mul, mul_ne_zero_iff] at hψ
  have hψ₁ := (mem_rationalUnramifiedPrincipalOpen _ hlJ.isConnectedReductive f₁ ψ).mpr hψ.1
  have hψ₂ := (mem_rationalUnramifiedPrincipalOpen _ hl'.isConnectedReductive f₂ ψ).mpr hψ.2
  constructor
  · refine (leviInduction_isIrreducible_iff_of_pointImage
      (Standard.parabolicHom i ν (rootSet i ν J)) (Standard.leviToParabolic i ν (rootSet i ν J))
      (Standard.unipotentToParabolic i ν (rootSet i ν J)) hpJ hrJ hlJ hmulJ
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
      (hU J) (hPpt J) (by rw [Standard.leviToParabolic_comp]; exact hpt J)
      (standard_unipotent_pointImage i ν J) _ _ (LinearEquiv.refl ℂ _)
      (leviRationalPointHomeomorph i ν J) (fun m => by rw [Standard.leviToParabolic_comp]; rfl)
      (fun m x => rfl)).mp (h₁ ψ hψ₁)
  · refine (leviInduction_isIrreducible_iff_of_pointImage p' l' r' hp' hrI hl' hmul'
      ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I
        ).conjugateWithLevi g hIJ)
      (isClosed_conjugateSubgroup g (hU I)) ?_ (by rw [hlp']; exact hpt J) ?_ _ _
      (LinearEquiv.refl ℂ _) (leviRationalPointHomeomorph i ν J)
      (fun m => by rw [hlp']; rfl) (fun m x => rfl)).mp (h₂ ψ hψ₂)
    · ext x
      rw [mem_pointImage_comp_innerIso, hPpt I, mem_conjugateSubgroup]
    · ext x
      rw [show r' ≫ p' = (Standard.unipotentToParabolic i ν (rootSet i ν I) ≫
          Standard.parabolicHom i ν (rootSet i ν I)) ≫ (G.innerIso g).hom from
          (Category.assoc _ _ _).symm,
        mem_pointImage_comp_innerIso, standard_unipotent_pointImage, mem_conjugateSubgroup]

/-- The published conditional same-Levi statement. -/
theorem rationalSameLeviGenericInductionIrreducibilityFromInputs :
    RationalSameLeviGenericInductionIrreducibilityFromInputsStatement.{u, v} :=
  rationalSameLeviGenericInductionIrreducibility_of_inputs

end RationalPointFamily

end Langlands.Aubert.General
