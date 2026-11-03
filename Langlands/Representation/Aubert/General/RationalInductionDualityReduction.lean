import Langlands.Representation.Smooth.Contragredient.Equivalence
import Langlands.Representation.Aubert.General.RationalInductionDualityStatement
import Langlands.Representation.Induction.CompactPairingDuality
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.BruhatTits.Parabolic.QuotientCompactStatement

/-!
# Reduction of rational natural induction duality to a uniform integral duality

For an actual semidirect decomposition `P = M ⋉ U` with continuous Levi
projection, this file proves the parts of same-parabolic induction duality that
do not depend on a compact-picture integral: admissibility of the inducing and
induced representations, compact-open cofinality of the Levi, and the
packaging of a uniform family of integral-characterized dualities into a natural
family of isomorphisms of bundled smooth representations. It also identifies the
actual standard rational-point parabolic with a dynamic parabolic, so that the
dynamic quotient-compactness statement applies to it.
-/

noncomputable section

open CategoryTheory MeasureTheory
open scoped NNReal

namespace Langlands.Aubert.General

universe uG uV

section Contragredient

variable {R H V W : Type*} [CommRing R] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {ρ : Representation R H V} {σ : Representation R H W}

/-- The shared equivalence on smooth contragredients. -/
abbrev smoothContragredientEquiv (e : ρ.Equiv σ) :
    (smoothContragredient σ).Equiv (smoothContragredient ρ) :=
  Langlands.smoothContragredientEquiv e

end Contragredient

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)

/-- A closed Levi has compact open subgroups cofinal among its open subgroups. -/
theorem compactOpenCofinal_of_isClosed {M : Subgroup G} (hM : IsClosed (M : Set G)) :
    CompactOpenCofinal M := by
  have := hM.locallyCompactSpace
  intro H
  obtain ⟨L, hL, hLH⟩ := compactOpenSubgroupBasis M (H : Set M) H.mem_nhds_one
  exact ⟨L, hL, fun x hx => hLH hx⟩

variable (hU : IsClosed (U : Set G))

/-- The square of the induction character is the restricted Haar modulus of
conjugation on `U`. -/
theorem closedHalfCharacter_mul_self (q : P) :
    ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂˣ) : ℂ) *
        HaarModulus.closedHalfCharacter U hU P h.le_normalizer q =
      (((HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0) : ℝ) : ℂ) := by
  let := hU.locallyCompactSpace
  have hsq := congrArg Units.val (HaarModulus.halfCharacter_sq U P h.le_normalizer q)
  rw [Units.val_pow_eq_pow_val, Jacquet.complexCharacter_apply, sq] at hsq
  exact hsq

/-- The inducing representation `p ↦ δ_P(p)^{1/2} σ(m(p))` of an admissible
Levi representation is admissible: a vector fixed by an open subgroup `H` of `P`
is fixed by the open subgroup of `M` cut out by `H` and the kernel of the
induction character. -/
theorem inducingRepresentation_isAdmissible (hm : Continuous h.projection)
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) :
    IsAdmissible (inducingRepresentation h hU A) := by
  let χ := HaarModulus.closedHalfCharacter U hU P h.le_normalizer
  have hχ : IsOpen (χ.ker : Set P) :=
    HaarModulus.isOpen_ker_closedHalfCharacter U hU P h.le_normalizer
  refine ⟨fun v => ?_, fun H => ?_⟩
  · obtain ⟨H, hH⟩ := A.isSmooth v
    exact Induction.exists_twist_comp_fixed P h.projection hm χ hχ A.representation v H hH
  · let H' : OpenSubgroup P := H ⊓ ⟨χ.ker, hχ⟩
    let N : OpenSubgroup M := H'.comap (Subgroup.inclusion h.levi_le)
      (continuous_inclusion h.levi_le)
    have hle : fixedVectors (inducingRepresentation h hU A) H.toSubgroup ≤
        fixedVectors A.representation N.toSubgroup := by
      intro v hv n
      have hn : (Subgroup.inclusion h.levi_le (n : M) : P) ∈ H' := n.2
      obtain ⟨hnH, hnχ⟩ := OpenSubgroup.mem_inf.mp hn
      have hχn : χ (Subgroup.inclusion h.levi_le (n : M)) = 1 := hnχ
      have hfix := hv ⟨_, hnH⟩
      change (χ (Subgroup.inclusion h.levi_le (n : M)) : ℂ) •
          A.representation (h.projection (Subgroup.inclusion h.levi_le (n : M))) v = v at hfix
      rw [hχn, Units.val_one, one_smul] at hfix
      have hproj : h.projection (Subgroup.inclusion h.levi_le (n : M)) = n :=
        h.projection_levi n
      rw [hproj] at hfix
      exact hfix
    have := hA.2 N
    exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

/-- With `P \ G` compact, smooth induction of the inducing representation of an
admissible representation is admissible. -/
theorem smoothInduced_inducingRepresentation_isAdmissible
    [CompactSpace (Induction.LeftQuotient P)] (hm : Continuous h.projection)
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) :
    IsAdmissible (Induction.smoothInduced P (inducingRepresentation h hU A)) :=
  Induction.smoothInduced_isAdmissible_of_compactSpace P _
    (inducingRepresentation_isAdmissible h hU hm A hA)

/-- With `P \ G` compact, normalized induction of an admissible representation
is admissible. -/
theorem normalizedInductionFunctor_obj_isAdmissible [CompactSpace (Induction.LeftQuotient P)]
    (hm : Continuous h.projection) (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) :
    ((normalizedInductionFunctor h hU).obj A).IsAdmissible :=
  smoothInduced_inducingRepresentation_isAdmissible h hU hm A hA

/-- A uniform compact-picture integral duality on admissible inducing objects:
one measure `μ` on one subgroup `K`, and for every admissible `A` an
equivalence of the smooth dual of `i(A)` with `i(A∨)` characterized by the
integral of the coefficient pairing over `K`. -/
def IsUniformIntegralDuality (K : Subgroup G) [MeasurableSpace K] (μ : Measure K) : Prop :=
  ∀ A : SmoothRep.{0, uG, uV} ℂ M, A.IsAdmissible →
    ∃ E : Representation.Equiv
        ((normalizedInductionFunctor h hU).obj A).contragredient.representation
        ((normalizedInductionFunctor h hU).obj A.contragredient).representation,
      ∀ (ℓ : ((normalizedInductionFunctor h hU).obj A).contragredient)
        (f : (normalizedInductionFunctor h hU).obj A),
        smoothDualPairing ((normalizedInductionFunctor h hU).obj A).representation ℓ f =
          ∫ k : K, smoothDualPairing A.representation
            (Induction.eval P (inducingRepresentation h hU A.contragredient) (E ℓ) k)
            (Induction.eval P (inducingRepresentation h hU A) f k) ∂μ

/-- A uniform integral duality gives a natural family of isomorphisms
`i(A)∨ ≅ i(A∨)` on admissible objects. -/
theorem exists_natural_of_isUniformIntegralDuality (K : Subgroup G) [MeasurableSpace K]
    (μ : Measure K) (hdual : IsUniformIntegralDuality.{uG, uV} h hU K μ) :
    ∃ E : ∀ (A : SmoothRep.{0, uG, uV} ℂ M), A.IsAdmissible →
        (((normalizedInductionFunctor h hU).obj A).contragredient ≅
          (normalizedInductionFunctor h hU).obj A.contragredient),
      ∀ (A B : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) (hB : B.IsAdmissible)
        (f : A ⟶ B),
        SmoothRep.contragredientHom ((normalizedInductionFunctor h hU).map f) ≫ (E A hA).hom =
          (E B hB).hom ≫ (normalizedInductionFunctor h hU).map (SmoothRep.contragredientHom f) := by
  refine ⟨fun A hA => SmoothRep.mkIso
    (A := ((normalizedInductionFunctor h hU).obj A).contragredient)
    (B := (normalizedInductionFunctor h hU).obj A.contragredient)
    (Classical.choose (hdual A hA)), ?_⟩
  intro A B hA hB f
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro ℓ
  set EA := Classical.choose (hdual A hA) with hEA_def
  set EB := Classical.choose (hdual B hB) with hEB_def
  have hEA := Classical.choose_spec (hdual A hA)
  have hEB := Classical.choose_spec (hdual B hB)
  rw [← hEA_def] at hEA
  rw [← hEB_def] at hEB
  change EA (contragredientMap (SmoothRep.hom ((normalizedInductionFunctor h hU).map f)) ℓ) =
    SmoothRep.hom ((normalizedInductionFunctor h hU).map (SmoothRep.contragredientHom f)) (EB ℓ)
  rw [← EA.apply_symm_apply
    (SmoothRep.hom ((normalizedInductionFunctor h hU).map (SmoothRep.contragredientHom f)) (EB ℓ))]
  congr 1
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change smoothDualPairing _ ℓ (SmoothRep.hom ((normalizedInductionFunctor h hU).map f) x) =
    smoothDualPairing ((normalizedInductionFunctor h hU).obj A).representation
      (EA.symm (SmoothRep.hom ((normalizedInductionFunctor h hU).map
        (SmoothRep.contragredientHom f)) (EB ℓ))) x
  rw [hEA, EA.apply_symm_apply, hEB]
  rfl

/-- An integral-characterized equivalence in the form produced by
`Induction.exists_integralDualEquiv` gives one in the form used by
`IsUniformIntegralDuality`. The two forms differ only by unfolding the induction
functor; the transfer goes through identity equivalences so that no
definitional unfolding of smooth-dual carriers is needed. -/
theorem exists_functorEquiv_of_twistEquiv (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (A : SmoothRep.{0, uG, uV} ℂ M)
    (E : Representation.Equiv
        (smoothContragredient (Induction.smoothInduced P (inducingRepresentation h hU A)))
        (Induction.smoothInduced P
          (Langlands.twist (HaarModulus.closedHalfCharacter U hU P h.le_normalizer)
            ((smoothContragredient A.representation).comp h.projection))))
    (hE : ∀ (ℓ : SmoothDual (Induction.smoothInduced P (inducingRepresentation h hU A)))
        (f : Induction.SmoothFunctions P (inducingRepresentation h hU A)),
        smoothDualPairing _ ℓ f =
          ∫ k : K, smoothDualPairing A.representation
            (Induction.eval P _ (E ℓ) k) (Induction.eval P _ f k) ∂μ) :
    ∃ E : Representation.Equiv
        ((normalizedInductionFunctor h hU).obj A).contragredient.representation
        ((normalizedInductionFunctor h hU).obj A.contragredient).representation,
      ∀ (ℓ : ((normalizedInductionFunctor h hU).obj A).contragredient)
        (f : (normalizedInductionFunctor h hU).obj A),
        smoothDualPairing ((normalizedInductionFunctor h hU).obj A).representation ℓ f =
          ∫ k : K, smoothDualPairing A.representation
            (Induction.eval P (inducingRepresentation h hU A.contragredient) (E ℓ) k)
            (Induction.eval P (inducingRepresentation h hU A) f k) ∂μ := by
  let e0 : ((normalizedInductionFunctor h hU).obj A).representation.Equiv
      (Induction.smoothInduced P (inducingRepresentation h hU A)) :=
    Representation.Equiv.refl _
  let e2 : (Induction.smoothInduced P
      (Langlands.twist (HaarModulus.closedHalfCharacter U hU P h.le_normalizer)
        ((smoothContragredient A.representation).comp h.projection))).Equiv
      ((normalizedInductionFunctor h hU).obj A.contragredient).representation :=
    Representation.Equiv.refl _
  refine ⟨((smoothContragredientEquiv e0.symm).trans E).trans e2, fun ℓ f => ?_⟩
  exact hE (smoothContragredientEquiv e0.symm ℓ) (e0 f)

end Generic

section Rational

open _root_.AlgebraicGeometry GroupScheme
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open RationalPointFamily

universe u

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The standard-cocharacter statement realizes the actual standard parabolic as
the rational points of a dynamic parabolic. -/
theorem exists_parabolic_eq_dynamic (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) :
    ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      parabolic i ν I = (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) := by
  have := hG.isSeparated
  obtain ⟨hexists, hcompare⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨ζ, hζ⟩ := hexists
  obtain ⟨hP, -, -⟩ := hcompare ζ hζ
  refine ⟨CommGroupScheme.groupHom ζ ≫ i, ?_⟩
  change (standardParabolic i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)) = _
  rw [hP]

/-- The dynamic quotient-compactness statement makes the right-coset space
`P \ G` of the actual standard parabolic compact. -/
theorem compactSpace_leftQuotient_parabolic
    (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    CompactSpace (Induction.LeftQuotient (parabolic i ν I)) := by
  obtain ⟨χ, hχ⟩ := exists_parabolic_eq_dynamic i ν hStandard hG hi hν I
  have hc := (hcompact k G hG χ).2
  rw [hχ]
  exact hc

end Rational

end Langlands.Aubert.General
