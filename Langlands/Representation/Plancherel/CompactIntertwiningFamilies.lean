import Langlands.Representation.Plancherel.NormalizedCompactPicture
import Langlands.Representation.Plancherel.StandardIntertwiningTargetLaws
import Langlands.Representation.Plancherel.UnramifiedOperatorFamilies

/-!
# Actual compact-picture operator families

Restriction identifies actual Levi-normalized unramified inductions with
fixed compact pictures. Conjugating the actual full-source standard integral
by these identifications gives its compact-picture family. Full convergence
and the squared-modulus identity remain explicit prerequisites.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining

universe uG uI uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)

/-- The actual positive Levi-normalized induction at an unramified parameter. -/
abbrev UnramifiedLeviInduction (χ : unramifiedCharacters ν)
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M) :=
  (DynamicNormalization.leviTwistedInductionFunctor h hU).obj
    (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))

/-- Restriction to the chosen compact subgroup, with the actual full/Levi
normalization comparison, identifies every twist with the same compact space. -/
def unramifiedLeviInductionCompactEquiv (χ : unramifiedCharacters ν)
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M) :
    UnramifiedLeviInduction h hU ν χ A ≃ₗ[ℂ] CompactInductionPicture h K A :=
  (normalizedInductionLeviEquiv h hU hδ
    (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))).symm.toLinearEquiv.trans
      (unramifiedNormalizedInductionCompactEquiv h K hU hP hK hPK ν hν hr χ A).toLinearEquiv

@[simp]
theorem unramifiedLeviInductionCompactEquiv_eval (χ : unramifiedCharacters ν)
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    (f : UnramifiedLeviInduction h hU ν χ A) (k : K) :
    eval _ _ (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A f) k =
      eval _ _ f (k : G) := rfl

/-- The inverse is extension by the actual twisted positive normalized action. -/
theorem unramifiedLeviInductionCompactEquiv_symm_mul (χ : unramifiedCharacters ν)
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    (f : CompactInductionPicture h K A) (p : P) (k : K) :
    eval _ _
      ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f)
      ((p : G) * (k : G)) =
        (inducingRepresentation h hU
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) p)
          (eval _ _ f k) :=
  unramifiedNormalizedInductionCompactEquiv_symm_mul h K hU hP hK hPK ν hν hr χ A f p k

variable {A : Langlands.SmoothRep.{0, uG, uV} ℂ M}
  {B : Langlands.SmoothRep.{0, uG, uW} ℂ M}

/-- Representative transport is the same fixed pointwise map on the compact
picture for every unramified parameter. -/
theorem unramifiedLeviInductionCompactEquiv_natural (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv B.representation)
    (f : UnramifiedLeviInduction h hU ν χ A) :
    unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ B
        (inducedMap h hU (twistEquiv χ.val.toMonoidHom e).toIntertwiningMap f) =
      compactInductionPictureEquiv h K e
        (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rfl

theorem unramifiedLeviInductionCompactEquiv_symm_natural (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv B.representation) (f : CompactInductionPicture h K A) :
    (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ B).symm
        (compactInductionPictureEquiv h K e f) =
      inducedMap h hU (twistEquiv χ.val.toMonoidHom e).toIntertwiningMap
        ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f) := by
  apply (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ B).injective
  rw [LinearEquiv.apply_symm_apply, unramifiedLeviInductionCompactEquiv_natural,
    LinearEquiv.apply_symm_apply]

variable {P' U' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  (hδ' : IsUnimodularModulus U' hU') (hP' : IsClosed (P' : Set G))
  (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hr' : Continuous h'.projection)

/-- The source's compact-picture conjugation of an actual ambient intertwiner. -/
def compactIntertwiningOperator (χ : unramifiedCharacters ν)
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    (J : (UnramifiedLeviInduction h hU ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν χ A).representation) :
    CompactInductionPicture h K A →ₗ[ℂ] CompactInductionPicture h' K A :=
  (unramifiedLeviInductionCompactEquiv h' hU' hδ' K hP' hK hP'K ν hν hr' χ A).toLinearMap.comp
    (J.toLinearMap.comp
      (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm.toLinearMap)

@[simp]
theorem compactIntertwiningOperator_eval (χ : unramifiedCharacters ν)
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    (J : (UnramifiedLeviInduction h hU ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν χ A).representation)
    (f : CompactInductionPicture h K A) (k : K) :
    eval _ _ (compactIntertwiningOperator h hU hδ K hP hK hPK ν hν hr
      h' hU' hδ' hP' hP'K hr' χ A J f) k =
        eval _ _ (J
          ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f))
          (k : G) := rfl

/-- The compact-picture representative square follows from the actual
ambient square; its vertical maps are fixed independently of the parameter. -/
theorem compactIntertwiningOperator_natural (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv B.representation)
    (JA : (UnramifiedLeviInduction h hU ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν χ A).representation)
    (JB : (UnramifiedLeviInduction h hU ν χ B).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν χ B).representation)
    (hJ : ∀ f, JB (inducedMap h hU (twistEquiv χ.val.toMonoidHom e).toIntertwiningMap f) =
      inducedMap h' hU' (twistEquiv χ.val.toMonoidHom e).toIntertwiningMap (JA f))
    (f : CompactInductionPicture h K A) :
    compactIntertwiningOperator h hU hδ K hP hK hPK ν hν hr
        h' hU' hδ' hP' hP'K hr' χ B JB (compactInductionPictureEquiv h K e f) =
      compactInductionPictureEquiv h' K e
        (compactIntertwiningOperator h hU hδ K hP hK hPK ν hν hr
          h' hU' hδ' hP' hP'K hr' χ A JA f) := by
  change unramifiedLeviInductionCompactEquiv h' hU' hδ' K hP' hK hP'K ν hν hr' χ B
    (JB ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ B).symm
      (compactInductionPictureEquiv h K e f))) = _
  rw [unramifiedLeviInductionCompactEquiv_symm_natural, hJ,
    unramifiedLeviInductionCompactEquiv_natural]
  rfl

section StandardIntegral

variable [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')] [T2Space G]
  (qν : Measure (QuotientSpace (U := U) U'))
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
  (hM : IsClosed (M : Set G)) (hsq : SquaredModulusCompatibility h hU h' hU')

/-- The compact operator is the actual standard integral, only at parameters
where its original scalar-integral domain is the whole source. -/
def standardCompactOperator (χ : unramifiedCharacters ν)
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    (hfull : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤) :
    CompactInductionPicture h K A →ₗ[ℂ] CompactInductionPicture h' K A :=
  compactIntertwiningOperator h hU hδ K hP hK hPK ν hν hr
    h' hU' hδ' hP' hP'K hr' χ A
    (fullSourceIntertwiner h hU h' hU'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
      qν μU' μI hqν hM hsq hfull)

@[simp]
theorem standardCompactOperator_eval (χ : unramifiedCharacters ν)
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    (hfull : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    (f : CompactInductionPicture h K A) (k : K) :
    eval _ _ (standardCompactOperator h hU hδ K hP hK hPK ν hν hr
      h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq χ A hfull f) k =
      operator h hU U' (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
        qν hM (sourceToDomain h hU _ qν hfull
          ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f))
        (k : G) := rfl

/-- The original smooth-dual integral relation is retained on all of `G`
after extending the compact output by its actual normalized covariance. -/
theorem standardCompactOperator_spec (χ : unramifiedCharacters ν)
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    (hfull : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    (f : CompactInductionPicture h K A) :
    HasIntegral h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν
      ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f)
      (eval _ _
        ((unramifiedLeviInductionCompactEquiv h' hU' hδ' K hP' hK hP'K ν hν hr' χ A).symm
          (standardCompactOperator h hU hδ K hP hK hPK ν hν hr
            h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq χ A hfull f))) := by
  unfold standardCompactOperator compactIntertwiningOperator
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact fullSourceIntertwiner_spec h hU h' hU' _ qν μU' μI hqν hM hsq hfull _

/-- The actual integral's compact representative square, with the two
full-domain equalities separately visible. -/
theorem standardCompactOperator_natural (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv B.representation)
    (hfullA : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    (hfullB : domain h hU U'
      (B.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    (f : CompactInductionPicture h K A) :
    standardCompactOperator h hU hδ K hP hK hPK ν hν hr
        h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq χ B hfullB
        (compactInductionPictureEquiv h K e f) =
      compactInductionPictureEquiv h' K e
        (standardCompactOperator h hU hδ K hP hK hPK ν hν hr
          h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq χ A hfullA f) := by
  apply compactIntertwiningOperator_natural
  intro v
  exact congrArg (fun T => T v)
    (fullSourceIntertwiner_natural h hU h' hU' qν μU' μI hqν hM hsq
      hfullA hfullB (twistEquiv χ.val.toMonoidHom e).toIntertwiningMap)

/-- The rationality condition for the actual compact-picture standard
integral on a given parameter subset. It asserts rationality, not its proof;
the required full-domain equalities are separate arguments. -/
def StandardCompactRationalOn (Ω : Set (unramifiedCharacters ν))
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    (hfull : ∀ χ : Ω, domain h hU U'
      (A.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ.val)) qν = ⊤) :
    Prop :=
  UnramifiedOperatorFamily.IsRationalOperatorOn Ω
    (fun χ => standardCompactOperator h hU hδ K hP hK hPK ν hν hr
      h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq χ.val A (hfull χ))

end StandardIntegral

end Langlands.Plancherel
