import Langlands.Representation.Induction.OpenSubgroupRestriction
import Langlands.Representation.Induction.UnramifiedCompactStabilizer
import Langlands.Representation.Aubert.General.InductionCarrierTransport
import Langlands.Weil.Representation.ContinuityProof

/-!
# Actual compact pictures for normalized induction and unramified twists

The half-modulus and unramified pullback are proved trivial on the actual
compact intersection. Restriction therefore identifies every twisted
normalized induction with one fixed space of actual compact sections.
-/

noncomputable section

open scoped NNReal

namespace Langlands.HaarModulus

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- The actual positive normalizing character is trivial on the intersection
of a closed inducing subgroup with a compact open subgroup. -/
theorem closedHalfCharacter_eq_one_of_mem_compactOpen
    (U P : Subgroup G) (hU : IsClosed (U : Set G))
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) (hP : IsClosed (P : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {p : P}
    (hp : (p : G) ∈ K) : closedHalfCharacter U hU P hPU p = 1 := by
  have hp' : p ∈ Induction.conjOpenSubgroup P K 1 := by
    simpa only [Induction.mem_conjOpenSubgroup, inv_one, one_mul, mul_one] using hp
  have hδ := RankinSelberg.LastRowReduction.eq_one_of_isCompact
    (closedRestrictCharacter U hU P hPU)
    (Weil.continuous_of_open_kernel _ (isOpen_ker_closedRestrictCharacter U hU P hPU))
    (Induction.conjOpenSubgroup P K 1).toSubgroup
    (Induction.isCompact_conjOpenSubgroup P hP K hK 1) hp'
  let := hU.locallyCompactSpace
  change p ∈ (closedHalfCharacter U hU P hPU).ker
  rw [closedHalfCharacter_eq, halfCharacter_ker]
  exact hδ

end Langlands.HaarModulus

namespace Langlands.Plancherel

open Aubert.General Induction

universe uG uI uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)

/-- The unnormalized Levi action on the actual intersection `P ∩ K`. -/
abbrev compactPictureInducingRepresentation (A : SmoothRep.{0, uG, uV} ℂ M) :
    Representation ℂ (P.comap K.toSubgroup.subtype) A :=
  (A.representation.comp h.projection).comp
    (K.toSubgroup.subtype.subgroupComap P)

/-- The fixed actual space of compact-picture sections; its right action is by `K`. -/
abbrev CompactInductionPicture (A : SmoothRep.{0, uG, uV} ℂ M) :=
  SmoothFunctions (P.comap K.toSubgroup.subtype)
    (compactPictureInducingRepresentation h K A)

variable (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G))
  (hK : IsCompact (K : Set G))

include hP hK in
/-- Restricting the actual normalized inducing action removes its half-character. -/
theorem normalized_compactPictureInducing_eq
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    openSubgroupInducingRepresentation P K (inducingRepresentation h hU A) =
      compactPictureInducingRepresentation h K A := by
  apply MonoidHom.ext
  intro p
  apply LinearMap.ext
  intro v
  change (HaarModulus.closedHalfCharacter U hU P h.le_normalizer
    (K.toSubgroup.subtype.subgroupComap P p) : ℂ) •
      A.representation (h.projection (K.toSubgroup.subtype.subgroupComap P p)) v =
        A.representation (h.projection (K.toSubgroup.subtype.subgroupComap P p)) v
  rw [HaarModulus.closedHalfCharacter_eq_one_of_mem_compactOpen U P hU
    h.le_normalizer hP K hK p.1.property]
  exact one_smul ℂ _

variable (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

/-- Literal restriction gives the compact picture of actual normalized induction. -/
def normalizedInductionCompactEquiv (A : SmoothRep.{0, uG, uV} ℂ M) :
    Representation.Equiv
      (((normalizedInductionFunctor h hU).obj A).representation.comp K.toSubgroup.subtype)
      (smoothInduced (P.comap K.toSubgroup.subtype)
        (compactPictureInducingRepresentation h K A)) :=
  (openSubgroupInductionEquiv P K (inducingRepresentation h hU A) hPK).trans
    (smoothInducedEquiv _ (equivOfRepresentationEq
      (normalized_compactPictureInducing_eq h K hU hP hK A)))

@[simp]
theorem normalizedInductionCompactEquiv_eval (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (normalizedInductionFunctor h hU).obj A) (k : K) :
    eval _ _ (normalizedInductionCompactEquiv h K hU hP hK hPK A f) k =
      eval P (inducingRepresentation h hU A) f k := rfl

/-- The inverse is the actual normalized covariance extension. -/
@[simp]
theorem normalizedInductionCompactEquiv_symm_mul (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : CompactInductionPicture h K A) (p : P) (k : K) :
    eval P (inducingRepresentation h hU A)
      ((normalizedInductionCompactEquiv h K hU hP hK hPK A).symm f)
      ((p : G) * (k : G)) =
        (inducingRepresentation h hU A p) (eval _ _ f k) :=
  openSubgroupInductionEquiv_symm_mul P K (inducingRepresentation h hU A) hPK _ p k

variable {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)

include hP hK hν hr in
omit [LocallyCompactSpace G] in
/-- An actual unramified twist does not change the inducing action on the
compact intersection. Continuity of the actual Levi projection is explicit. -/
theorem unramified_compactPictureInducing_eq
    (χ : unramifiedCharacters ν) (A : SmoothRep.{0, uG, uV} ℂ M) :
    compactPictureInducingRepresentation h K
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) =
      compactPictureInducingRepresentation h K A := by
  apply MonoidHom.ext
  intro p
  apply LinearMap.ext
  intro v
  have hp : K.toSubgroup.subtype.subgroupComap P p ∈ conjOpenSubgroup P K 1 := by
    apply mem_conjOpenSubgroup.mpr
    change (1 : G)⁻¹ * ((p.1 : K) : G) * 1 ∈ K
    simp only [inv_one, one_mul, mul_one]
    exact p.1.property
  have hχ := unramifiedPullback_eq_one_of_mem_conjOpenSubgroup P hP ν hν
    h.projection hr χ K hK 1 hp
  change (χ.val (h.projection (K.toSubgroup.subtype.subgroupComap P p)) : ℂ) •
    A.representation (h.projection (K.toSubgroup.subtype.subgroupComap P p)) v =
      A.representation (h.projection (K.toSubgroup.subtype.subgroupComap P p)) v
  rw [hχ]
  exact one_smul ℂ _

/-- All actual unramified twists restrict to one fixed compact-picture carrier. -/
def unramifiedNormalizedInductionCompactEquiv
    (χ : unramifiedCharacters ν) (A : SmoothRep.{0, uG, uV} ℂ M) :
    Representation.Equiv
      (((normalizedInductionFunctor h hU).obj
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))).representation.comp
          K.toSubgroup.subtype)
      (smoothInduced (P.comap K.toSubgroup.subtype)
        (compactPictureInducingRepresentation h K A)) :=
  (normalizedInductionCompactEquiv h K hU hP hK hPK
    (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))).trans
    (smoothInducedEquiv _ (equivOfRepresentationEq
      (unramified_compactPictureInducing_eq h K hP hK ν hν hr χ A)))

@[simp]
theorem unramifiedNormalizedInductionCompactEquiv_eval
    (χ : unramifiedCharacters ν) (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (normalizedInductionFunctor h hU).obj
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) (k : K) :
    eval _ _ (unramifiedNormalizedInductionCompactEquiv h K hU hP hK hPK ν hν hr χ A f) k =
      eval _ _ f k := rfl

/-- The inverse compact-picture map extends by the actual twisted normalized
covariance, with no choice of a tensor decomposition. -/
@[simp]
theorem unramifiedNormalizedInductionCompactEquiv_symm_mul
    (χ : unramifiedCharacters ν) (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : CompactInductionPicture h K A) (p : P) (k : K) :
    eval _ _
      ((unramifiedNormalizedInductionCompactEquiv h K hU hP hK hPK ν hν hr χ A).symm f)
      ((p : G) * (k : G)) =
        (inducingRepresentation h hU
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) p)
          (eval _ _ f k) :=
  openSubgroupInductionEquiv_symm_mul P K _ hPK _ p k

variable {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}

/-- Coefficient transport on the fixed compact picture is actual postcomposition. -/
def compactInductionPictureEquiv (e : A.representation.Equiv B.representation) :
    (smoothInduced (P.comap K.toSubgroup.subtype)
      (compactPictureInducingRepresentation h K A)).Equiv
    (smoothInduced (P.comap K.toSubgroup.subtype)
      (compactPictureInducingRepresentation h K B)) :=
  smoothInducedEquiv _ (Representation.Equiv.mk e.toLinearEquiv
    (fun p => e.isIntertwining' (h.projection (K.toSubgroup.subtype.subgroupComap P p))))

omit [LocallyCompactSpace G] in
@[simp]
theorem compactInductionPictureEquiv_eval (e : A.representation.Equiv B.representation)
    (f : CompactInductionPicture h K A) (k : K) :
    eval _ _ (compactInductionPictureEquiv h K e f) k = e (eval _ _ f k) := rfl

/-- The actual normalized representative transport commutes with restriction. -/
theorem normalizedInductionCompactEquiv_natural
    (e : A.representation.Equiv B.representation)
    (f : (normalizedInductionFunctor h hU).obj A) :
    normalizedInductionCompactEquiv h K hU hP hK hPK B
      (normalizedInductionEquivOfEquiv h hU e f) =
        compactInductionPictureEquiv h K e
          (normalizedInductionCompactEquiv h K hU hP hK hPK A f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rfl

/-- Twisting an actual representative equivalence before restriction gives
the same pointwise map on the fixed compact picture. -/
theorem unramifiedNormalizedInductionCompactEquiv_natural
    (χ : unramifiedCharacters ν) (e : A.representation.Equiv B.representation)
    (f : (normalizedInductionFunctor h hU).obj
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) :
    unramifiedNormalizedInductionCompactEquiv h K hU hP hK hPK ν hν hr χ B
      (normalizedInductionEquivOfEquiv h hU
        (twistEquiv χ.val.toMonoidHom e) f) =
      compactInductionPictureEquiv h K e
        (unramifiedNormalizedInductionCompactEquiv h K hU hP hK hPK ν hν hr χ A f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rfl

end Langlands.Plancherel
