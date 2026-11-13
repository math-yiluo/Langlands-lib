import Langlands.Representation.Aubert.General.SharpConsequenceStatements
import Langlands.Representation.Aubert.General.SupportCategoryReductions
import Langlands.Representation.Aubert.General.RationalSharpConsequenceTargets
import Langlands.Representation.Aubert.General.RationalInductionTarget
import Langlands.Representation.Aubert.General.RationalInvolutivityReduction
import Langlands.Representation.Aubert.General.RationalCuspidalEigenvalueProof
import Langlands.Representation.Aubert.General.RationalLeviCuspidalJacquet
import Langlands.Representation.Aubert.General.RationalWeylComparisonProof
import Langlands.Representation.Aubert.General.RootAssociationLaws
import Langlands.Representation.Aubert.General.RationalStandardParabolicTransport
import Langlands.Representation.Aubert.General.RationalLeviFiniteLengthProof
import Langlands.Representation.Smooth.IrreducibleClassDetection
import Langlands.Representation.Smooth.FiniteExactEuler
import Langlands.Representation.Aubert.General.SharpFiniteLength

/-!
# Reduction of the irreducibility of `E#` to the class formula and Theorem 1.7

Aubert's Corollaire 3.9 (b) (1995, p. 2189): for `E` in the cuspidal series
`𝔈(I)`, the terminal cokernel `E#` is irreducible. The argument is a length
count in the exact finite-length Grothendieck group, using the integer-valued
composition length `FiniteLengthGrothendieckGroup.compositionLength`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uR uG uV

open IrreducibleGrothendieckProof

namespace FiniteLengthGrothendieckGroup

section Length

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- The composition length of the class of an actual finite-length
representation is its length over the group algebra. -/
theorem exists_compositionLength_ofRepresentation (A : SmoothRep.{uR, uG, uV} k G)
    (hA : A.HasFiniteLength) :
    ∃ n : ℕ, repLength A.representation = n ∧
      compositionLength (ofRepresentation A hA) = (n : ℤ) := by
  obtain ⟨n, s, hs⟩ := chosenSeries ⟨A, hA⟩
  exact ⟨n, repLength_eq_of_hasSimpleFactors s hs, compositionLength_of_series A hA s hs⟩

/-- An actual finite-length representation is irreducible exactly when its
class has composition length one. -/
theorem compositionLength_ofRepresentation_eq_one_iff (A : SmoothRep.{uR, uG, uV} k G)
    (hA : A.HasFiniteLength) :
    compositionLength (ofRepresentation A hA) = 1 ↔ A.IsIrreducible := by
  obtain ⟨n, hn, hc⟩ := exists_compositionLength_ofRepresentation A hA
  refine Iff.trans ?_ (repLength_eq_one_iff (ρ := A.representation))
  rw [hc, hn]
  constructor
  · intro h
    have h1 : n = 1 := by exact_mod_cast h
    rw [h1]
    rfl
  · intro h
    have h1 : n = 1 := by exact_mod_cast h
    rw [h1]
    rfl

/-- A nonzero class of an actual finite-length representation has composition
length at least one. -/
theorem one_le_compositionLength_of_ne_zero (A : SmoothRep.{uR, uG, uV} k G)
    (hA : A.HasFiniteLength) (h : ofRepresentation A hA ≠ 0) :
    1 ≤ compositionLength (ofRepresentation A hA) := by
  obtain ⟨n, hn, hc⟩ := exists_compositionLength_ofRepresentation A hA
  rw [hc]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exfalso
    apply h
    rw [h0] at hn
    have : Subsingleton A.obj := repLength_eq_zero_iff.mp (by exact_mod_cast hn)
    exact ofRepresentation_eq_zero_of_subsingleton A hA
  · exact_mod_cast hpos

end Length

section Bound

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Let `C` be a class of smooth representations closed under actual
subquotients, and let `F` be an integer-linear endomorphism of the exact
finite-length Grothendieck group sending the class of every irreducible member
of `C` to an element of composition length at least one. Then `F` does not
decrease the composition length of the class of a finite-length member of
`C`. The proof sums over an actual composition series. -/
theorem compositionLength_le_of_irreducible
    (C : SmoothRep.{0, uG, uV} ℂ G → Prop)
    (hC : ∀ A B : SmoothRep.{0, uG, uV} ℂ G, C A → IsSubquotient B A → C B)
    (F : FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ G)
    (hF : ∀ (τ : SmoothRep.{0, uG, uV} ℂ G) (hτ : τ.IsIrreducible), C τ →
      1 ≤ compositionLength (F (ofRepresentation τ (hasFiniteLength_of_isIrreducible hτ))))
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.HasFiniteLength) (hCA : C A) :
    compositionLength (ofRepresentation A hA) ≤
      compositionLength (F (ofRepresentation A hA)) := by
  obtain ⟨n, s, hs⟩ := chosenSeries ⟨A, hA⟩
  have hsum : ofRepresentation A hA = ∑ i : Fin n,
      ofRepresentation (gradedSmooth s i) (hasFiniteLength_of_isIrreducible (hs i)) := by
    rw [← realize_seriesClass s hs hA, seriesClass, map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      realizeIrreducibles_generator_irreducibleIsoClass _ (hs i) _
  have hgr (i : Fin n) : C (gradedSmooth s i) :=
    hC A _ hCA (isSubquotient_iff_exists.mpr
      ⟨subrepresentation A (s.subrepresentation i.succ), subtype A _,
        ofHom (s.gradedProjection i).hom, subtype_injective A _,
        s.gradedProjection_surjective i⟩)
  rw [compositionLength_of_series A hA s hs, hsum, map_sum, map_sum]
  calc (n : ℤ) = ∑ _i : Fin n, (1 : ℤ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => hF _ (hs i) (hgr i)

end Bound

end FiniteLengthGrothendieckGroup

end Langlands.SmoothRep

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep SmoothRep.FiniteLengthGrothendieckGroup

section LeviEigenvalue

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))

include h in
/-- Aubert's Theorem 1.7 (4) for the Levi operator of a standard Levi `M J`:
an actual irreducible Levi-cuspidal representation `σ` of `M J` has eigenvalue
`(-1)^{|J|}`. Only the term of the full index set survives; it is `σ` itself
because the parabolic is all of `M J` and the radical is trivial. -/
theorem leviAlternatingOperator_cuspidal (J : Finset ι) (hM : IsClosed (M J : Set G))
    (hJ : ∀ I : Finset J, IsSemidirectDecomposition ((P (leviIndex J I)).subgroupOf (M J))
      ((M (leviIndex J I)).subgroupOf (M J)) ((U (leviIndex J I)).subgroupOf (M J)))
    (hfl : letI := hM.locallyCompactSpace
      ∀ I : Finset J, ParabolicFiniteLength.{uG, max uG uV} (hJ I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val))
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M J)) (hσ : σ.IsIrreducible)
    (hc : IsLeviCuspidal P M U hU J hM hJ σ) :
    leviAlternatingOperator.{uI, uG, uV} P M U J hM hJ hU hfl
        (ofRepresentation σ (hasFiniteLength_of_isIrreducible hσ)) =
      ((-1 : ℤ) ^ J.card) • ofRepresentation σ (hasFiniteLength_of_isIrreducible hσ) := by
  let _ := hM.locallyCompactSpace
  have hPtop : (P (leviIndex J Finset.univ)).subgroupOf (M J) = ⊤ := by
    rw [CuspidalEmbedding.leviIndex_univ]
    exact Subgroup.subgroupOf_eq_top.mpr (h J).levi_le
  have hUbot : (U (leviIndex J Finset.univ)).subgroupOf (M J) = ⊥ := by
    rw [CuspidalEmbedding.leviIndex_univ, Subgroup.subgroupOf_eq_bot, Subgroup.disjoint_def]
    intro x hxU hxM
    have h1 := (h J).projection_levi ⟨x, hxM⟩
    have h2 := (h J).projection_unipotent ⟨x, hxU⟩
    have h3 : (⟨x, (h J).levi_le hxM⟩ : P J) = ⟨x, (h J).unipotent_le hxU⟩ := rfl
    rw [h3, h2] at h1
    exact (congrArg Subtype.val h1).symm
  have hδ : IsUnimodularModulus ((U (leviIndex J Finset.univ)).subgroupOf (M J))
      ((hU (leviIndex J Finset.univ)).preimage continuous_subtype_val) := by
    intro u
    obtain ⟨x, hx⟩ := u
    have hx' : x ∈ (⊥ : Subgroup (M J)) := hUbot ▸ hx
    rw [Subgroup.mem_bot] at hx'
    subst hx'
    exact map_one _
  refine (alternatingOperator_ofRepresentation _ _ _ hJ _ hfl σ
    (hasFiniteLength_of_isIrreducible hσ)).trans ?_
  rw [Finset.sum_eq_single Finset.univ]
  · rw [RationalPointFamily.inductionJacquetClass_of_top_bot (hJ Finset.univ) _ hδ hPtop hUbot σ
      (hasFiniteLength_of_isIrreducible hσ), Finset.card_univ, Fintype.card_coe]
  · intro I _ hI
    have hz : Subsingleton ((jacquetFunctor.{uG, max uG uV} (hJ I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val)).obj σ).obj := hc ⟨I, hI⟩
    have hrfl := (hfl I).2.2.1 σ (hasFiniteLength_of_isIrreducible hσ)
    have h0 := IrreducibleGrothendieckProof.ofRepresentation_eq_zero_of_subsingleton _ hrfl
    erw [← inductionK0_ofRepresentation (hJ I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val) (hfl I).1 (hfl I).2.1 _ hrfl]
    rw [h0, map_zero, smul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

end LeviEigenvalue

section CuspidalInduction

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hM : ∀ J, IsClosed (M J : Set G))
  (hL : ∀ (J : Finset ι) (I : Finset J),
    IsSemidirectDecomposition ((P (leviIndex J I)).subgroupOf (M J))
      ((M (leviIndex J I)).subgroupOf (M J)) ((U (leviIndex J I)).subgroupOf (M J)))

/-- Aubert's identity `D_G [i_I σ] = (-1)^{|I|} [i_I σ]` for an actual
irreducible Levi-cuspidal `σ` of `M I`: Theorem 1.7 (2) moves `D_G` past
`i_I` to the Levi operator, where `leviAlternatingOperator_cuspidal` applies. -/
theorem alternatingOperator_cuspidalInduction
    (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
    (hLeviFl : ∀ J, letI := (hM J).locallyCompactSpace
      ∀ I : Finset J, ParabolicFiniteLength.{uG, max uG uV} (hL J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val))
    (hcompat : InductionCompatibilityStatement.{uI, uG, uV} P M U h hU hfl hM hL hLeviFl)
    (I : Finset ι) (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)) (hσ : σ.IsIrreducible)
    (hc : IsLeviCuspidal P M U hU I (hM I) (hL I) σ) :
    alternatingOperator.{uI, uG, uV} P M U h hU hfl
        (ofRepresentation ((normalizedInductionFunctor.{uG, max uG uV} (h I) (hU I)).obj σ)
          ((hfl I).1 σ (hasFiniteLength_of_isIrreducible hσ))) =
      ((-1 : ℤ) ^ I.card) • ofRepresentation
          ((normalizedInductionFunctor.{uG, max uG uV} (h I) (hU I)).obj σ)
          ((hfl I).1 σ (hasFiniteLength_of_isIrreducible hσ)) := by
  rw [← inductionK0_ofRepresentation (h I) (hU I) (hfl I).1 (hfl I).2.1 σ
      (hasFiniteLength_of_isIrreducible hσ), ← LinearMap.comp_apply, hcompat I,
    LinearMap.comp_apply,
    leviAlternatingOperator_cuspidal P M U h hU I (hM I) (hL I) (hLeviFl I) σ hσ hc, map_zsmul]

end CuspidalInduction

section Closer

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Monotone P) (hU : Antitone U)
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
  (IsAssociate : Finset ι → Finset ι → G → Prop)

/-- Corollaire 3.9 (b) for an abstract standard family, from one finite-length
proof `hfl`, involutivity of `D_G` (Theorem 1.7 (3)), reflexivity of the
association at the identity, the class formula (Corollaire 3.9 (a)), and
Aubert's identity `D_G [i_I σ] = (-1)^{|I|} [i_I σ]` for irreducible
Levi-cuspidal `σ` (Theorem 1.7 (2) and (4)). Finite length of `E#` is derived
from `hfl` by the published `sharpFiniteLengthTarget_of_inductionJacquet`. -/
theorem sharpIrreducibleTarget_of_classFormula
    (hfl : ∀ J, ParabolicFiniteLength.{uG, max uG (max uI uV)} (h J) (hclosed J))
    (hinv : (alternatingOperator.{uI, uG, max uI uV} P M U h hclosed hfl).comp
        (alternatingOperator.{uI, uG, max uI uV} P M U h hclosed hfl) = LinearMap.id)
    (hrefl : ∀ I, IsAssociate I I 1)
    (hCF : SharpClassFormulaTarget.{uI, uG, uV} P M U h hclosed hδ hP hU hM hL IsAssociate)
    (hcusp : ∀ (I : Finset ι) (σ : SmoothRep.{0, uG, max uG (max uI uV)} ℂ (M I))
      (hσ : σ.IsIrreducible), IsLeviCuspidal P M U hclosed I (hM I) (hL I) σ →
        alternatingOperator.{uI, uG, max uI uV} P M U h hclosed hfl
            (ofRepresentation
              ((normalizedInductionFunctor.{uG, max uG (max uI uV)} (h I) (hclosed I)).obj σ)
              ((hfl I).1 σ (hasFiniteLength_of_isIrreducible hσ))) =
          ((-1 : ℤ) ^ I.card) • ofRepresentation
              ((normalizedInductionFunctor.{uG, max uG (max uI uV)} (h I) (hclosed I)).obj σ)
              ((hfl I).1 σ (hasFiniteLength_of_isIrreducible hσ))) :
    SharpIrreducibleTarget.{uI, uG, uV} P M U h hclosed hδ hP hU hM hL := by
  have hSFL : SharpFiniteLengthTarget.{uI, uG, uV} P M U h hclosed hδ hP hU :=
    sharpFiniteLengthTarget_of_inductionJacquet P M U h hclosed hδ hP hU
      (fun J A hA => inductionJacquet_hasFiniteLength.{uI, uG, max uI uV}
        P M U h hclosed hfl J A hA)
  intro I E hE
  obtain ⟨hEirr, σ, hσ, hc, hsub⟩ := hE
  let D := alternatingOperator.{uI, uG, max uI uV} P M U h hclosed hfl
  let F := ((-1 : ℤ) ^ I.card) • D
  have hsign : ((-1 : ℤ) ^ I.card) * (-1 : ℤ) ^ I.card = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hFF (x) : F (F x) = x := by
    change ((-1 : ℤ) ^ I.card) • D (((-1 : ℤ) ^ I.card) • D x) = x
    rw [map_zsmul, smul_smul, hsign, one_smul]
    exact LinearMap.congr_fun hinv x
  -- On a finite-length member of `Alg({I})`, `F` is the class of `E#`.
  have hsharp (Y : SmoothRep.{0, uG, max uI uG uV} ℂ G)
      (hY : IsInSupportCategory.{uI, uG, max uI uV} P M U h hclosed IsAssociate I (hM I) (hL I) Y)
      (hYfl : Y.HasFiniteLength) :
      F (ofRepresentation Y hYfl) = ofRepresentation
        (StandardComplex.sharpObject.{uI, uG, max uI uV} P M U h hclosed hδ hP hU Y I)
        (hSFL I Y hYfl) := by
    change ((-1 : ℤ) ^ I.card) • D (ofRepresentation Y hYfl) = _
    rw [show D (ofRepresentation Y hYfl) = _ from hCF hfl I Y hY hYfl (hSFL I Y hYfl),
      smul_smul, hsign, one_smul]
  -- `F` sends every irreducible member of `Alg({I})` to a nonzero actual class.
  have hpos (τ : SmoothRep.{0, uG, max uI uG uV} ℂ G) (hτ : τ.IsIrreducible)
      (hτC : IsInSupportCategory.{uI, uG, max uI uV} P M U h hclosed IsAssociate I
        (hM I) (hL I) τ) :
      1 ≤ compositionLength (F (ofRepresentation τ (hasFiniteLength_of_isIrreducible hτ))) := by
    rw [hsharp τ hτC]
    apply one_le_compositionLength_of_ne_zero
    intro h0
    have h1 := hFF (ofRepresentation τ (hasFiniteLength_of_isIrreducible hτ))
    rw [hsharp τ hτC, h0, map_zero] at h1
    have h2 := (compositionLength_ofRepresentation_eq_one_iff τ
      (hasFiniteLength_of_isIrreducible hτ)).mpr hτ
    rw [← h1, map_zero] at h2
    exact zero_ne_one h2
  have hcore := compositionLength_le_of_irreducible
    (IsInSupportCategory.{uI, uG, max uI uV} P M U h hclosed IsAssociate I (hM I) (hL I))
    (fun _ _ hA hBA => hA.of_isSubquotient hBA) F hpos
  -- The cuspidal induction `X = i_I(σ)` and the class identity `F [X] = [X]`.
  let X := (normalizedInductionFunctor.{uG, max uG (max uI uV)} (h I) (hclosed I)).obj σ
  have hXfl : X.HasFiniteLength := (hfl I).1 σ (hasFiniteLength_of_isIrreducible hσ)
  have hXC : IsInSupportCategory.{uI, uG, max uI uV} P M U h hclosed IsAssociate I
      (hM I) (hL I) X := isInSupportCategory_cuspidalInduction (hrefl I) σ hσ hc
  have hFX : F (ofRepresentation X hXfl) = ofRepresentation X hXfl := by
    change ((-1 : ℤ) ^ I.card) • D (ofRepresentation X hXfl) = _
    rw [show D (ofRepresentation X hXfl) = _ from hcusp I σ hσ hc, smul_smul, hsign, one_smul]
  -- Split `X` around its subquotient `E ≅ (S / T)`.
  obtain ⟨S, T, ⟨e⟩⟩ := hsub
  let Y := subrepresentation X S
  have hYfl : Y.HasFiniteLength := IrreducibleGrothendieckProof.subrepresentation_hasFiniteLength hXfl S
  have hQfl := FiniteExactEuler.quotient_hasFiniteLength hXfl S
  have hY1fl := IrreducibleGrothendieckProof.subrepresentation_hasFiniteLength hYfl T
  have hY2fl := FiniteExactEuler.quotient_hasFiniteLength hYfl T
  have hEfl := hasFiniteLength_of_isIrreducible hEirr
  have hX := ofRepresentation_shortExact hYfl hXfl hQfl (subtype_mkQ_isShortExact X S)
  have hY := ofRepresentation_shortExact hY1fl hYfl hY2fl (subtype_mkQ_isShortExact Y T)
  have hE : ofRepresentation E hEfl = ofRepresentation (quotient Y T) hY2fl :=
    ofObject_eq_of_iso (A := ⟨E, hEfl⟩) (B := ⟨quotient Y T, hY2fl⟩) e
  have hYC : IsInSupportCategory.{uI, uG, max uI uV} P M U h hclosed IsAssociate I
      (hM I) (hL I) Y :=
    hXC.of_isSubquotient (subrepresentation_isSubrepresentation S).isSubquotient
  have hQC := hXC.of_isSubquotient (quotient_isQuotient S).isSubquotient
  have hY1C := hYC.of_isSubquotient (subrepresentation_isSubrepresentation T).isSubquotient
  have hEC := hXC.of_isSubquotient ⟨S, T, ⟨e⟩⟩
  have h1 := hcore _ hY1fl hY1C
  have h2 := hcore _ hQfl hQC
  have hEone := (compositionLength_ofRepresentation_eq_one_iff E hEfl).mpr hEirr
  have hlen := congrArg compositionLength hFX
  rw [hX, hY, ← hE] at hlen
  simp only [map_add] at hlen
  have hle : compositionLength (F (ofRepresentation E hEfl)) ≤ 1 := by linarith
  have hge := hpos E hEirr hEC
  rw [hsharp E hEC hEfl] at hle
  rw [hsharp E hEC] at hge
  exact (compositionLength_ofRepresentation_eq_one_iff _ _).mp (le_antisymm hle hge)

end Closer

namespace RationalPointFamily

universe u v

open _root_.AlgebraicGeometry GroupScheme
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

/-- Corollaire 3.9 (b) on the actual families from the two dynamic
finite-length statements (Renard VI.6.2, VI.6.4), induction compatibility
(Theorem 1.7 (2)), involutivity of `D_G` (Theorem 1.7 (3)) and the class
formula (Corollaire 3.9 (a)). Finite length of `E#` follows from the dynamic
finite-length statements inside the generic closer. The association hypotheses
`hN`, `hZ` are supplied by `rationalWeylComparison`, finite length inside the
standard Levis by `rationalLeviFiniteLengthStatement`, and the Levi cuspidal
eigenvalue by `leviAlternatingOperator_cuspidal`. -/
theorem rationalSharpIrreducibleStatement_of_inputs
    (hiDyn : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
    (hrDyn : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v})
    (hcompat : RationalInductionCompatibilityStatement.{u, v})
    (hInv : RationalInvolutivityStatement.{u, v})
    (hCF : RationalSharpClassFormulaStatement.{u, v}) :
    RationalSharpIrreducibleStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder hInter hRoots hU hM hUc
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _
  obtain ⟨hN, hZ⟩ := rationalWeylComparison k G hG T i hi
  have hP := isClosed_standard_parabolic i ν hStandard hG hi hν
  have hproj := continuous_standard_projection i ν hStandard hG hi hν
  have hiFl := fun I =>
    standard_induction_preservesFiniteLength i ν hStandard hG hi hν hiDyn I (hU I)
  have hrFl := fun I =>
    standard_jacquet_preservesFiniteLength i ν hStandard hG hi hν hrDyn I (hU I)
  have hLFl := rationalLeviFiniteLengthStatement.{u, v} k G hG T i hi ν hν hStandard hInter hU hP
    hproj hUc hiFl hrFl
    (levi_isClosed i ν hStandard hG hi hν hP hproj)
  exact sharpIrreducibleTarget_of_classFormula _ _ _ _ _ _ _ _ _ _ (rootAssociation i ν hN hZ)
    (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
    (hInv k G hG T i hi ν hν hStandard hRoots hU hP hproj hUc hiFl hrFl)
    (rootAssociation_one i ν hN hZ)
    (hCF k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc)
    (alternatingOperator_cuspidalInduction _ _ _ _ _ _ _ _ _
      (inductionCompatibilityStatement_of_rational i ν hStandard hG hi hν hU hP hproj hUc hiFl
        hrFl hRoots hInter (fun J I => (hLFl J I).1) (fun J I => (hLFl J I).2) hcompat))

/-- The reduction of Aubert's Corollaire 3.9 (b) on the actual rational-point
families to five published propositions: finite-length preservation by the
actual dynamic normalized induction and Jacquet functors (Renard VI.6.2, VI.6.4,
at carrier universe `max (u + 1) v`), compatibility of `D_G` with standard
induction (Theorem 1.7 (2)), involutivity of `D_G` (Theorem 1.7 (3)) and the
signed class formula (Corollaire 3.9 (a)). Finite length of `E#` is derived
inside the proof from the two dynamic finite-length statements. -/
def RationalSharpIrreducibleReductionStatement : Prop :=
  DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
    DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
      RationalInductionCompatibilityStatement.{u, v} →
        RationalInvolutivityStatement.{u, v} →
          RationalSharpClassFormulaStatement.{u, v} →
            RationalSharpIrreducibleStatement.{u, v}

/-- The reduction holds, by `rationalSharpIrreducibleStatement_of_inputs`. -/
theorem rationalSharpIrreducibleReduction :
    RationalSharpIrreducibleReductionStatement.{u, v} :=
  fun hiDyn hrDyn hcompat hInv hCF =>
    rationalSharpIrreducibleStatement_of_inputs hiDyn hrDyn hcompat hInv hCF

end RationalPointFamily

end Langlands.Aubert.General
