import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Rational.StandardLeviConjugationProof
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme
import Mathlib.GroupTheory.Coset.Defs

/-! # The actual Weyl index and lower subgroups for the weak expansion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz.WeakExpansion

variable {F : Type u} [Field F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I I' : Set (characterLattice T))

/-- Forward conjugation: the all-test functor `n M_I n⁻¹`. -/
def conjugatedLevi (n : normalizerPoints i) : SubgroupFunctor G :=
  (standardLevi i ν I).comap (G.innerIso (n : rationalPoints G)).inv

/-- Forward conjugation: the all-test functor `n P_I n⁻¹`. -/
def conjugatedParabolic (n : normalizerPoints i) : SubgroupFunctor G :=
  (standardParabolic i ν I).comap (G.innerIso (n : rationalPoints G)).inv

/-- Forward conjugation: the all-test functor `n U_I n⁻¹`. -/
def conjugatedUnipotent (n : normalizerPoints i) : SubgroupFunctor G :=
  (standardUnipotent i ν I).comap (G.innerIso (n : rationalPoints G)).inv

/-- The actual Weyl elements carrying the inducing Levi into `M_{I'}`.
The inclusion is tested as an inclusion of subgroup functors, not only on `F`-points. -/
def admissibleWeylElements : Set (relativeWeylGroup i) :=
  {w | ∃ n : normalizerPoints i,
    QuotientGroup.mk n = w ∧ conjugatedLevi i ν I n ≤ standardLevi i ν I'}

/-- The image in `W^G` of the actual normalizer points lying in `M_{I'}(F)`. -/
abbrev lowerWeylSubgroup : Subgroup (relativeWeylGroup i) :=
  standardRelativeWeylGroup i ν I'

/-- The relation of belonging to the same left `W^{M'}`-orbit.
Mathlib calls this `rightRel`, since its equivalence classes are cosets `W^{M'}s`. -/
def weylIndexSetoid : Setoid (admissibleWeylElements i ν I I') :=
  Setoid.comap Subtype.val (QuotientGroup.rightRel (lowerWeylSubgroup i ν I'))

/-- Waldspurger's `W(M'|G|M) = W^{M'} \ {s ∈ W^G | sM ⊂ M'}`. -/
abbrev WeylIndex : Type u :=
  Quotient (weylIndexSetoid i ν I I')

/-- The quotient map on admissible Weyl elements. -/
def weylIndexMk (w : admissibleWeylElements i ν I I') : WeylIndex i ν I I' :=
  Quotient.mk _ w

/-- The equivalence relation has the orientation for a quotient by left multiplication. -/
theorem weylIndexMk_eq_iff (w v : admissibleWeylElements i ν I I') :
    weylIndexMk i ν I I' w = weylIndexMk i ν I I' v ↔
      v.val * w.val⁻¹ ∈ lowerWeylSubgroup i ν I' := by
  change Quotient.mk _ w = Quotient.mk _ v ↔ _
  rw [Quotient.eq]
  exact QuotientGroup.rightRel_apply

/-- An explicit representative system, retained as input to all later constructions. -/
structure Representatives where
  weyl : WeylIndex i ν I I' → admissibleWeylElements i ν I I'
  weyl_spec : ∀ s, weylIndexMk i ν I I' (weyl s) = s
  normalizer : WeylIndex i ν I I' → normalizerPoints i
  normalizer_spec : ∀ s,
    (QuotientGroup.mk (normalizer s) : relativeWeylGroup i) = (weyl s).val
  levi_le : ∀ s, conjugatedLevi i ν I (normalizer s) ≤ standardLevi i ν I'

/-- Existence of a representative system uses ordinary quotient and witness choice only. -/
def representatives : Representatives i ν I I' where
  weyl s := s.out
  weyl_spec s := Quotient.out_eq s
  normalizer s := (s.out.property).choose
  normalizer_spec s := (s.out.property).choose_spec.1
  levi_le s := (s.out.property).choose_spec.2

/-- Finiteness of the actual Weyl group gives a finite expansion index, including the empty case. -/
theorem finite_weylIndex (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) :
    Finite (WeylIndex i ν I I') := by
  letI := hG.finite_relativeWeylGroup i hi
  exact Quotient.finite _

/-- The actual lower ambient group is the standard Levi scheme `M_{I'}`. -/
abbrev lowerAmbient : GroupScheme (Spec (CommRingCat.of F)) :=
  Standard.leviScheme i ν I'

/-- The actual lower semistandard parabolic `M_{I'} ∩ nP_In⁻¹`. -/
def lowerParabolic (n : normalizerPoints i) : SubgroupFunctor (lowerAmbient i ν I') :=
  (conjugatedParabolic i ν I n).comap (Standard.leviHom i ν I')

/-- The actual lower inducing Levi, as a subgroup functor of the actual `M_{I'}`. -/
def lowerLevi (n : normalizerPoints i) : SubgroupFunctor (lowerAmbient i ν I') :=
  (conjugatedLevi i ν I n).comap (Standard.leviHom i ν I')

/-- The actual lower unipotent subgroup `M_{I'} ∩ nU_In⁻¹`. -/
def lowerUnipotent (n : normalizerPoints i) : SubgroupFunctor (lowerAmbient i ν I') :=
  (conjugatedUnipotent i ν I n).comap (Standard.leviHom i ν I')

/-- The lower inducing Levi is contained in the lower parabolic on every test scheme. -/
theorem lowerLevi_le_lowerParabolic (n : normalizerPoints i) :
    lowerLevi i ν I I' n ≤ lowerParabolic i ν I I' n := by
  intro X x hx
  exact standardLevi_le_standardParabolic i ν I X hx

/-- The lower unipotent subgroup lies in the lower parabolic on every test scheme. -/
theorem lowerUnipotent_le_lowerParabolic (n : normalizerPoints i) :
    lowerUnipotent i ν I I' n ≤ lowerParabolic i ν I I' n := by
  intro X x hx
  exact standardUnipotent_le_standardParabolic i ν I X hx

/-- The point formula fixes the conjugation direction of the inducing Levi. -/
theorem conjugatedLevi_points (n : normalizerPoints i) :
    (conjugatedLevi i ν I n).rationalPoints =
      (standardLeviPoints i ν I).map (MulAut.conj (n : rationalPoints G)).toMonoidHom :=
  SubgroupFunctor.rationalPoints_comap_innerIso_inv _ _

/-- The lower parabolic consists exactly of lower points whose ambient image belongs
to the forward conjugate of the original standard parabolic. -/
theorem lowerParabolic_points (n : normalizerPoints i) :
    (lowerParabolic i ν I I' n).rationalPoints =
      ((standardParabolicPoints i ν I).map
        (MulAut.conj (n : rationalPoints G)).toMonoidHom).comap
          (rationalPoints.map (Standard.leviHom i ν I')) := by
  rw [lowerParabolic, SubgroupFunctor.rationalPoints_comap, conjugatedParabolic,
    SubgroupFunctor.rationalPoints_comap_innerIso_inv]

/-- Changing the normalizer lift within one actual Weyl class leaves the conjugated
Levi functor unchanged. This is an imported standard-Levi conjugation result. -/
theorem conjugatedLevi_eq_of_weyl_eq (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν)
    (n m : normalizerPoints i)
    (hnm : (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk m) :
    conjugatedLevi i ν I n = conjugatedLevi i ν I m :=
  (standardLeviConjugation F G hG T i hi ν hν).2 I hI n m hnm

/-- Admissibility may be checked on any lift of a Weyl class. -/
theorem mem_admissibleWeylElements_iff (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν) (n : normalizerPoints i) :
    (QuotientGroup.mk n : relativeWeylGroup i) ∈ admissibleWeylElements i ν I I' ↔
      conjugatedLevi i ν I n ≤ standardLevi i ν I' := by
  constructor
  · rintro ⟨m, hmn, hm⟩
    rw [conjugatedLevi_eq_of_weyl_eq i ν I hG hi hν hI m n hmn] at hm
    exact hm
  · exact fun h => ⟨n, rfl, h⟩

/-- Lower inducing Levis also do not depend on the normalizer lift of a fixed Weyl class. -/
theorem lowerLevi_eq_of_weyl_eq (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν) (n m : normalizerPoints i)
    (hnm : (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk m) :
    lowerLevi i ν I I' n = lowerLevi i ν I I' m := by
  unfold lowerLevi
  rw [conjugatedLevi_eq_of_weyl_eq i ν I hG hi hν hI n m hnm]

end Langlands.HarishChandraSchwartz.WeakExpansion
