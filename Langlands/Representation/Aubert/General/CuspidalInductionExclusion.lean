import Langlands.Representation.Aubert.General.FirstAdjointnessConsequences
import Langlands.Representation.Aubert.General.SupportCategory
import Langlands.CategoryTheory.RenardCategoryDecomposition
import Langlands.Representation.CuspidalSupport.RationalCuspidalCategory

/-!
# Proper-induction exclusion from a supplied actual cuspidal splitting

The splitting is an explicit hypothesis. First adjointness eliminates its
cuspidal component; the actual coproduct then identifies the induction with
the component having no nonzero cuspidal subquotient.
-/

noncomputable section

open CategoryTheory Limits

namespace Langlands.Aubert.General

universe uK uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {κ : Type uK}
variable (P M U : κ → Subgroup G)
  (h : ∀ k, IsSemidirectDecomposition (P k) (M k) (U k))
  (hU : ∀ k, IsClosed (U k : Set G))

/-- An actual binary coproduct with a cuspidal component and a remainder
having no nonzero cuspidal subquotient. This is a local input condition;
it does not assert that such a splitting exists. The cuspidal component
itself is required to be cuspidal, without a condition on its subquotients. -/
def HasCuspidalRemainderSplitting (A : SmoothRep.{0, uG, uV} ℂ G) : Prop :=
  ∃ (Y : Bool → SmoothRep.{0, uG, uV} ℂ G) (j : ∀ b, Y b ⟶ A),
    IsCuspidalFor P M U h hU (Y true) ∧
      (∀ D : SmoothRep.{0, uG, uV} ℂ G,
        Nontrivial D → SmoothRep.IsSubquotient D (Y false) →
          ¬ IsCuspidalFor P M U h hU D) ∧
      Nonempty (IsColimit (Cofan.mk A j))

/-- If every map from a cuspidal object to the ambient object vanishes, an
actual cuspidal/remainder splitting excludes all nonzero cuspidal
subquotients of that ambient object. -/
theorem no_cuspidal_subquotient_of_splitting
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (hsplit : HasCuspidalRemainderSplitting P M U h hU A)
    (hHom : ∀ (C : SmoothRep.{0, uG, uV} ℂ G),
      IsCuspidalFor P M U h hU C → ∀ f : C ⟶ A, f = 0)
    (D : SmoothRep.{0, uG, uV} ℂ G) (hD : Nontrivial D)
    (hDA : SmoothRep.IsSubquotient D A) :
    ¬ IsCuspidalFor P M U h hU D := by
  obtain ⟨Y, j, hC, hR, ⟨hc⟩⟩ := hsplit
  have hj : j true = 0 := hHom (Y true) hC (j true)
  let f : ∀ b, Y b ⟶ Y false := fun b => match b with
    | false => 𝟙 (Y false)
    | true => 0
  let p : A ⟶ Y false := Cofan.IsColimit.desc hc f
  have hjp : j false ≫ p = 𝟙 (Y false) := by
    change (Cofan.mk A j).inj false ≫ Cofan.IsColimit.desc hc f = _
    exact Cofan.IsColimit.fac hc f false
  have hpj : p ≫ j false = 𝟙 A := by
    apply Cofan.IsColimit.hom_ext hc
    intro b
    change j b ≫ (p ≫ j false) = j b ≫ 𝟙 A
    rw [← Category.assoc]
    change ((Cofan.mk A j).inj b ≫ Cofan.IsColimit.desc hc f) ≫ j false = _
    rw [Cofan.IsColimit.fac]
    cases b <;> simp [f, hj]
  let e : A ≅ Y false := ⟨p, j false, hpj, hjp⟩
  exact hR D hD (hDA.of_iso_right e)

/-- Actual normalized induction along a member of the cuspidality family
has no nonzero cuspidal subquotient, provided its actual splitting is
supplied and the unipotent subgroup is unimodular. -/
theorem no_cuspidal_subquotient_of_induction_splitting
    (k : κ) (hδ : IsUnimodularModulus (U k) (hU k))
    (σ : SmoothRep.{0, uG, uV} ℂ (M k))
    (hsplit : HasCuspidalRemainderSplitting P M U h hU
      ((normalizedInductionFunctor (h k) (hU k)).obj σ))
    (D : SmoothRep.{0, uG, max uG uV} ℂ G) (hD : Nontrivial D)
    (hDA : SmoothRep.IsSubquotient D
      ((normalizedInductionFunctor (h k) (hU k)).obj σ)) :
    ¬ IsCuspidalFor P M U h hU D := by
  refine no_cuspidal_subquotient_of_splitting P M U h hU hsplit ?_ D hD hDA
  intro C hC f
  let := hC k
  have hz : FirstAdjointness.equiv (h k) (hU k) hδ C σ (SmoothRep.hom f) = 0 := by
    ext q
    rw [Subsingleton.elim q 0, map_zero, map_zero]
  have hf : SmoothRep.hom f = 0 := by
    apply (FirstAdjointness.equiv (h k) (hU k) hδ C σ).injective
    simpa using hz
  ext v
  exact congrArg (fun F => F v) hf

section Standard

variable {ι : Type uK} [Fintype ι]

/-- The supplied local splitting for the family of proper standard subsets.
It is a hypothesis, not a whole-category splitting theorem. -/
def HasStandardCuspidalRemainderSplitting
    (P M U : Finset ι → Subgroup G)
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    (A : SmoothRep.{0, uG, uV} ℂ G) : Prop :=
  HasCuspidalRemainderSplitting
    (fun I : {I : Finset ι // I ≠ Finset.univ} => P I)
    (fun I => M I) (fun I => U I) (fun I => h I) (fun I => hU I) A

/-- Proper standard induction excludes every nonzero cuspidal subquotient
when its actual local splitting is supplied. -/
theorem no_cuspidal_subquotient_of_proper_induction_splitting
    (P M U : Finset ι → Subgroup G)
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    (I : Finset ι) (hI : I ≠ Finset.univ)
    (hδ : IsUnimodularModulus (U I) (hU I))
    (σ : SmoothRep.{0, uG, uV} ℂ (M I))
    (hsplit : HasStandardCuspidalRemainderSplitting P M U h hU
      ((normalizedInductionFunctor (h I) (hU I)).obj σ))
    (D : SmoothRep.{0, uG, max uG uV} ℂ G) (hD : Nontrivial D)
    (hDA : SmoothRep.IsSubquotient D
      ((normalizedInductionFunctor (h I) (hU I)).obj σ)) :
    ¬ IsCuspidal P M U h hU D :=
  no_cuspidal_subquotient_of_induction_splitting
    (fun I : {I : Finset ι // I ≠ Finset.univ} => P I)
    (fun I => M I) (fun I => U I) (fun I => h I) (fun I => hU I)
    ⟨I, hI⟩ hδ σ hsplit D hD hDA

end Standard

/-- The same exclusion inside an actual standard Levi, with precisely its
proper inside-Levi Jacquet family and its actual induction functor. -/
theorem no_leviCuspidal_subquotient_of_proper_induction_splitting
    {ι : Type uK} (P M U : Finset ι → Subgroup G)
    (hU : ∀ I, IsClosed (U I : Set G))
    (J : Finset ι) (hM : IsClosed (M J : Set G))
    (hJ : ∀ K : Finset J,
      IsSemidirectDecomposition ((P (leviIndex J K)).subgroupOf (M J))
        ((M (leviIndex J K)).subgroupOf (M J))
        ((U (leviIndex J K)).subgroupOf (M J))) :
    letI := hM.locallyCompactSpace
    ∀ (K : Finset J) (_hK : K ≠ Finset.univ)
      (_hδ : IsUnimodularModulus ((U (leviIndex J K)).subgroupOf (M J))
        ((hU (leviIndex J K)).preimage continuous_subtype_val))
      (σ : SmoothRep.{0, uG, uV} ℂ ((M (leviIndex J K)).subgroupOf (M J)))
      (_hsplit : HasStandardCuspidalRemainderSplitting
        (fun L : Finset J => (P (leviIndex J L)).subgroupOf (M J))
        (fun L => (M (leviIndex J L)).subgroupOf (M J))
        (fun L => (U (leviIndex J L)).subgroupOf (M J)) hJ
        (fun L => (hU (leviIndex J L)).preimage continuous_subtype_val)
        ((normalizedInductionFunctor (hJ K)
          ((hU (leviIndex J K)).preimage continuous_subtype_val)).obj σ))
      (D : SmoothRep.{0, uG, max uG uV} ℂ (M J)) (_hD : Nontrivial D),
      SmoothRep.IsSubquotient D
        ((normalizedInductionFunctor (hJ K)
          ((hU (leviIndex J K)).preimage continuous_subtype_val)).obj σ) →
      ¬ IsLeviCuspidal P M U hU J hM hJ D := by
  let := hM.locallyCompactSpace
  intro K hK hδ σ hsplit D hD hDA
  exact no_cuspidal_subquotient_of_proper_induction_splitting
    (fun L : Finset J => (P (leviIndex J L)).subgroupOf (M J))
    (fun L => (M (leviIndex J L)).subgroupOf (M J))
    (fun L => (U (leviIndex J L)).subgroupOf (M J)) hJ
    (fun L => (hU (leviIndex J L)).preimage continuous_subtype_val)
    K hK hδ σ hsplit D hD hDA

end Langlands.Aubert.General

namespace Langlands.CuspidalSupport

open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

local instance cuspidalInductionExclusionRationalPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

variable [LocallyCompactSpace (GroupScheme.rationalPoints G)]
  [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (h : ∀ I, IsSemidirectDecomposition
    (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G)))

/-- The exact published rational whole-category coproduct condition supplies
the weaker local splitting input. This implication does not prove the
whole-category condition. -/
theorem hasStandardCuspidalRemainderSplitting_of_rationalWholeCoproduct
    (hwhole : Renard.EveryObjectIsCoproductOfComponents
      (rationalWholeCuspidalDecompositionProperties.{uF, uV} G i ν h hU))
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    HasStandardCuspidalRemainderSplitting
      (parabolic i ν) (levi i ν) (unipotent i ν) h hU A := by
  obtain ⟨Y, j, hY, hc⟩ := hwhole A
  refine ⟨Y, j, ?_, ?_, hc⟩
  · exact hY true (Y true) (SmoothRep.isSubquotient_iff_exists.mpr
      ⟨Y true, 𝟙 _, 𝟙 _, Function.injective_id, Function.surjective_id⟩)
  · exact hY false

/-- Conditional rational proper-induction exclusion using exactly the
published whole-category decomposition as the missing splitting input. -/
theorem rationalNoCuspidalSubquotientProperty_of_properInduction_decomposition
    (hwhole : IsRationalWholeCuspidalCategoryDecomposition.{uF, max uF uV}
      G i ν h hU)
    (I : Finset (SimpleRoot i ν)) (hI : I ≠ Finset.univ)
    (hδ : IsUnimodularModulus (unipotent i ν I) (hU I))
    (σ : SmoothRep.{0, uF, uV} ℂ (levi i ν I)) :
    rationalNoCuspidalSubquotientProperty G i ν h hU
      ((normalizedInductionFunctor (h I) (hU I)).obj σ) := by
  intro D hD hDA
  exact no_cuspidal_subquotient_of_proper_induction_splitting
    (parabolic i ν) (levi i ν) (unipotent i ν) h hU I hI hδ σ
    (hasStandardCuspidalRemainderSplitting_of_rationalWholeCoproduct
      G i ν h hU hwhole.1 _) D hD hDA

end Langlands.CuspidalSupport
