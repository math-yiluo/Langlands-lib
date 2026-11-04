import Langlands.Representation.Aubert.General.RationalTerminalJacquet

/-! # The fixed-Levi terminal-cokernel comparison on the actual rational points

At the full Levi support the retained terminal degree is zero, where no
incoming boundary is divided out. The actual initial map and the canonical
quotient projection then give a natural isomorphism with the identity functor
on all smooth representations of the Levi.
-/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General

open CategoryTheory

universe u v uI uG uV

section Endpoints

variable {G : Type uG} [Group G] {P M U : Subgroup G}

/-- A semidirect decomposition with full Levi factor has full parabolic. -/
theorem IsSemidirectDecomposition.parabolic_eq_top_of_levi_eq_top
    (h : IsSemidirectDecomposition P M U) (hM : M = ⊤) : P = ⊤ := by
  rw [← top_le_iff, ← hM]
  exact h.levi_le

/-- A semidirect decomposition with full Levi factor has trivial radical. -/
theorem IsSemidirectDecomposition.unipotent_eq_bot_of_levi_eq_top
    (h : IsSemidirectDecomposition P M U) (hM : M = ⊤) : U = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  have huP : u ∈ P := h.unipotent_le hu
  have huM : u ∈ M := by
    rw [hM]
    exact Subgroup.mem_top u
  have h1 : (⟨u, huP⟩ : P) = 1 :=
    Subgroup.disjoint_def.mp h.isComplement'.disjoint
      (Subgroup.mem_subgroupOf.mpr huM) (Subgroup.mem_subgroupOf.mpr hu)
  exact congrArg Subtype.val h1

end Endpoints

namespace Complex

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (h : ∀ s, IsSemidirectDecomposition (P s) (M s) (U s))
variable (hclosed : ∀ s, IsClosed (U s : Set G))
variable (hδ : ∀ s, IsUnimodularModulus (U s) (hclosed s))
variable (hP : Antitone P) (hU : Monotone U)
variable {A B : SmoothRep.{0, uG, max uG uV} ℂ G}

/-- The actual initial map followed by the canonical degree-zero terminal projection. -/
def initialTerminalMap (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    A.representation.IntertwiningMap (terminalRepresentation P M U h hclosed hδ hP hU A 0) :=
  (terminalProjection P M U h hclosed hδ hP hU A 0).comp (initialMap P M U h hclosed hδ A)

/-- In degree zero the incoming boundary is zero, so the projection is injective. -/
theorem terminalProjection_zero_injective (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    Function.Injective (terminalProjection P M U h hclosed hδ hP hU A 0) := by
  intro x y hxy
  have hmem : x - y ∈ boundary P M U h hclosed hδ hP hU A 0 :=
    (Submodule.Quotient.eq (boundary P M U h hclosed hδ hP hU A 0)).mp hxy
  change x - y ∈ (⊥ : Submodule ℂ _) at hmem
  exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp hmem)

/-- With full parabolic and trivial radical at the empty removed set, the degree-zero
comparison is bijective. -/
theorem initialTerminalMap_bijective (hP0 : P ∅ = ⊤) (hU0 : U ∅ = ⊥)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    Function.Bijective (initialTerminalMap P M U h hclosed hδ hP hU A) := by
  have hinit : Function.Bijective (initialMap P M U h hclosed hδ A) :=
    (initialEquiv P M U h hclosed hδ hP0 hU0 A).toLinearEquiv.bijective
  have hproj : Function.Bijective (terminalProjection P M U h hclosed hδ hP hU A 0) :=
    ⟨terminalProjection_zero_injective P M U h hclosed hδ hP hU A,
      terminalProjection_surjective P M U h hclosed hδ hP hU A 0⟩
  exact hproj.comp hinit

/-- The degree-zero comparison commutes with every equivariant map. -/
theorem initialTerminalMap_natural (φ : A ⟶ B) :
    (initialTerminalMap P M U h hclosed hδ hP hU B).comp (SmoothRep.hom φ) =
      (terminalMap P M U h hclosed hδ hP hU φ 0).comp
        (initialTerminalMap P M U h hclosed hδ hP hU A) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have h1 := LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap
    (initialMap_natural P M U h hclosed hδ hP hU φ)) v
  have h2 := LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap
    (terminalMap_comp_projection P M U h hclosed hδ hP hU φ 0))
    (initialMap P M U h hclosed hδ A v)
  change terminalProjection P M U h hclosed hδ hP hU B 0
      (initialMap P M U h hclosed hδ B (SmoothRep.hom φ v)) =
    terminalMap P M U h hclosed hδ hP hU φ 0
      (terminalProjection P M U h hclosed hδ hP hU A 0 (initialMap P M U h hclosed hδ A v))
  change terminalMap P M U h hclosed hδ hP hU φ 0
      (terminalProjection P M U h hclosed hδ hP hU A 0 (initialMap P M U h hclosed hδ A v)) =
    terminalProjection P M U h hclosed hδ hP hU B 0
      (degreeMap P M U h hclosed hδ hP hU φ 0 (initialMap P M U h hclosed hδ A v)) at h2
  change degreeMap P M U h hclosed hδ hP hU φ 0 (initialMap P M U h hclosed hδ A v) =
    initialMap P M U h hclosed hδ B (SmoothRep.hom φ v) at h1
  rw [h2, h1]

/-- At degree zero the actual terminal functor is naturally isomorphic to the
identity functor on the full smooth category. -/
def terminalZeroIso (hP0 : P ∅ = ⊤) (hU0 : U ∅ = ⊥) :
    terminalFunctor.{uI, uG, max uI uV} P M U h hclosed hδ hP hU 0 ≅
      𝟭 (SmoothRep.{0, uG, max uI uG uV} ℂ G) :=
  (NatIso.ofComponents
    (fun A => SmoothRep.mkIso
      ((initialTerminalMap.{uI, uG, max uI uV} P M U h hclosed hδ hP hU A).ofBijective
        (initialTerminalMap_bijective P M U h hclosed hδ hP hU hP0 hU0 A)))
    (fun {A B} φ => by
      apply (SmoothRep.toRep).map_injective
      apply Rep.hom_ext
      exact initialTerminalMap_natural P M U h hclosed hδ hP hU φ)).symm

/-- The terminal functor at any degree equal to zero is naturally isomorphic to
the identity functor. -/
def terminalIsoOfDegreeEqZero (hP0 : P ∅ = ⊤) (hU0 : U ∅ = ⊥) (k : ℕ) (hk : k = 0) :
    terminalFunctor.{uI, uG, max uI uV} P M U h hclosed hδ hP hU k ≅
      𝟭 (SmoothRep.{0, uG, max uI uG uV} ℂ G) :=
  eqToIso (congrArg (terminalFunctor.{uI, uG, max uI uV} P M U h hclosed hδ hP hU) hk) ≪≫
    terminalZeroIso P M U h hclosed hδ hP hU hP0 hU0

end Complex

namespace LeviComplex

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (hclosed : ∀ K, IsClosed (U K : Set G))
variable (hP : Monotone P) (hU : Antitone U)
variable (J : Finset ι) (hM : IsClosed (M J : Set G))
variable (hJ : ∀ K : Finset J,
  IsSemidirectDecomposition (family (M J) P J K)
    (family (M J) M J K) (family (M J) U J K))
variable (hJδ : letI := hM.locallyCompactSpace
  ∀ K : Finset J, IsUnimodularModulus (family (M J) U J K)
    ((hclosed (leviIndex J K)).preimage continuous_subtype_val))

omit [LinearOrder ι] [Fintype ι] in
/-- The full index finset of `J`, read in the ambient root set, is `J`. -/
theorem leviIndex_univ : leviIndex J (Finset.univ : Finset J) = J := by
  rw [Finset.univ_eq_attach]
  exact Finset.attach_map_val

omit [LinearOrder ι] [Fintype ι] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] in
/-- At the full index finset of `J` the restricted Levi is all of `M J`. -/
theorem family_levi_univ : family (M J) M J Finset.univ = ⊤ := by
  change (M (leviIndex J Finset.univ)).subgroupOf (M J) = ⊤
  rw [leviIndex_univ]
  exact Subgroup.subgroupOf_self _

omit [LinearOrder ι] [Fintype ι] in
/-- The terminal degree of the full Levi support is zero. -/
theorem terminalDegree_univ : Complex.terminalDegree (Finset.univ : Finset J) = 0 := by
  unfold Complex.terminalDegree
  rw [Finset.card_univ, Nat.sub_self]

/-- The actual Levi terminal cokernel at full support is naturally isomorphic
to the identity functor on all smooth representations of `M J`. -/
def sharpFunctorUnivIso :
    sharpFunctor P M U hclosed hP hU J hM hJ hJδ Finset.univ ≅
      𝟭 (SmoothRep.{0, uG, max uI uG uV} ℂ (M J)) := by
  letI := hM.locallyCompactSpace
  have hP0 : StandardComplex.removedFamily (family (M J) P J) ∅ = ⊤ := by
    change family (M J) P J (Finset.univ \ ∅) = ⊤
    rw [Finset.sdiff_empty]
    exact (hJ Finset.univ).parabolic_eq_top_of_levi_eq_top (family_levi_univ M J)
  have hU0 : StandardComplex.removedFamily (family (M J) U J) ∅ = ⊥ := by
    change family (M J) U J (Finset.univ \ ∅) = ⊥
    rw [Finset.sdiff_empty]
    exact (hJ Finset.univ).unipotent_eq_bot_of_levi_eq_top (family_levi_univ M J)
  exact Complex.terminalIsoOfDegreeEqZero.{uI, uG, max uI uV}
    (StandardComplex.removedFamily (family (M J) P J))
    (StandardComplex.removedFamily (family (M J) M J))
    (StandardComplex.removedFamily (family (M J) U J))
    (fun s => hJ (Finset.univ \ s))
    (fun s => (hclosed (leviIndex J (Finset.univ \ s))).preimage continuous_subtype_val)
    (fun s => hJδ (Finset.univ \ s))
    (StandardComplex.removedFamily_antitone (family_monotone (M J) hP J))
    (StandardComplex.removedFamily_monotone (family_antitone (M J) hU J))
    hP0 hU0 _ (terminalDegree_univ J)

end LeviComplex

namespace TerminalJacquet

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
variable (hclosed : ∀ J, IsClosed (U J : Set G))
variable (hP : Monotone P) (hU : Antitone U)
variable (IsAssociate : Finset ι → Finset ι → G → Prop)
variable (hM : ∀ J, IsClosed (M J : Set G))
variable (hLevi : ∀ (J : Finset ι) (K : Finset J),
  IsSemidirectDecomposition ((P (leviIndex J K)).subgroupOf (M J))
    ((M (leviIndex J K)).subgroupOf (M J))
    ((U (leviIndex J K)).subgroupOf (M J)))
variable (hLeviδ : ∀ J, letI := (hM J).locallyCompactSpace
  ∀ K : Finset J, IsUnimodularModulus ((U (leviIndex J K)).subgroupOf (M J))
    ((hclosed (leviIndex J K)).preimage continuous_subtype_val))

omit [Fintype ι] in
/-- The fixed-Levi comparison holds for every generic standard family: the
full-support Levi cokernel is naturally the identity, whiskered by the
support-category inclusion and the actual Jacquet functor. -/
theorem fixedLeviComparison :
    FixedLeviComparisonStatement.{uI, uG, uV}
      P M U h hclosed hP hU IsAssociate hM hLevi hLeviδ := by
  intro I C
  exact ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (C.ι ⋙ jacquetFunctor (h I) (hclosed I))
      (LeviComplex.sharpFunctorUnivIso.{uI, uG, uV} P M U hclosed hP hU I (hM I)
        (hLevi I) (hLeviδ I)) ≪≫
    Functor.rightUnitor _⟩

end TerminalJacquet

namespace RationalPointFamily

open _root_.AlgebraicGeometry GroupScheme
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

/-- The fixed-Levi equality before (**) on p.4690 of Aubert's erratum, as a
natural isomorphism on the full actual support category. -/
theorem rationalFixedLeviComparison :
    RationalFixedLeviComparisonStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUcLevi _
  exact TerminalJacquet.fixedLeviComparison (parabolic i ν) (levi i ν) (unipotent i ν)
    _ hU _ _ _ hM _ _

end RationalPointFamily

end Langlands.Aubert.General
