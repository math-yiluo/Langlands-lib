import Langlands.Representation.Aubert.General.RationalSharpConsequenceTargets
import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets

/-! # Sharp support retention from induction--Jacquet stability

The actual terminal cokernel `E#` is a quotient of the degree-`|S| - |I|` object
of the standard complex, which is jointly embedded in the finitely many
`i_{S \ s} r_{S \ s}(E)`. Stability of `Alg({I})` under every such composite
therefore gives `E# ∈ Alg({I})`. No proof of that stability is imported; it is a
hypothesis of both reductions below. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.SmoothRep

universe uR uG uV uJ

variable {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- A subsingleton smooth representation has no irreducible subquotient. -/
theorem not_isSubquotient_of_subsingleton {C D : SmoothRep.{uR, uG, uV} R G}
    [Subsingleton C] (hD : D.IsIrreducible) : ¬ IsSubquotient D C := by
  intro h
  obtain ⟨B, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  have hB (b : B) : b = 0 := hi (Subsingleton.elim (hom i b) (hom i 0))
  have hDz (d : D) : d = 0 := by
    obtain ⟨b, rfl⟩ := hq d
    rw [hB b, map_zero]
  have := hD
  apply (bot_ne_top : (⊥ : Subrepresentation D.representation) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext d
  rw [hDz d]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

/-- An irreducible subquotient of `X` occurs in one of the targets of a finite
jointly injective family of intertwiners out of `X`. -/
theorem exists_isSubquotient_of_jointlyInjective {J : Type uJ} [Finite J]
    {X D : SmoothRep.{uR, uG, uV} R G} {T : J → SmoothRep.{uR, uG, uV} R G}
    (p : ∀ j, X ⟶ T j) (hp : ∀ x : X, (∀ j, hom (p j) x = 0) → x = 0)
    (hD : D.IsIrreducible) (h : IsSubquotient D X) :
    ∃ j, IsSubquotient D (T j) := by
  classical
  have key : ∀ (F : Finset J) (C : SmoothRep.{uR, uG, uV} R G) (i : C ⟶ X),
      Function.Injective (hom i) → (∀ j, j ∉ F → ∀ c, hom (p j) (hom i c) = 0) →
        IsSubquotient D C → ∃ j, IsSubquotient D (T j) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro C i hi hzero hC
      have : Subsingleton C := ⟨fun a b => hi (by
        rw [hp (hom i a) (fun j => hzero j (Finset.notMem_empty j) a),
          hp (hom i b) (fun j => hzero j (Finset.notMem_empty j) b)])⟩
      exact absurd hC (not_isSubquotient_of_subsingleton hD)
    | insert a F ha ih =>
      intro C i hi hzero hC
      rcases irreducibleSubquotient_kernel_or_image hD hC (i ≫ p a) with hk | hm
      · refine ih (kernel (i ≫ p a)) (kernelι (i ≫ p a) ≫ i) ?_ ?_ hk
        · rw [hom_comp]
          exact hi.comp (subtype_injective _ _)
        · intro j hj c
          by_cases hja : j = a
          · subst hja
            exact c.property
          · exact hzero j (by simp [hja, hj]) _
      · exact ⟨a, smoothSubquotientTransitivity R G (T a) (image (i ≫ p a)) D hm
          (subrepresentation_isSubrepresentation _).isSubquotient⟩
  have := Fintype.ofFinite J
  exact key Finset.univ X (𝟙 X) (fun _ _ hxy => hxy)
    (fun j hj => absurd (Finset.mem_univ j) hj) h

end Langlands.SmoothRep

namespace Langlands.Aubert.General

universe uI uG uV uJ

section Generic

variable {ι : Type uI}
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}
  {IsAssociate : Finset ι → Finset ι → G → Prop} {I : Finset ι}
  {hM : IsClosed (M I : Set G)}
  {hI : ∀ K : Finset I, IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
    ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}

/-- `Alg({I})` contains every representation carried by a finite jointly
injective family of intertwiners into members of `Alg({I})`. -/
theorem IsInSupportCategory.of_jointlyInjective {J : Type uJ} [Finite J]
    {X : SmoothRep.{0, uG, max uG uV} ℂ G} {T : J → SmoothRep.{0, uG, max uG uV} ℂ G}
    (p : ∀ j, X ⟶ T j) (hp : ∀ x : X, (∀ j, SmoothRep.hom (p j) x = 0) → x = 0)
    (hT : ∀ j, IsInSupportCategory P M U h hU IsAssociate I hM hI (T j)) :
    IsInSupportCategory P M U h hU IsAssociate I hM hI X := by
  intro π hπ hπX
  obtain ⟨j, hj⟩ := SmoothRep.exists_isSubquotient_of_jointlyInjective p hp hπ hπX
  exact hT j π hπ hj

/-- `Alg({I})` contains every actual quotient of one of its members. -/
theorem IsInSupportCategory.of_isQuotient {E F : SmoothRep.{0, uG, max uG uV} ℂ G}
    (hE : IsInSupportCategory P M U h hU IsAssociate I hM hI E)
    (hFE : SmoothRep.IsQuotient F E) :
    IsInSupportCategory P M U h hU IsAssociate I hM hI F :=
  hE.of_isSubquotient hFE.isSubquotient

end Generic

section Complex

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

/-- The coordinate projection from the actual homogeneous object of the standard
complex onto its factor `i_{S \ s} r_{S \ s}(A)`. -/
def StandardComplex.degreeProjection (A : SmoothRep.{0, uG, max uI uG uV} ℂ G) (k : ℕ)
    (s : {s : Finset ι // s.card = k}) :
    StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed A k ⟶
      (inductionJacquetFunctor.{uG, max uI uV} (h (Finset.univ \ s.1))
        (hclosed (Finset.univ \ s.1))).obj A :=
  SmoothRep.ofHom
    { toLinearMap := LinearMap.proj s
      isIntertwining' := fun _ => rfl }

/-- The coordinate projections of a homogeneous object are jointly injective. -/
theorem StandardComplex.degreeProjection_jointlyInjective
    (A : SmoothRep.{0, uG, max uI uG uV} ℂ G) (k : ℕ)
    (x : StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed A k)
    (hx : ∀ s, SmoothRep.hom (StandardComplex.degreeProjection P M U h hclosed A k s) x = 0) :
    x = 0 :=
  funext hx

/-- Generic retention: stability of `Alg({I})` under every actual
induction--Jacquet composite gives `E# ∈ Alg({I})` for every `E ∈ Alg({I})`. -/
theorem sharpSupportRetention_of_supportCategoryInductionJacquet
    (hIJ : SupportCategoryInductionJacquetTarget.{uI, uG, max uI uV}
      P M U h hclosed hM hL IsAssociate) :
    SharpSupportRetentionTarget.{uI, uG, uV} P M U h hclosed hδ hP hU hM hL IsAssociate := by
  intro I E hE
  have hdeg : IsInSupportCategory.{uI, uG, max uI uV} P M U h hclosed IsAssociate I (hM I)
      (hL I) (StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed E
        (Complex.terminalDegree I)) :=
    IsInSupportCategory.of_jointlyInjective
      (StandardComplex.degreeProjection P M U h hclosed E (Complex.terminalDegree I))
      (StandardComplex.degreeProjection_jointlyInjective P M U h hclosed E
        (Complex.terminalDegree I))
      (fun s => hIJ I (Finset.univ \ s.1) E hE)
  exact hdeg.of_isQuotient
    ⟨SmoothRep.ofHom (StandardComplex.terminalProjection.{uI, uG, max uI uV}
        P M U h hclosed hδ hP hU E (Complex.terminalDegree I)),
      Complex.terminalProjection_surjective _ _ _ _ _ _ _ _ E _⟩

end Complex

end Langlands.Aubert.General

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

universe u v

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Rational retention, conditional on the actual induction--Jacquet stability
statement for the literal standard rational-point families. -/
theorem rationalSharpSupportRetention_of_inductionJacquet
    (hIJ : RationalSupportCategoryInductionJacquetStatement.{u, v}) :
    RationalSharpSupportRetentionStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _
  exact sharpSupportRetention_of_supportCategoryInductionJacquet.{u, u, max (u + 1) v} _ _ _ _ _
    _ _ _ _ _ _ (hIJ k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)

end Langlands.Aubert.General.RationalPointFamily
