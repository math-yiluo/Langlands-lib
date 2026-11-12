import Langlands.Representation.Intertwining.PQFilteredKernels
import Langlands.Representation.Intertwining.PQFiniteActionRegularity
import Langlands.Representation.Exponents.ArbitraryParabolicInduction
import Langlands.Representation.Category.NaturalCokernel
import Langlands.Representation.Filtration.QuotientTail

/-! # The actual PQ regularity quotient and its filtered kernel criterion -/

noncomputable section

open CategoryTheory

namespace Langlands

private theorem intertwiner_map_groupAlgebra
    {H B V W : Type*} [Monoid H] [Monoid B]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {τ : Representation ℂ H W}
    (f : ρ.IntertwiningMap τ) (φ : B →* H) (c : MonoidAlgebra ℂ B) (v : V) :
    f (Representation.asAlgebraHom (ρ.comp φ) c v) =
      Representation.asAlgebraHom (τ.comp φ) c (f v) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single b z =>
    simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
    exact congrArg (fun y => z • y)
      (Representation.IntertwiningMap.isIntertwining ρ τ f (φ b) v)

private theorem groupAlgebraKernel_le_of_surjective
    {H B V W : Type*} [Monoid H] [Monoid B]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {τ : Representation ℂ H W}
    (f : ρ.IntertwiningMap τ) (hf : Function.Surjective f) (φ : B →* H) :
    groupAlgebraKernel ρ φ ≤ groupAlgebraKernel τ φ := by
  intro c hc
  apply (mem_groupAlgebraKernel_iff _ φ c).mpr
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := hf w
  exact (intertwiner_map_groupAlgebra f φ c v).symm.trans (by
    rw [(mem_groupAlgebraKernel_iff _ φ c).mp hc]
    exact map_zero f)

/-- An equivariant equivalence preserves the kernel of the same group-algebra action. -/
theorem groupAlgebraKernel_eq_of_equiv
    {H B V W : Type*} [Monoid H] [Monoid B]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {τ : Representation ℂ H W}
    (e : ρ.Equiv τ) (φ : B →* H) :
    groupAlgebraKernel ρ φ = groupAlgebraKernel τ φ :=
  le_antisymm (groupAlgebraKernel_le_of_surjective e.toIntertwiningMap e.surjective φ)
    (groupAlgebraKernel_le_of_surjective e.symm.toIntertwiningMap e.symm.surjective φ)

namespace PQFilteredKernels

variable {H B : Type*} [Group H] [CommGroup B]
  {C : Type*} [Category C] {F : C ⥤ Rep ℂ H}
  {n : ℕ} (s : RepFunctorFiltration F n) (X : C) (φ : B →* H)
  (pieces : Fin n → C ⥤ Rep ℂ H)
  (e : ∀ i, s.graded i ≅ pieces i)

include e

/-- Natural grade identifications identify the intersection of actual action kernels. -/
theorem gradedKernel_eq_pieceKernels :
    gradedKernel s X φ =
      ⨅ i, groupAlgebraKernel ((pieces i).obj X).ρ φ := by
  apply iInf_congr
  intro i
  exact groupAlgebraKernel_eq_of_equiv (Representation.equivOfIso ((e i).app X)) φ

/-- Comaximality for the ambient action can be read on supplied models of all grades. -/
theorem sup_kernel_eq_top_iff_pieceKernels (I : Ideal (MonoidAlgebra ℂ B)) :
    I ⊔ groupAlgebraKernel (F.obj X).ρ φ = ⊤ ↔
      I ⊔ (⨅ i, groupAlgebraKernel ((pieces i).obj X).ρ φ) = ⊤ := by
  rw [sup_kernel_eq_top_iff s X φ, gradedKernel_eq_pieceKernels s X φ pieces e]

end PQFilteredKernels

end Langlands

universe u v

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance regularityFiltrationAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))

/-- The actual ambient quotient by the boundary-support image at the identity.
Its object at `σ` is the representation used in `pqRegularityKernel`. -/
def pqRegularityQuotientFunctor :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤
      Rep.{max u v} ℂ (rationalPoints M) := by
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  let F := leviInductionFunctor.{u, v} p l r hp hr hl hmul ⋙
    leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ
  let S : RepSubfunctor (F ⋙ SmoothRep.toRep) :=
    boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      (identityParabolicDoubleCoset p q)
  exact S.ambientQuotient ⋙ SmoothRep.toRep

/-- The same-vector-class natural projection onto the actual regularity quotient. -/
def pqRegularityProjection :
    letI := leviPointTopology l hl
    leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ ⟶
      pqRegularityQuotientFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ := by
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  let F := leviInductionFunctor.{u, v} p l r hp hr hl hmul ⋙
    leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ
  let S : RepSubfunctor (F ⋙ SmoothRep.toRep) :=
    boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      (identityParabolicDoubleCoset p q)
  exact Functor.whiskerRight S.ambientProjection SmoothRep.toRep

theorem pqRegularityProjection_mem_kernel
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (x : (leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj σ) :
    x ∈ (boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).obj σ ↔
      ((pqRegularityProjection p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).app σ).hom x = 0 :=
  (Submodule.Quotient.mk_eq_zero _).symm

theorem pqRegularityProjection_surjective
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    Function.Surjective
      ((pqRegularityProjection p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).app σ).hom :=
  Submodule.mkQ_surjective _

/-- If the boundary image is a step of the canonical support flag, its surviving
tail filters the actual quotient in the definition of PQ regularity. -/
def pqRegularitySupportFiltration {a b : ℕ}
    (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) (a + b))
    (hboundary : letI := leviPointTopology l hl
      ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        ((leviJacquetSupportFiltration p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ s).step
          (RepFunctorFiltration.tailIndex a b 0)).obj σ =
          (boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
            (identityParabolicDoubleCoset p q)).obj σ) :
    letI := leviPointTopology l hl
    RepFunctorFiltration
      (pqRegularityQuotientFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ) b := by
  letI := leviPointTopology l hl
  exact (leviJacquetSupportFiltration p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ s).quotientTail
    (pqRegularityProjection p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)
    (fun σ x => by
      rw [hboundary σ]
      exact pqRegularityProjection_mem_kernel p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ σ x)
    (pqRegularityProjection_surjective p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)

/-- Every surviving actual support grade retains its original natural model. -/
def pqRegularitySupportGradedIso {a b : ℕ}
    (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) (a + b))
    (hboundary : letI := leviPointTopology l hl
      ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        ((leviJacquetSupportFiltration p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ s).step
          (RepFunctorFiltration.tailIndex a b 0)).obj σ =
          (boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
            (identityParabolicDoubleCoset p q)).obj σ)
    (i : Fin b) :
    letI := leviPointTopology l hl
    (leviJacquetSupportFiltration.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ s).graded
        ⟨a + i.val, by omega⟩ ≅
      (pqRegularitySupportFiltration p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        s hboundary).graded i := by
  letI := leviPointTopology l hl
  exact (leviJacquetSupportFiltration p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ s).quotientTailGradedIso
    (pqRegularityProjection p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)
    (fun σ x => by
      rw [hboundary σ]
      exact pqRegularityProjection_mem_kernel p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ σ x)
    (pqRegularityProjection_surjective p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ) i

variable {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M)
  {n : ℕ}
  (s : letI := leviPointTopology l hl
    RepFunctorFiltration
      (pqRegularityQuotientFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ) n)
  (pieces : letI := leviPointTopology l hl
    Fin n → SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤ Rep.{max u v} ℂ (rationalPoints M))
  (e : ∀ i, s.graded i ≅ pieces i)
  (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))

include s e

/-- The actual regularity condition is equivalent to comaximality against the
intersection of kernels on all supplied natural models of the quotient grades. -/
theorem pqRegularity_iff_pieceKernels :
    IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ ↔
      splitComponentKernel l hl a σ ⊔
        (⨅ i, groupAlgebraKernel ((pieces i).obj σ).ρ (rationalPoints.map a)) = ⊤ := by
  exact PQFilteredKernels.sup_kernel_eq_top_iff_pieceKernels
    s σ (rationalPoints.map a) pieces e (splitComponentKernel l hl a σ)

/-- A finite intersection in the criterion can equivalently be tested one piece at a time. -/
theorem pqRegularity_iff_all_pieceKernels :
    IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ ↔
      ∀ i, splitComponentKernel l hl a σ ⊔
        groupAlgebraKernel ((pieces i).obj σ).ρ (rationalPoints.map a) = ⊤ := by
  rw [pqRegularity_iff_pieceKernels p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a s pieces e σ]
  constructor
  · intro h i
    exact top_unique (h ▸ sup_le_sup_left (iInf_le _ i) _)
  · intro h
    simpa only [Finset.mem_univ, iInf_pos] using
      (Ideal.sup_iInf_eq_top (s := Finset.univ)
        (I := splitComponentKernel l hl a σ)
        (J := fun i => groupAlgebraKernel ((pieces i).obj σ).ρ (rationalPoints.map a))
        (fun i _ => h i))

/-- PQ regularity forces disjoint algebraic generalized-character sets on every
model of a grade of the actual quotient. No finiteness of the action algebra is used. -/
theorem pqRegularity_disjoint_generalizedCharacters
    (h : IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ) :
    ∀ i, Disjoint
      {χ | IsGeneralizedEigencharacter (σ.obj.ρ.comp (rationalPoints.map a)) χ}
      {χ | IsGeneralizedEigencharacter (((pieces i).obj σ).ρ.comp (rationalPoints.map a)) χ} := by
  intro i
  exact PQKernelCharacters.disjoint_generalizedCharacters _ _
    ((pqRegularity_iff_all_pieceKernels p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      a s pieces e σ).mp h i)

/-- The converse spectral implication holds when the actual actions of the
split group have finite-dimensional action quotients. -/
theorem pqRegularity_of_disjoint_generalizedCharacters
    [Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (σ.obj.ρ.comp (rationalPoints.map a)))]
    [∀ i, Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (((pieces i).obj σ).ρ.comp (rationalPoints.map a)))]
    (h : ∀ i, Disjoint
      {χ | IsGeneralizedEigencharacter (σ.obj.ρ.comp (rationalPoints.map a)) χ}
      {χ | IsGeneralizedEigencharacter (((pieces i).obj σ).ρ.comp (rationalPoints.map a)) χ}) :
    IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ := by
  apply (pqRegularity_iff_all_pieceKernels p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    a s pieces e σ).mpr
  intro i
  exact (PQFiniteActionRegularity.sup_kernels_eq_top_iff
    (σ.obj.ρ.comp (rationalPoints.map a))
    (((pieces i).obj σ).ρ.comp (rationalPoints.map a))).mpr (h i)

/-- With smooth grade models the forward spectral criterion uses precisely the
published compact-open generalized-weight predicate. -/
theorem pqRegularity_disjoint_weights
    (ha : IsSplitComponent a)
    (hsmooth : ∀ i, letI := leviPointTopology l hl; IsSmooth ((pieces i).obj σ).ρ)
    (h : IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := RationalPointFamily.splitComponentPointTopology ha
    ∀ i, Disjoint (groupExponents ha σ)
      {χ | IsGeneralizedWeight ((pieces i).obj σ).ρ (rationalPoints.map a) χ
        ha.isCentralSplitTorus.isCentral.map_mem_center} := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := ha.isAffine
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  let := RationalPointFamily.splitComponentPointTopology ha
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have hcont : Continuous (rationalPoints.map a) :=
    Langlands.AlgebraicGeometry.PointTopology.continuous_rationalPointMap k a.hom.hom
  intro i
  apply Set.disjoint_left.mpr
  intro χ hχ hχi
  exact Set.disjoint_left.mp
    (pqRegularity_disjoint_generalizedCharacters p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      a s pieces e σ h i)
    ((isGeneralizedWeight_iff σ.representation σ.isSmooth (rationalPoints.map a) hcont
      ha.isCentralSplitTorus.isCentral.map_mem_center χ).mp hχ)
    ((isGeneralizedWeight_iff ((pieces i).obj σ).ρ (hsmooth i) (rationalPoints.map a) hcont
      ha.isCentralSplitTorus.isCentral.map_mem_center χ).mp hχi)

/-- Under finite action-quotient hypotheses, disjoint compact-open weights on
all smooth quotient-grade models imply the actual PQ regularity condition. -/
theorem pqRegularity_of_disjoint_weights
    (ha : IsSplitComponent a)
    (hsmooth : ∀ i, letI := leviPointTopology l hl; IsSmooth ((pieces i).obj σ).ρ)
    [Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (σ.obj.ρ.comp (rationalPoints.map a)))]
    [∀ i, Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (((pieces i).obj σ).ρ.comp (rationalPoints.map a)))]
    (h : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      letI := RationalPointFamily.splitComponentPointTopology ha
      ∀ i, Disjoint (groupExponents ha σ)
        {χ | IsGeneralizedWeight ((pieces i).obj σ).ρ (rationalPoints.map a) χ
          ha.isCentralSplitTorus.isCentral.map_mem_center}) :
    IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := ha.isAffine
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  let := RationalPointFamily.splitComponentPointTopology ha
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have hcont : Continuous (rationalPoints.map a) :=
    Langlands.AlgebraicGeometry.PointTopology.continuous_rationalPointMap k a.hom.hom
  apply pqRegularity_of_disjoint_generalizedCharacters p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    a s pieces e σ
  intro i
  apply Set.disjoint_left.mpr
  intro χ hχ hχi
  exact Set.disjoint_left.mp (h i)
    ((isGeneralizedWeight_iff σ.representation σ.isSmooth (rationalPoints.map a) hcont
      ha.isCentralSplitTorus.isCentral.map_mem_center χ).mpr hχ)
    ((isGeneralizedWeight_iff ((pieces i).obj σ).ρ (hsmooth i) (rationalPoints.map a) hcont
      ha.isCentralSplitTorus.isCentral.map_mem_center χ).mpr hχi)

end Langlands.Aubert.General.RepresentedParabolic
