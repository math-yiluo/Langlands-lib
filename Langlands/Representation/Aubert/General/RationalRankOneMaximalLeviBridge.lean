import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization
import Langlands.Representation.Aubert.General.RationalRankOneNormalizingWeyl
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalReducibilityStatement
import Langlands.Representation.Exponents.RepresentedCuspidalityComparison
import Langlands.Representation.Aubert.General.RationalLeviCuspidalityTransportProof
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.GroupScheme.Rational.StandardParabolicClassificationAssembly
import Langlands.GroupScheme.Rational.StandardParabolicOrderFromRoots
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Rational.CentralizerRootSystemInheritance
import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen
import Langlands.Representation.Plancherel.RationalTwistStabilizer
import Langlands.Representation.Smooth.LengthTwoEndpoints
import Langlands.Representation.Smooth.IrreducibleRealization

/-! # The rational rank-one self-association target from Renard VII.1.3

Renard VII.1.3, applied to the standard maximal parabolic of a maximal proper set
of simple roots, gives a rational point normalizing the actual standard Levi
scheme and lying outside its points. Conjugacy of maximal split tori inside the
Levi corrects it into the normalizer of the split torus points. Through the
published normalizer-form equivalence this proves
`RationalRankOneSelfAssociationStatement` from
`MaximalLeviSupercuspidalReducibilityStatement`.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section TorusNormalizer

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M : GroupScheme (Spec (CommRingCat.of k))}

/-- A point normalizing a closed connected reductive subgroup, through an
automorphism of that subgroup, can be corrected by a point of the subgroup to
normalize the image of a maximal split torus of the subgroup. The corrected
point normalizes the subgroup points and lies outside them when the original
point does. -/
theorem exists_torusNormalizer_of_leviNormalizer
    (hM : IsConnectedReductive M) (j : M ⟶ G) (iM : T.toGrp ⟶ M)
    (hiM : IsMaximalSplitTorus iM) (g : rationalPoints G) (φ : M ≅ M)
    (hφ : φ.hom ≫ j = j ≫ (G.innerIso g).hom) (hg : g ∉ pointImage j) :
    ∃ n : rationalPoints G,
      (∀ x : rationalPoints G, x ∈ pointImage (iM ≫ j) ↔
        n * x * n⁻¹ ∈ pointImage (iM ≫ j)) ∧
      (∀ x ∈ pointImage j, n * x * n⁻¹ ∈ pointImage j) ∧ n ∉ pointImage j := by
  have := hM.isAffineHom
  have := hM.smooth
  have := hM.connectedSpace
  obtain ⟨m, e, hm⟩ := smoothMaximalSplitTorusConjugacy k M T T iM (iM ≫ φ.hom) hiM (hiM.comp_iso φ)
  set m' : rationalPoints G := rationalPoints.map j m with hm'
  have hm'L : m' ∈ pointImage j := ⟨m, rfl⟩
  -- The two conjugates of the torus image agree.
  have htorus : iM ≫ j ≫ (G.innerIso m').hom = e.hom ≫ iM ≫ j ≫ (G.innerIso g).hom := by
    have h := congrArg (· ≫ j) hm
    simp only [Category.assoc] at h
    rw [innerIso_hom_comp] at h
    rw [← hφ]
    exact h
  have hT : ∀ x : rationalPoints G,
      m'⁻¹ * x * m' ∈ pointImage (iM ≫ j) ↔ g⁻¹ * x * g ∈ pointImage (iM ≫ j) := by
    intro x
    have h1 := mem_pointImage_comp_innerIso (iM ≫ j) m' x
    have h2 := mem_pointImage_comp_innerIso (iM ≫ j) g x
    simp only [Category.assoc] at h1 h2
    rw [← h1, ← h2, htorus, pointImage_iso_comp]
  -- The automorphism shows that `g` normalizes the subgroup points.
  have hL : ∀ x : rationalPoints G, x ∈ pointImage j ↔ g⁻¹ * x * g ∈ pointImage j := by
    intro x
    rw [← mem_pointImage_comp_innerIso, ← hφ, pointImage_iso_comp]
  refine ⟨g⁻¹ * m', ?_, ?_, ?_⟩
  · intro y
    have h := hT (m' * y * m'⁻¹)
    have e1 : m'⁻¹ * (m' * y * m'⁻¹) * m' = y := by group
    have e2 : g⁻¹ * (m' * y * m'⁻¹) * g = g⁻¹ * m' * y * (g⁻¹ * m')⁻¹ := by group
    rw [e1, e2] at h
    exact h
  · intro x hx
    have hx' : m' * x * m'⁻¹ ∈ pointImage j :=
      (pointImage j).mul_mem ((pointImage j).mul_mem hm'L hx) ((pointImage j).inv_mem hm'L)
    have h := (hL _).mp hx'
    have e2 : g⁻¹ * (m' * x * m'⁻¹) * g = g⁻¹ * m' * x * (g⁻¹ * m')⁻¹ := by group
    rwa [e2] at h
  · intro hn
    apply hg
    have h : (g⁻¹ * m') * m'⁻¹ ∈ pointImage j :=
      (pointImage j).mul_mem hn ((pointImage j).inv_mem hm'L)
    have e3 : (g⁻¹ * m') * m'⁻¹ = g⁻¹ := by group
    rw [e3] at h
    simpa using (pointImage j).inv_mem h

end TorusNormalizer


section InductionCongr

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
  [NonarchimedeanGroup Γ]

/-- Irreducibility of normalized induction does not depend on how equal
parabolic, Levi and radical subgroups are presented, for representations of
the two Levi presentations identified by an equivariant linear equivalence. -/
theorem normalizedInduction_isIrreducible_congr {P M U P' M' U' : Subgroup Γ}
    (hP : P = P') (hM : M = M') (hU : U = U')
    (h : IsSemidirectDecomposition P M U) (hUc : IsClosed (U : Set Γ))
    (h' : IsSemidirectDecomposition P' M' U') (hUc' : IsClosed (U' : Set Γ))
    (A : SmoothRep.{0, u, w} ℂ M) (A' : SmoothRep.{0, u, w} ℂ M') (f : A ≃ₗ[ℂ] A')
    (hf : ∀ (m : M) (x : A),
      f (A.representation m x) = A'.representation ⟨m, hM ▸ m.2⟩ (f x)) :
    ((normalizedInductionFunctor h hUc).obj A).IsIrreducible ↔
      ((normalizedInductionFunctor h' hUc').obj A').IsIrreducible := by
  subst hP hM hU
  let e : A ≅ A' := SmoothRep.mkIso
    (Representation.Equiv.mk f (fun m => LinearMap.ext fun x => hf m x))
  exact ⟨SmoothRep.isIrreducible_of_iso ((normalizedInductionFunctor h hUc).mapIso e),
    SmoothRep.isIrreducible_of_iso ((normalizedInductionFunctor h hUc).mapIso e.symm)⟩

end InductionCongr

section Maximality

open RationalPointFamily

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A closed subgroup whose range is every point is an isomorphism. -/
theorem isIso_of_closedSubgroup_range_eq_top {P : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (hp : IsClosedSubgroup p) (h : SubgroupFunctor.range p = ⊤) : IsIso p := by
  have hrep : (⊤ : SubgroupFunctor G).IsRepresentedBy p := by
    rw [← h]
    exact hp.isRepresentedBy_range
  have hid : (⊤ : SubgroupFunctor G).IsRepresentedBy (𝟙 G) := by
    refine ⟨inferInstance, ?_⟩
    apply SubgroupFunctor.ext
    intro Q
    apply Subgroup.ext
    intro x
    exact ⟨fun _ => trivial, fun _ => ⟨x, Category.comp_id x⟩⟩
  have he : (hrep.isoOfIsRepresentedBy hid).hom = p := by
    simpa using hrep.isoOfIsRepresentedBy_hom_comp hid
  rw [← he]
  infer_instance

/-- A factor between closed subgroups with the same range is an isomorphism. -/
theorem isIso_of_comp_eq_of_range_eq {P Q : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (q : Q ⟶ G) (j : P ⟶ Q) (hp : IsClosedSubgroup p)
    (hq : IsClosedSubgroup q) (hj : j ≫ q = p)
    (h : SubgroupFunctor.range q = SubgroupFunctor.range p) : IsIso j := by
  have hqrep : (SubgroupFunctor.range p).IsRepresentedBy q := ⟨hq.isRepresentedBy_range.1, h⟩
  have he : j = (hp.isRepresentedBy_range.isoOfIsRepresentedBy hqrep).hom :=
    hqrep.hom_ext (by rw [hj, SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp])
  rw [he]
  infer_instance

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T)

/-- The standard parabolic of all simple roots is the whole group. -/
theorem standardParabolic_simpleRelativeRoots_eq_top
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i) :
    standardParabolic i ν (simpleRelativeRoots i ν) = ⊤ := by
  have hcmp0 :=
    (hRoots.standardCocharacterDynamicComparison i ν _ hi.isSplitSubtorus.1 hν
      (relativeRootSignsDetermineDynamic k G hG T i hi)).standard_eq_dynamic
      i ν _ (isStandardCocharacter_simple_zero i ν)
  rw [hcmp0.1, groupHom_zero_comp_eq_trivialCocharacter,
    Dynamic.parabolic_trivialCocharacter]

/-- The standard parabolic of a maximal proper set of simple roots is maximal
among actual rational parabolics: a parabolic through which it factors is
either itself or the whole group. -/
theorem standardParabolic_isMaximal
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]
    {J : Finset (SimpleRoot i ν)} {α : SimpleRoot i ν} (hJ : J = Finset.univ.erase α) :
    ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G)
      (j : Standard.parabolicScheme i ν (rootSet i ν J) ⟶ Q),
      IsParabolicSubgroup q → j ≫ q = Standard.parabolicHom i ν (rootSet i ν J) →
        IsIso j ∨ IsIso q := by
  intro Q q j hq hjq
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG Q q hq.isClosedSubgroup).mp hq
  have hpc := Standard.isClosedSubgroup_parabolicHom i ν (rootSet i ν J)
  have hrangeP : SubgroupFunctor.range (Standard.parabolicHom i ν (rootSet i ν J)) =
      standardParabolic i ν (rootSet i ν J) :=
    (Standard.isRepresentedBy_parabolicHom i ν _).2
  have hPq : standardParabolic i ν (rootSet i ν J) ≤ SubgroupFunctor.range q := by
    rw [← hrangeP, ← hjq]
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ j.hom.hom, by rw [Grp.comp_hom_hom, Category.assoc]⟩
  have hOrder := standardParabolic_order_of_root_comparison i ν hν
    (relativeRootNegation k G hG T i hi)
    (fun J hJ => (hStandard k G hG T i hi ν hν J hJ).1)
    (fun z e => (relativeRootSignInclusions k G hG T i hi z e).1)
    (fun z e => (relativeRootSignInclusions k G hG T i hi z e).2)
  have hmin : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ Dynamic.parabolic χ := by
    rw [← standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν, ← hχ]
    exact ((hOrder.1 ∅ _ (Set.empty_subset _) (rootSet_subset i ν J)).1.mp
      (Set.empty_subset _)).trans hPq
  obtain ⟨K, hK, hKeq⟩ := exists_standardParabolic_eq_of_parabolic_le_of_structural_statements
    smoothMaximalSplitTorusConjugacy dynamicConnected relativeRootSignInclusions
    relativeRootNegation hG hi hν χ hmin
  have hJK : rootSet i ν J ⊆ K :=
    (hOrder.1 _ K (rootSet_subset i ν J) hK).1.mpr (by rw [← hKeq, ← hχ]; exact hPq)
  by_cases hαK : α.val ∈ K
  · right
    have hKall : K = simpleRelativeRoots i ν := by
      apply Set.Subset.antisymm hK
      intro β hβ
      by_cases hβα : (⟨β, hβ⟩ : SimpleRoot i ν) = α
      · rw [← hβα] at hαK
        exact hαK
      · apply hJK
        change ((⟨β, hβ⟩ : SimpleRoot i ν) : characterLattice T) ∈ rootSet i ν J
        rw [val_mem_rootSet, hJ]
        exact Finset.mem_erase.mpr ⟨hβα, Finset.mem_univ _⟩
    apply isIso_of_closedSubgroup_range_eq_top q hq.isClosedSubgroup
    rw [hχ, hKeq, hKall, standardParabolic_simpleRelativeRoots_eq_top i ν hG hi hν hRoots]
  · left
    have hKJ : K = rootSet i ν J := by
      apply Set.Subset.antisymm _ hJK
      intro β hβ
      have hβs := hK hβ
      change ((⟨β, hβs⟩ : SimpleRoot i ν) : characterLattice T) ∈ rootSet i ν J
      rw [val_mem_rootSet, hJ]
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      apply hαK
      rw [← h]
      exact hβ
    apply isIso_of_comp_eq_of_range_eq _ q j hpc hq.isClosedSubgroup hjq
    rw [hχ, hKeq, hKJ, hrangeP]

end Maximality

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology RepresentedParabolic

section LeviNormalizer

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- A rational point normalizing the actual standard Levi scheme through an
automorphism of it, and lying outside its points, can be replaced by a point of
the normalizer of the split torus points that normalizes the literal standard
Levi subgroup without belonging to it. -/
theorem exists_torusNormalizer_of_standardLeviNormalizer
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (J : Finset (SimpleRoot i ν))
    (g : rationalPoints G) (φ : Standard.leviScheme i ν (rootSet i ν J) ≅
      Standard.leviScheme i ν (rootSet i ν J))
    (hφ : φ.hom ≫ Standard.leviToParabolic i ν (rootSet i ν J) ≫
        Standard.parabolicHom i ν (rootSet i ν J) =
      Standard.leviToParabolic i ν (rootSet i ν J) ≫
        Standard.parabolicHom i ν (rootSet i ν J) ≫ (G.innerIso g).hom)
    (hg : g ∉ pointImage (Standard.leviToParabolic i ν (rootSet i ν J) ≫
      Standard.parabolicHom i ν (rootSet i ν J))) :
    ∃ n : Group.RelativeWeyl.normalizer (torusPoints i),
      (∀ x ∈ levi i ν J, (n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹ ∈
        levi i ν J) ∧ (n : RationalPoint k G.X) ∉ levi i ν J := by
  have hcomp : Standard.leviToParabolic i ν (rootSet i ν J) ≫
      Standard.parabolicHom i ν (rootSet i ν J) = Standard.leviHom i ν (rootSet i ν J) :=
    Standard.leviToParabolic_comp i ν _
  rw [hcomp] at hg
  have hφ' : φ.hom ≫ Standard.leviHom i ν (rootSet i ν J) =
      Standard.leviHom i ν (rootSet i ν J) ≫ (G.innerIso g).hom := by
    rw [← hcomp]
    simpa only [Category.assoc] using hφ
  let iL := standardLeviTorusFactor i ν (rootSet i ν J)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J))
  have hiL : IsMaximalSplitTorus iL :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν (rootSet i ν J)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J))
  obtain ⟨n, hnT, hnL, hnnot⟩ := exists_torusNormalizer_of_leviNormalizer
    (standardLeviScheme_isConnectedReductive i ν hStandard dynamicCentralizerReductive
      hG hi hν J) (Standard.leviHom i ν (rootSet i ν J)) iL hiL g φ hφ' hg
  have hMpt : pointImage (Standard.leviHom i ν (rootSet i ν J)) = levi i ν J :=
    congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _)))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J)).2
  have hTpt : pointImage (iL ≫ Standard.leviHom i ν (rootSet i ν J)) = torusPoints i := by
    rw [standardLeviTorusFactor_comp]
    rfl
  rw [hMpt] at hnL hnnot
  rw [hTpt] at hnT
  exact ⟨⟨n, Subgroup.mem_normalizer_iff.mpr hnT⟩, hnL, hnnot⟩

end LeviNormalizer

section Supercuspidal

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)

local instance bridgeAmbientPointTopology : TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Inside-Levi standard cuspidality of a representation of the literal Levi
subgroup implies supercuspidality, for every actual proper rational parabolic
of the actual standard Levi scheme, of its pullback to the Levi's own points. -/
theorem isSupercuspidal_pullback_of_isCorollaryLeviCuspidal
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    [Fintype (SimpleRoot i ν)]
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G)))
    (J : Finset (SimpleRoot i ν)) (hMJ : IsClosed (levi i ν J : Set (rationalPoints G)))
    (hInner : ∀ K : Finset J,
      IsSemidirectDecomposition ((parabolic i ν (leviIndex J K)).subgroupOf (levi i ν J))
        ((levi i ν (leviIndex J K)).subgroupOf (levi i ν J))
        ((unipotent i ν (leviIndex J K)).subgroupOf (levi i ν J)))
    (σ : SmoothRep.{0, u, max u w} ℂ (levi i ν J))
    (hσ : IsCorollaryLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) J hMJ hInner hU σ) :
    haveI := (standardLeviScheme_isConnectedReductive i ν hStandard dynamicCentralizerReductive
      hG hi hν J).isAffineHom
    haveI : T2Space k := BruhatTits.localField_t2Space k
    letI : TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν J))) :=
      pointTopology
    ∀ [LocallyCompactSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν J)))]
      [NonarchimedeanGroup (rationalPoints (Standard.leviScheme i ν (rootSet i ν J)))],
      IsSupercuspidal (SmoothRep.pullback (leviRationalPointHomeomorph i ν J) σ) := by
  let L := Standard.leviScheme i ν (rootSet i ν J)
  have hL : IsConnectedReductive L :=
    standardLeviScheme_isConnectedReductive i ν hStandard dynamicCentralizerReductive hG hi hν J
  have := hL.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have := hL.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : TopologicalSpace (rationalPoints L) := pointTopology
  intro _ _
  let iL := standardLeviTorusFactor i ν (rootSet i ν J)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J))
  have hiL : IsMaximalSplitTorus iL :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν (rootSet i ν J)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J))
  have := hiL.isSplitSubtorus.mono
  have hνL : IsGenericCocharacter iL ν :=
    (standardLeviStandardFamilies dynamicLie hStandard k G hG T i hi ν hν
      (rootSet i ν J) (rootSet_subset i ν J) L hL
      (Standard.leviHom i ν (rootSet i ν J))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J))).2.1
  have hRootsL : HasRelativeRootSystem iL :=
    HasRelativeRootSystem.of_standardLeviTorusFactor hRoots hStandard hG hi ν hν
      (rootSet i ν J) (rootSet_subset i ν J) hL (Standard.leviHom i ν (rootSet i ν J))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J))
  let := simpleRelativeRootFintype iL hRootsL hiL.isSplitSubtorus.1 ν
  let hUL := isClosed_unipotent_of_isNonarchimedeanLocalField iL ν
  have hOwn := isSemidirectDecomposition_of_standardCocharacterStatement iL ν hStandard hL hiL hνL
  have hLC : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J hMJ hInner σ :=
    fun I => (SmoothRep.isZero_iff_subsingleton_carrier _).mp (hσ I.1 I.2)
  have hcusp := (rationalLeviCuspidalityTransport.{u, max u w} dynamicLie hStandard k G hG T i hi
    ν hν J hL hU hUL hMJ hInner hOwn σ).mpr hLC
  exact isSupercuspidal_of_isCuspidal iL ν parabolicDynamic
    smoothMaximalSplitTorusConjugacy hL hiL hνL hRootsL hOwn hUL _ hcusp

omit [Mono i.hom.hom.left] in
/-- The actual normalized induction from the represented standard parabolic,
applied to the pullback of a representation of the literal Levi subgroup to the
Levi's own points, is irreducible exactly when the normalized induction from
the literal standard family is. -/
theorem leviInduction_isIrreducible_iff_standard
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G)))
    (J : Finset (SimpleRoot i ν))
    (hp : IsParabolicSubgroup (Standard.parabolicHom i ν (rootSet i ν J)))
    (hl : IsRationalLeviSubgroup (Standard.leviToParabolic i ν (rootSet i ν J)))
    (hr : LeviSubgroup.IsGeometricUnipotentRadical
      (Standard.unipotentToParabolic i ν (rootSet i ν J)))
    (hmul : IsIso (subgroupMultiplication (Standard.leviToParabolic i ν (rootSet i ν J))
      (Standard.unipotentToParabolic i ν (rootSet i ν J))))
    (σ : SmoothRep.{0, u, w} ℂ (levi i ν J)) :
    haveI : T2Space k := BruhatTits.localField_t2Space k
    letI := leviPointTopology (Standard.leviToParabolic i ν (rootSet i ν J)) hl
    ((leviInductionFunctor (Standard.parabolicHom i ν (rootSet i ν J))
        (Standard.leviToParabolic i ν (rootSet i ν J))
        (Standard.unipotentToParabolic i ν (rootSet i ν J)) hp hr hl hmul).obj
          (SmoothRep.pullback (leviRationalPointHomeomorph i ν J) σ)).IsIrreducible ↔
      ((normalizedInductionFunctor
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
        (hU J)).obj σ).IsIrreducible := by
  let : T2Space k := BruhatTits.localField_t2Space k
  let := leviPointTopology (Standard.leviToParabolic i ν (rootSet i ν J)) hl
  have hPpt : pointImage (Standard.parabolicHom i ν (rootSet i ν J)) = parabolic i ν J :=
    congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _)))
      (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν J)).2
  have hMpt : pointImage (Standard.leviToParabolic i ν (rootSet i ν J) ≫
      Standard.parabolicHom i ν (rootSet i ν J)) = levi i ν J := by
    rw [Standard.leviToParabolic_comp]
    exact congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _)))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J)).2
  rw [leviInductionFunctor_obj]
  apply normalizedInduction_isIrreducible_congr hPpt hMpt (standard_unipotent_pointImage i ν J)
    _ _ _ _ _ _ (LinearEquiv.refl ℂ _)
  intro m x
  change σ.representation (leviRationalPointHomeomorph i ν J
      ((leviPointsEquiv _ _ hp hl).symm m)) x = σ.representation ⟨m, _⟩ x
  congr 2
  apply Subtype.ext
  rw [leviRationalPointHomeomorph_apply_coe, ← Standard.leviToParabolic_comp,
    ← leviPointsEquiv_apply_coe _ _ hp hl, ContinuousMulEquiv.apply_symm_apply]

/-- Renard VII.1.3 at the standard maximal parabolic of a maximal proper set of
simple roots: a reducible normalized induction of an irreducible inside-Levi
cuspidal representation of the literal Levi subgroup yields a point of the
normalizer of the split torus points that normalizes the literal Levi without
belonging to it. -/
theorem exists_torusNormalizer_of_maximalLeviSupercuspidalReducibility
    (hVII : RepresentedParabolic.MaximalLeviSupercuspidalReducibilityStatement.{u, max u w})
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G)))
    {J : Finset (SimpleRoot i ν)} {α : SimpleRoot i ν} (hα : J = Finset.univ.erase α)
    (hMJ : IsClosed (levi i ν J : Set (rationalPoints G)))
    (hInner : ∀ K : Finset J,
      IsSemidirectDecomposition ((parabolic i ν (leviIndex J K)).subgroupOf (levi i ν J))
        ((levi i ν (leviIndex J K)).subgroupOf (levi i ν J))
        ((unipotent i ν (leviIndex J K)).subgroupOf (levi i ν J)))
    (σ : SmoothRep.{0, u, max u w} ℂ (levi i ν J)) (hσ : σ.IsIrreducible)
    (hcusp : IsCorollaryLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) J hMJ hInner hU σ)
    (hred : ¬ ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
      (hU J)).obj σ).IsIrreducible) :
    ∃ n : Group.RelativeWeyl.normalizer (torusPoints i),
      (∀ x ∈ levi i ν J, (n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹ ∈
        levi i ν J) ∧ (n : RationalPoint k G.X) ∉ levi i ν J := by
  have := hG.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  obtain ⟨hp, hl, hr, hmul⟩ :=
    standard_representatives_geometric_of_standardCocharacter i ν hStandard hG hi hν J
  have hJne : J ≠ Finset.univ := by
    intro h
    have hαJ : α ∈ J := h ▸ Finset.mem_univ α
    rw [hα] at hαJ
    exact Finset.notMem_erase α Finset.univ hαJ
  have hproper : ¬ IsIso (Standard.parabolicHom i ν (rootSet i ν J)) := by
    intro hiso
    let := hiso
    apply standardParabolic_ne_top_of_ne_univ i ν hi.isSplitSubtorus.1
      hRoots hStandard hG hi hν hJne
    rw [← (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν J)).2]
    apply SubgroupFunctor.ext
    intro Q
    apply top_unique
    intro x _
    refine ⟨x ≫ (inv (Standard.parabolicHom i ν (rootSet i ν J))).hom.hom, ?_⟩
    change (x ≫ (inv (Standard.parabolicHom i ν (rootSet i ν J))).hom.hom) ≫
      (Standard.parabolicHom i ν (rootSet i ν J)).hom.hom = x
    rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id]
  have hmax := standardParabolic_isMaximal i ν hStandard hG hi hν hRoots hα
  -- The representation of the Levi's own points.
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology (Standard.leviToParabolic i ν (rootSet i ν J)) hl
  let : LocallyCompactSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν J))) :=
    leviPoints_locallyCompactSpace _ _ hp hl
  let : NonarchimedeanGroup (rationalPoints (Standard.leviScheme i ν (rootSet i ν J))) :=
    leviPoints_nonarchimedeanGroup _ _ hp hl
  have hρirr : (SmoothRep.pullback (leviRationalPointHomeomorph i ν J) σ).IsIrreducible := by
    let : σ.representation.IsIrreducible := hσ
    exact CuspidalSupport.isIrreducible_comp_of_surjective σ.representation
      (leviRationalPointHomeomorph i ν J).toMonoidHom
      (leviRationalPointHomeomorph i ν J).surjective
  have hρsc : IsSupercuspidal (SmoothRep.pullback (leviRationalPointHomeomorph i ν J) σ) :=
    isSupercuspidal_pullback_of_isCorollaryLeviCuspidal i ν hStandard hG hi hν hRoots
      hU J hMJ hInner σ hcusp
  have hρred := fun h => hred
    ((leviInduction_isIrreducible_iff_standard i ν hStandard hG hi hν hU J hp hl hr hmul σ).mp h)
  obtain ⟨g, φ, hφ, hg, -⟩ := hVII k G hG _ _ _
    (Standard.parabolicHom i ν (rootSet i ν J)) (Standard.leviToParabolic i ν (rootSet i ν J))
    (Standard.unipotentToParabolic i ν (rootSet i ν J)) hp hl hr hmul hproper hmax
    (SmoothRep.pullback (leviRationalPointHomeomorph i ν J) σ) hρirr hρsc hρred
  -- Correct the normalizing point into the torus normalizer.
  exact exists_torusNormalizer_of_standardLeviNormalizer i ν hStandard hG hi hν J g φ hφ hg

end Supercuspidal

section Assembly

/-- **Bridge.** Renard VII.1.3 for actual maximal parabolics, with Levi
carriers in `Type (max (u + 1) v)`, proves the rank-one normalizing-Weyl
statement at the full rational scope. The parabolic-dynamic description of
parabolics and the conjugacy of maximal split tori enter through their
published proofs. -/
theorem rationalRankOneNormalizingWeyl_of_maximalLeviSupercuspidalReducibility
    (hVII : RepresentedParabolic.MaximalLeviSupercuspidalReducibilityStatement.{u, max (u + 1) v}) :
    RationalRankOneNormalizingWeylStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  have := hG.smooth
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  intro _ hN hZ C actual hLength hSimple hIdent hMin hAssoc J hJ σ hσ hcusp hred
  obtain ⟨α, hα⟩ := hJ
  exact exists_torusNormalizer_of_maximalLeviSupercuspidalReducibility.{u, max (u + 1) v}
    i ν hVII hStandard hG hi hν hRoots hU hα (hM J)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) σ.val hσ hcusp hred

/-- Renard VII.1.3, for fields in universe `u` and Levi carriers in universe
`max (u + 1) v`, implies the rational rank-one self-association target at
universes `u, v`. -/
def RationalRankOneSelfAssociationFromMaximalLeviStatement : Prop :=
  RepresentedParabolic.MaximalLeviSupercuspidalReducibilityStatement.{u, max (u + 1) v} →
    RationalRankOneSelfAssociationStatement.{u, v}

/-- The rational self-association target follows from Renard VII.1.3 through
the published normalizer-form equivalence. -/
theorem rationalRankOneSelfAssociation_of_maximalLeviSupercuspidalReducibility :
    RationalRankOneSelfAssociationFromMaximalLeviStatement.{u, v} := fun hVII =>
  rationalRankOneSelfAssociation_of_normalizingWeyl
    (rationalRankOneNormalizingWeyl_of_maximalLeviSupercuspidalReducibility hVII)

end Assembly

end Langlands.Aubert.General.RationalPointFamily
