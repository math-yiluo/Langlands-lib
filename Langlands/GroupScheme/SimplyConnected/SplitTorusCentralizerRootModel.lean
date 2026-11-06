import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedGeometricReduction
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection

/-! # Actual maximal tori and roots of split-torus centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

set_option autoImplicit false

section Roots

variable {G M : GroupScheme (Spec (CommRingCat.of k))} {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]

/-- For compatible actions of the same torus, the roots of an actual split-torus
centralizer are precisely the ambient roots trivial on the given split torus. -/
theorem relativeRoots_splitTorusCentralizer_factor
    (a : A.toGrp ⟶ G) (hA : IsSplitTorus A.toGrp)
    (i : T.toGrp ⟶ G) (iM : T.toGrp ⟶ M) (j : M ⟶ G)
    (hj : (torusCentralizer a).IsRepresentedBy j)
    (hcomp : iM ≫ j = i) (f : A ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ i = a) :
    relativeRoots iM = {α | α ∈ relativeRoots i ∧ f ≫ α = 0} := by
  let ν : cocharacterLattice T := centralizingCocharacter hA a ≫ f
  have hν : CommGroupScheme.groupHom ν ≫ i =
      CommGroupScheme.groupHom (centralizingCocharacter hA a) ≫ a := by
    change (CommGroupScheme.groupHom (centralizingCocharacter hA a) ≫
      CommGroupScheme.groupHom f) ≫ i = _
    rw [Category.assoc, hf]
  have hjν : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j := by
    rw [hν, centralizingCocharacter_spec hA a]
    exact hj
  have hroots := relativeRoots_centralizer_factor dynamicLie i iM j hcomp ν hjν
  have hfactor : CommGroupScheme.groupHom f ≫ iM = torusCentralizerFactor a hj := by
    apply hj.hom_ext
    rw [Category.assoc, hcomp, hf, torusCentralizerFactor_comp]
  have hcentral : IsCentral (CommGroupScheme.groupHom f ≫ iM) := by
    rw [hfactor]
    exact isCentral_torusCentralizerFactor a hj
  ext α
  constructor
  · intro hα
    exact ⟨relativeRoots_subset_of_factor hj iM hcomp hα,
      root_restrict_eq_zero_of_isCentral iM f hA hcentral hα⟩
  · rintro ⟨hα, hzero⟩
    rw [hroots]
    refine ⟨hα, ?_⟩
    simp only [latticePairing_apply, ν, Category.assoc, hzero,
      Limits.comp_zero, map_zero]

end Roots

section Model

variable {G M : GroupScheme (Spec (CommRingCat.of k))} {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An actual split maximal torus containing the given subtorus and factoring
through its centralizer. Root comparison is provided by the companion theorem. -/
structure SplitTorusCentralizerRootModel (a : A.toGrp ⟶ G) (j : M ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  ambient : torus.toGrp ⟶ G
  centralizer : torus.toGrp ⟶ M
  factor : A ⟶ torus
  isSplit : IsSplitTorus torus.toGrp
  ambient_maximal : IsMaximalTorus ambient
  centralizer_maximal : IsMaximalTorus centralizer
  factor_closed : IsClosedSubgroup (CommGroupScheme.groupHom factor)
  centralizer_comp : centralizer ≫ j = ambient
  factor_comp : CommGroupScheme.groupHom factor ≫ ambient = a

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Choose compatible actual split maximal tori of an ambient affine finite-type
group and a supplied split-torus centralizer over an algebraically closed field. -/
def splitTorusCentralizerRootModel [IsAlgClosed k]
    (a : A.toGrp ⟶ G) (ha : IsSplitSubtorus a) (j : M ⟶ G)
    (hj : (torusCentralizer a).IsRepresentedBy j) :
    SplitTorusCentralizerRootModel a j := Classical.choice <| by
  obtain ⟨T, i, hi, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G a ha.1.isTorus ha.2
  have hjc : IsClosedSubgroup j := ha.1.isClosedSubgroup_torusCentralizer a hj
  let iM : T.toGrp ⟶ M :=
    hj.factorHom i (range_le_torusCentralizer_of_factor a i f hf)
  have hiM : iM ≫ j = i := hj.factorHom_comp _ _
  refine
    ⟨{ torus := T
       ambient := i
       centralizer := iM
       factor := Additive.ofMul f
       isSplit := hi.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
       ambient_maximal := hi
       centralizer_maximal := IsMaximalTorus.of_comp hjc (hiM.symm ▸ hi)
       factor_closed := IsClosedSubgroup.of_comp hi.2.1 (hf.symm ▸ ha.2)
       centralizer_comp := hiM
       factor_comp := hf }⟩

namespace SplitTorusCentralizerRootModel

variable {a : A.toGrp ⟶ G} {j : M ⟶ G}
  (C : SplitTorusCentralizerRootModel a j)

/-- The generic cocharacter of the original split torus, in the actual ambient torus. -/
def cocharacter (hA : IsSplitTorus A.toGrp) : cocharacterLattice C.torus :=
  centralizingCocharacter hA a ≫ C.factor

/-- The chosen ambient-torus cocharacter has exactly the original all-test centralizer. -/
theorem cocharacter_centralizer (hA : IsSplitTorus A.toGrp) :
    Dynamic.centralizer (CommGroupScheme.groupHom (C.cocharacter hA) ≫ C.ambient) =
      torusCentralizer a := by
  change Dynamic.centralizer
    ((CommGroupScheme.groupHom (centralizingCocharacter hA a) ≫
      CommGroupScheme.groupHom C.factor) ≫ C.ambient) = _
  rw [Category.assoc, C.factor_comp, centralizingCocharacter_spec]

variable [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]

/-- The model identifies centralizer roots with ambient roots restricting to zero. -/
theorem relativeRoots_eq (hA : IsSplitTorus A.toGrp)
    (hj : (torusCentralizer a).IsRepresentedBy j) :
    relativeRoots C.centralizer =
      {α | α ∈ relativeRoots C.ambient ∧ C.factor ≫ α = 0} :=
  relativeRoots_splitTorusCentralizer_factor a hA C.ambient C.centralizer j hj
    C.centralizer_comp C.factor C.factor_comp

/-- The same roots are the ambient roots with zero pairing against the model's cocharacter. -/
theorem relativeRoots_eq_pairing (hA : IsSplitTorus A.toGrp)
    (hj : (torusCentralizer a).IsRepresentedBy j) :
    relativeRoots C.centralizer =
      {α | α ∈ relativeRoots C.ambient ∧
        latticePairing C.torus α (C.cocharacter hA) = 0} := by
  apply relativeRoots_centralizer_factor dynamicLie C.ambient C.centralizer j
    C.centralizer_comp (C.cocharacter hA)
  rw [C.cocharacter_centralizer hA]
  exact hj

end SplitTorusCentralizerRootModel

end Model

end Langlands.GroupScheme
