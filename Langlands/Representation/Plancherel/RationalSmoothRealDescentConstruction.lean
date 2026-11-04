import Langlands.Representation.Plancherel.RationalImageRealDescent
import Langlands.Representation.Plancherel.RationalSmoothRealDescentStatement
import Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Smooth real descent from the local-point structural inputs -/

set_option autoImplicit false

noncomputable section

universe u v w

namespace Langlands.SmoothRealDescent

variable {G : Type v} [Group G] {A : Type w} [Group A] [IsMulTorsionFree A]

/-- A homomorphism to a torsion-free group with finite kernel quotient is trivial. -/
theorem eq_one_of_finite_kernel_quotient (f : G →* A) [Finite (G ⧸ f.ker)]
    (g : G) : f g = 1 := by
  apply pow_left_injective f.ker.index_ne_zero_of_finite
  change f g ^ f.ker.index = 1 ^ f.ker.index
  rw [one_pow, ← map_pow]
  exact f.ker.pow_index_mem g

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- A homomorphism to a torsion-free group with open kernel kills compact groups. -/
theorem eq_one_of_compact [CompactSpace G] (f : G →* A)
    (hf : IsOpen (f.ker : Set G)) (g : G) : f g = 1 := by
  let : Finite (G ⧸ f.ker) := f.ker.quotient_finite_of_isOpen hf
  exact eq_one_of_finite_kernel_quotient f g

/-- In particular, it kills every compact subgroup of its domain. -/
theorem compact_subgroup_le_ker (f : G →* A) (hf : IsOpen (f.ker : Set G))
    (C : Subgroup G) (hC : IsCompact (C : Set G)) : C ≤ f.ker := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  intro c hc
  exact eq_one_of_compact (f.comp C.subtype)
    (hf.preimage continuous_subtype_val) ⟨c, hc⟩

/-- An open subgroup containing a cocompact subgroup has finite coset space.
Neither subgroup is required to be normal. -/
theorem quotient_finite_of_cocompact (H U : Subgroup G) [CompactSpace (G ⧸ H)]
    (hHU : H ≤ U) (hU : IsOpen (U : Set G)) : Finite (G ⧸ U) := by
  have hcont : Continuous (Subgroup.quotientMapOfLE hHU) := by
    apply (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr
    exact QuotientGroup.continuous_mk
  have hsurj : Function.Surjective (Subgroup.quotientMapOfLE hHU) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk g, rfl⟩
  let : CompactSpace (G ⧸ U) := hsurj.compactSpace hcont
  let : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  exact finite_of_compact_of_discrete

/-- An open-kernel homomorphism to a torsion-free group which kills a cocompact
subgroup is trivial on the whole group. -/
theorem eq_one_of_cocompact (f : G →* A) (hf : IsOpen (f.ker : Set G))
    (H : Subgroup G) [CompactSpace (G ⧸ H)] (hH : H ≤ f.ker) (g : G) :
    f g = 1 := by
  let : Finite (G ⧸ f.ker) := quotient_finite_of_cocompact H f.ker hH hf
  exact eq_one_of_finite_kernel_quotient f g

end Langlands.SmoothRealDescent

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.RationalPoints
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (M : GroupScheme (Spec (CommRingCat.of F))) (hM : GroupScheme.IsConnectedReductive M)

/-- The three actual local-point inputs imply norm-kernel annihilation. -/
theorem rationalCommonNormKernel_le_ker_of_structure
    (hcompact : CentralNormKernelCompactness M hM)
    (hcocompact : CentralDerivedNormKernelCocompactness M hM)
    (hderived : DerivedSmoothRealAnnihilation M hM) :
    haveI : IsAffineHom M.X.hom := hM.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
    ∀ f : GroupScheme.rationalPoints M →* Multiplicative ℝ,
      IsOpen (f.ker : Set (GroupScheme.rationalPoints M)) →
        rationalCommonNormKernel M ≤ f.ker := by
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : Smooth M.X.hom := hM.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
  let : IsTopologicalGroup (GroupScheme.rationalPoints M) :=
    rationalPoint_isTopologicalGroup F M
  intro f hf
  let K := rationalCommonNormKernel M
  let Z := GroupScheme.schemeCenterPoints M
  let D := (GroupScheme.derivedSubgroup M).carrier (Over.mk (𝟙 _))
  let H := ((Z ⊓ K) ⊔ D).subgroupOf K
  have hZ : Z ⊓ K ≤ f.ker :=
    SmoothRealDescent.compact_subgroup_le_ker f hf (Z ⊓ K) hcompact
  have hD : D ≤ f.ker := hderived f hf
  have hH : H ≤ (f.comp K.subtype).ker := by
    intro x hx
    exact (sup_le hZ hD) hx
  let : CompactSpace (K ⧸ H) := hcocompact
  intro g hg
  exact SmoothRealDescent.eq_one_of_cocompact (f.comp K.subtype)
    (hf.preimage continuous_subtype_val) H hH ⟨g, hg⟩

/-- Descend a smooth real homomorphism using the three actual local-point
structural inputs. These inputs remain explicit construction parameters. -/
def rationalSmoothRealDescendOfStructure
    (hcompact : CentralNormKernelCompactness M hM)
    (hcocompact : CentralDerivedNormKernelCocompactness M hM)
    (hderived : DerivedSmoothRealAnnihilation M hM) :
    haveI : IsAffineHom M.X.hom := hM.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
    (f : GroupScheme.rationalPoints M →* Multiplicative ℝ) →
      IsOpen (f.ker : Set (GroupScheme.rationalPoints M)) → rationalImageRealFunctionals M := by
  letI : IsAffineHom M.X.hom := hM.isAffineHom
  letI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  letI : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
  intro f hf
  exact rationalImageRealDescend M f
    (rationalCommonNormKernel_le_ker_of_structure M hM hcompact hcocompact hderived f hf)

/-- The structural construction has the exact valuation-image evaluation law. -/
theorem rationalSmoothRealDescendOfStructure_projection
    (hcompact : CentralNormKernelCompactness M hM)
    (hcocompact : CentralDerivedNormKernelCocompactness M hM)
    (hderived : DerivedSmoothRealAnnihilation M hM) :
    haveI : IsAffineHom M.X.hom := hM.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
    ∀ (f : GroupScheme.rationalPoints M →* Multiplicative ℝ)
      (hf : IsOpen (f.ker : Set (GroupScheme.rationalPoints M)))
      (g : GroupScheme.rationalPoints M),
      rationalSmoothRealDescendOfStructure M hM hcompact hcocompact hderived f hf
        (Additive.ofMul (rationalValuationImageProjection M g)) = (f g).toAdd := by
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
  intro f hf g
  exact rationalImageRealDescend_projection M f _ g

/-- The structural construction is uniquely determined by evaluation on points. -/
theorem rationalSmoothRealDescendOfStructure_unique
    (hcompact : CentralNormKernelCompactness M hM)
    (hcocompact : CentralDerivedNormKernelCocompactness M hM)
    (hderived : DerivedSmoothRealAnnihilation M hM) :
    haveI : IsAffineHom M.X.hom := hM.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
    ∀ (f : GroupScheme.rationalPoints M →* Multiplicative ℝ)
      (hf : IsOpen (f.ker : Set (GroupScheme.rationalPoints M)))
      (phi : rationalImageRealFunctionals M),
      (∀ g : GroupScheme.rationalPoints M,
        phi (Additive.ofMul (rationalValuationImageProjection M g)) = (f g).toAdd) →
      phi = rationalSmoothRealDescendOfStructure M hM hcompact hcocompact hderived f hf := by
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
  intro f hf phi hphi
  exact rationalImageRealDescend_unique M f _ phi hphi

/-- Conditional reduction only: it does not supply any of the three local-point
structural proofs required for the unconditional endpoint. -/
theorem rationalSmoothRealDescent_of_structure :
    SmoothRealStructureStatement.{u} → RationalSmoothRealDescentStatement.{u} := by
  rintro ⟨hc, hq, hd⟩ F _ _ _ _ M hM
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
  intro f hf
  have hker := rationalCommonNormKernel_le_ker_of_structure M hM
    (hc F M hM) (hq F M hM) (hd F M hM) f hf
  exact ⟨hker, existsUnique_rationalImageRealFunctional M f hker⟩

end Langlands.Plancherel
