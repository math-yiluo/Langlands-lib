import Langlands.BruhatTits.RationalPoints.SplitTorusDerivedAnnihilation
import Langlands.Representation.Plancherel.TorusSplitNormFactorization
import Langlands.Representation.Plancherel.TorusNormKernelCompactnessStatement
import Langlands.GroupScheme.Rational.RootReflectionExistenceStatement
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.Weil.Representation.ContinuityProof

/-! # Conditional annihilation of tori contained in the actual derived subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.RationalPoints

section Reflections

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (s : S.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono s.hom.hom.left]

/-- Integral normalizer data give the reflection predicate used by the torus norm. -/
theorem isRelativeReflection_of_integralData (D : RelativeRootReflectionData s)
    (a : relativeRoots s) :
    IsRelativeReflection s a.val (QuotientGroup.mk (D.representative a)) := by
  have hf : RelativeRootSystem.corootFunctional s (D.coroot a)
      (RelativeRootSystem.rootVector s a) = 2 := by
    rw [RelativeRootSystem.corootFunctional_rootVector, D.pair_self]
    norm_num
  refine ⟨a.property, RelativeRootSystem.corootFunctional s (D.coroot a), hf, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range (RelativeRootSystem.span_range_rootVector s)
  intro b
  change relativeWeylAction s (QuotientGroup.mk (D.representative a))
      (RelativeRootSystem.rootVector s b) =
    Module.reflection hf (RelativeRootSystem.rootVector s b)
  rw [Module.reflection_apply]
  exact (D.reflection_rootVector a b).symm

end Reflections

section TorusImages

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  [IsAffineHom G.X.hom]

local instance torusDerivedSmoothAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance torusDerivedSmoothTorusAffine : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
local instance torusDerivedSmoothAmbientTopology : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance torusDerivedSmoothTorusTopology : TopologicalSpace (rationalPoints T.toGrp) :=
  rationalPointTopology F T.toGrp.X

/-- Under the two structural inputs, every point of a closed torus contained
in the actual derived subgroup has trivial ambient smooth real image. -/
theorem torusImage_eq_one_of_structure
    (hG : IsConnectedReductive G)
    (hnorm : Langlands.Plancherel.TorusNormKernelCompactnessStatement.{u})
    (href : RelativeRootReflectionExistenceStatement.{u})
    (j : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) (hj : IsClosedSubgroup j)
    (hderived : SubgroupFunctor.range j ≤ derivedSubgroup G)
    (f : rationalPoints G →* Multiplicative ℝ)
    (hf : IsOpen (f.ker : Set (rationalPoints G))) (x : rationalPoints T.toGrp) :
    f (rationalPoints.map j x) = 1 := by
  let : Smooth G.X.hom := hG.smooth
  let K := Langlands.Plancherel.rationalCommonNormKernel T.toGrp
  let : IsTopologicalGroup (rationalPoints T.toGrp) :=
    rationalPoint_isTopologicalGroup F T.toGrp
  let : CompactSpace K := isCompact_iff_compactSpace.mp (hnorm F T.toGrp hT)
  let g : K →* Multiplicative ℝ :=
    f.comp ((rationalPoints.map j).comp K.subtype)
  have hg : IsOpen (g.ker : Set K) :=
    hf.preimage ((continuous_rationalPointMap F j.hom.hom).comp continuous_subtype_val)
  have hfin := Langlands.Weil.finite_range_of_open_kernel g hg
  let : Finite g.range := hfin.to_subtype
  have hK (z : K) : f (rationalPoints.map j (z : rationalPoints T.toGrp)) = 1 := by
    have ht := isOfFinOrder_of_finite (g.rangeRestrict z)
    obtain ⟨N, hN, hpow⟩ := ht.exists_pow_eq_one
    apply (isOfFinOrder_iff_eq_one _).mp
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨N, hN, congrArg (fun a : g.range => (a : Multiplicative ℝ)) hpow⟩
  obtain ⟨A, i, hi⟩ := exists_maximalSplitTorus T.toGrp
  obtain ⟨S, s, hs, b, hb⟩ := exists_maximalSplitTorus_extension G (i ≫ j)
    (hi.isSplitSubtorus.comp hj)
  let := hs.isSplitSubtorus.mono
  obtain ⟨D, _⟩ := href F G hG S s hs
  obtain ⟨a, z, hfact⟩ := Langlands.Plancherel.exists_split_mul_commonNormKernel i hT hi x
  have hpoint : rationalPoints.map s (rationalPoints.map b a) =
      rationalPoints.map j (rationalPoints.map i a) := by
    change (a ≫ b.hom.hom) ≫ s.hom.hom = (a ≫ i.hom.hom) ≫ j.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hb]
    rfl
  have hsplit : f (rationalPoints.map j (rationalPoints.map i a)) = 1 := by
    rw [← hpoint]
    apply map_eq_one_of_maximalSplitTorus_mem_derived s f _ hG hs
    · intro root hroot
      exact ⟨_, isRelativeReflection_of_integralData s D ⟨root, hroot⟩⟩
    · rw [hpoint]
      exact (SubgroupFunctor.le_def.mp hderived (Over.mk (𝟙 _)))
        ⟨rationalPoints.map i a, rfl⟩
  have hpow : (f (rationalPoints.map j x)) ^ Langlands.Plancherel.splitNormExponent i = 1 := by
    rw [← map_pow, ← map_pow, hfact, map_mul, map_mul, hsplit, hK, one_mul]
  apply (isOfFinOrder_iff_eq_one _).mp
  exact isOfFinOrder_iff_pow_eq_one.mpr
    ⟨_, Langlands.Plancherel.splitNormExponent_pos i hi.isSplitSubtorus, hpow⟩

/-- The actual torus point map, with values in the ambient real kernel,
under explicit norm-kernel compactness and reflection-existence premises. -/
def torusImageToOpenRealKernel
    (hG : IsConnectedReductive G)
    (hnorm : Langlands.Plancherel.TorusNormKernelCompactnessStatement.{u})
    (href : RelativeRootReflectionExistenceStatement.{u})
    (j : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) (hj : IsClosedSubgroup j)
    (hderived : SubgroupFunctor.range j ≤ derivedSubgroup G)
    (f : rationalPoints G →* Multiplicative ℝ)
    (hf : IsOpen (f.ker : Set (rationalPoints G))) :
    rationalPoints T.toGrp →* f.ker :=
  (rationalPoints.map j).codRestrict f.ker
    (fun x => torusImage_eq_one_of_structure hG hnorm href j hT hj hderived f hf x)

@[simp]
theorem torusImageToOpenRealKernel_coe
    (hG : IsConnectedReductive G)
    (hnorm : Langlands.Plancherel.TorusNormKernelCompactnessStatement.{u})
    (href : RelativeRootReflectionExistenceStatement.{u})
    (j : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) (hj : IsClosedSubgroup j)
    (hderived : SubgroupFunctor.range j ≤ derivedSubgroup G)
    (f : rationalPoints G →* Multiplicative ℝ)
    (hf : IsOpen (f.ker : Set (rationalPoints G))) (x : rationalPoints T.toGrp) :
    (torusImageToOpenRealKernel hG hnorm href j hT hj hderived f hf x :
      rationalPoints G) = rationalPoints.map j x := rfl

end TorusImages

end Langlands.BruhatTits.RationalPoints
