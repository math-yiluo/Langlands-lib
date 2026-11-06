import Langlands.GroupScheme.Reductive.GeometricRootCentralizerNeighbourhood
import Langlands.GroupScheme.Rational.ReflectionNegation

/-! # Actual geometric reflection data from integral normalizer reflections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

section Field

variable (k : Type u) [Field k] (I : Type u) [Fintype I] [DecidableEq I]
  {H : GroupScheme (Spec (CommRingCat.of k))}
  (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ H)

/-- The actual group-scheme automorphism induced by a specified normalizing
point of the standard torus. -/
def normalizingGroupIso (n : normalizerPoints (T := commGroupScheme _ I) j) :
    splitTorus (Spec (CommRingCat.of k)) I ≅ splitTorus (Spec (CommRingCat.of k)) I where
  hom := CommGroupScheme.groupHom (normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j n).hom
  inv := CommGroupScheme.groupHom (normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j n).inv
  hom_inv_id := congrArg CommGroupScheme.groupHom (normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j n).hom_inv_id
  inv_hom_id := congrArg CommGroupScheme.groupHom (normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j n).inv_hom_id

/-- The integral coordinate pullback of the actual normalizing automorphism. -/
def normalizingCoordinateIso (n : normalizerPoints (T := commGroupScheme _ I) j) :
    (I → ℤ) ≃ₗ[ℤ] (I → ℤ) :=
  characterCoordinateIso k I (normalizingGroupIso k I j n)

/-- Integral extension recovers the same actual normalizing automorphism at
the original field, with no choice of another representative. -/
theorem exponentIso_normalizingCoordinateIso_hom
    (n : normalizerPoints (T := commGroupScheme _ I) j) :
    (exponentIso (Spec (CommRingCat.of k)) I (normalizingCoordinateIso k I j n)).hom =
      CommGroupScheme.groupHom (normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j n).hom :=
  fieldAutomorphismExtension_hom k I (normalizingGroupIso k I j n)

variable [Mono j.hom.hom.left] [IsAffineHom H.X.hom]
  (D : RelativeRootReflectionData (T := commGroupScheme _ I) j)

omit [DecidableEq I] in
/-- The direct normalizing automorphism negates the specified actual root,
despite the inverse-precomposition convention for the Weyl action. -/
theorem normalizingAut_inverts_root (a : relativeRoots (T := commGroupScheme _ I) j) :
    (normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j (D.representative a)).hom ≫ a.val = -a.val := by
  have hinv : (normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j (D.representative a)).inv ≫ a.val = -a.val := by
    rw [← weylAction_apply (T := commGroupScheme (Spec (CommRingCat.of k)) I), D.action, D.pair_self, two_zsmul]
    abel
  calc
    _ = (normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j (D.representative a)).hom ≫
        (-((normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j (D.representative a)).inv ≫ a.val)) := by
      rw [hinv, neg_neg]
    _ = -a.val := by simp

omit [DecidableEq I] in
/-- The integral coordinates of the actual normalizing automorphism invert
the root's exact integral coordinate vector. -/
theorem normalizingCoordinateIso_inverts_root
    (a : relativeRoots (T := commGroupScheme _ I) j) :
    normalizingCoordinateIso k I j (D.representative a)
        (characterLatticeEquiv k I a.val) = -characterLatticeEquiv k I a.val := by
  change characterMap I I (normalizingGroupIso k I j (D.representative a)).hom
    (characterLatticeEquiv k I a.val) = _
  rw [characterMap_equiv]
  change characterLatticeEquiv k I
    ((normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j (D.representative a)).hom ≫ a.val) = _
  rw [normalizingAut_inverts_root k I j D]
  exact (characterLatticeEquiv k I).map_neg a.val

omit [DecidableEq I] in
/-- Every actual cocharacter annihilating the root is fixed by its actual
normalizing automorphism. The formula on the entire character lattice is used. -/
theorem normalizingAut_fixes_cocharacter
    (a : relativeRoots (T := commGroupScheme _ I) j)
    (ν : cocharacterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (hν : latticePairing (commGroupScheme _ I) a.val ν = 0) :
    ν ≫ (normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j (D.representative a)).hom = ν := by
  have hzero : ν ≫ a.val = 0 := by
    apply (gmEndEquiv k).injective
    rw [map_zero]
    exact hν
  have hinv : ν ≫ (normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j (D.representative a)).inv = ν := by
    apply hom_ext_projections _ I
    intro q
    rw [Category.assoc, ← weylAction_apply (T := commGroupScheme (Spec (CommRingCat.of k)) I), D.action,
      Preadditive.comp_sub, Preadditive.comp_zsmul, hzero, smul_zero, sub_zero]
  have h := congrArg (fun f => f ≫ (normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j (D.representative a)).hom) hinv
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.symm

/-- The fixed-cocharacter equation holds for the integral-coordinate extension
over its original field. -/
theorem normalizingCoordinateIso_fixes_cocharacter
    (a : relativeRoots (T := commGroupScheme _ I) j)
    (ν : cocharacterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (hν : latticePairing (commGroupScheme _ I) a.val ν = 0) :
    CommGroupScheme.groupHom ν ≫
        (exponentIso (Spec (CommRingCat.of k)) I
          (normalizingCoordinateIso k I j (D.representative a))).hom =
      CommGroupScheme.groupHom ν := by
  rw [exponentIso_normalizingCoordinateIso_hom]
  exact congrArg CommGroupScheme.groupHom (normalizingAut_fixes_cocharacter k I j D a ν hν)

/-- The original representative satisfies the all-test transporter equation
for its constructed integral-coordinate automorphism. -/
theorem normalizingCoordinateIso_isTransporter
    (a : relativeRoots (T := commGroupScheme _ I) j) :
    PointwiseSchemeAction.IsTransporter
      ((exponentIso (Spec (CommRingCat.of k)) I
        (normalizingCoordinateIso k I j (D.representative a))).hom ≫ j) j
      (D.representative a).val := by
  rw [exponentIso_normalizingCoordinateIso_hom]
  exact (isNormalizingPoint_normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j (D.representative a)).isTransporter

end Field

section Geometric

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance reflectionConstruction_smooth_geometricFiber (s : Spec (CommRingCat.of r)) :
    Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance reflectionConstruction_affine_geometricFiber (s : Spec (CommRingCat.of r)) :
    IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

variable [hi : IsClosedImmersion i.hom.hom.left] (s : Spec (CommRingCat.of r))

local instance reflectionConstruction_mono :
    Mono (geometricIdentityComponentHom I G i s).hom.hom.left := by
  let : IsClosedImmersion (geometricIdentityComponentHom I G i s).hom.hom.left :=
    isClosedSubgroup_geometricIdentityComponentHom I G i hi s
  infer_instance

variable (D : RelativeRootReflectionData (T := commGroupScheme _ I)
  (geometricIdentityComponentHom I G i s))

include hi D

/-- The actual forward field reflection data construct the geometric
reflection record, including its fixed generic annihilating cocharacter. -/
def geometricRootReflectionDataOfField
    (m : I → ℤ) (hm : m ∈ geometricExponentRoots I G i s) :
    GeometricRootReflectionData I G i s m hm := by
  let k := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)
  let j := geometricIdentityComponentHom I G i s
  let a : relativeRoots (T := commGroupScheme _ I) j := ⟨exponentCharacter _ I m, hm⟩
  refine
    { automorphism := normalizingCoordinateIso k I j (D.representative a)
      inverts := ?_
      fixesCocharacter := ?_
      point := (D.representative a).val
      transports := normalizingCoordinateIso_isTransporter k I j D a }
  · have h := normalizingCoordinateIso_inverts_root k I j D a
    dsimp only [k, a] at h
    simpa only [k, a, exponentCharacter_eq_characterLatticeEquiv_symm,
      AddEquiv.apply_symm_apply] using h
  · apply normalizingCoordinateIso_fixes_cocharacter k I j D a
    change latticePairing (commGroupScheme _ I) (exponentCharacter _ I m)
      (exponentCocharacter _ I (rootCentralizerVector I G i s m hm)) = 0
    rw [latticePairing_exponentCharacter_exponentCocharacter]
    exact dot_rootCentralizerVector I G i s m hm

omit [DecidableEq I] in
/-- Forward integral normalizer reflection data already imply negation of the
full actual geometric exponent-root set. -/
theorem neg_mem_geometricExponentRoots_of_fieldReflectionData
    (m : I → ℤ) (hm : m ∈ geometricExponentRoots I G i s) :
    -m ∈ geometricExponentRoots I G i s := by
  have h := D.neg_mem_relativeRoots (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s) hm
  change exponentCharacterLinear _ I (-m) ∈ roots _
  rw [map_neg]
  exact h

/-- Actual field reflection data construct every coordinate reflection, every
root-centralizer good open and the resulting original-base good open. -/
def identityComponentReductiveNeighbourhood_of_fieldReflectionData
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i)
    (hred : ∀ m ∈ geometricExponentRoots I G i s,
      ∀ a ∈ geometricExponentRoots I G i s,
      ¬ LinearIndependent ℤ ![
        exponentCharacter
          (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I m,
        exponentCharacter
          (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I a] →
        a = m ∨ a = -m)
    (hlines : ∀ m ∈ geometricExponentRoots I G i s, exponentWeightRank I G i m s = 1) :
    IdentityComponentReductiveOpenNeighbourhood G s :=
  identityComponentReductiveNeighbourhood_of_geometricRootReflections I G i hi s hself
    (neg_mem_geometricExponentRoots_of_fieldReflectionData I G i s D) hred hlines
    (fun m hm => ⟨geometricRootReflectionDataOfField I G i s D m hm⟩)

end Geometric

end Langlands.GroupScheme.splitTorus
