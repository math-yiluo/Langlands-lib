import Langlands.GroupScheme.Torus.ZeroDifferential
import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Lie.SplitTorusCoordinates

/-! # Actual tangent vectors of cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- The actual tangent point of the multiplicative group with value `1 + a ε`. -/
def gmInfinitesimal (a : k) : lieKernel (Gm (Spec (CommRingCat.of k))).toGrp k :=
  ⟨(Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k (DualNumber k))).symm
      (splitTorus.infinitesimalUnit k a), by
    apply (Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k k)).injective
    change Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k k)
        (GroupScheme.affinePointMap _
          (CommAlgCat.ofHom (TrivSqZeroExt.fstHom k k k)) _) = _
    rw [Gm.affineUnitsEquiv_naturality, MulEquiv.apply_symm_apply, map_one]
    apply Units.ext
    rfl⟩

@[simp] theorem gmInfinitesimal_value (a : k) :
    Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k (DualNumber k))
      (gmInfinitesimal a).val = splitTorus.infinitesimalUnit k a :=
  MulEquiv.apply_symm_apply _ _

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Differentiate a cocharacter at the actual multiplicative tangent point `1 + ε`. -/
def cocharacterTangent (y : cocharacterLattice T) : lieKernel T.toGrp k :=
  targetMap (CommGroupScheme.groupHom y) k (gmInfinitesimal 1)

/-- A character evaluated on a cocharacter tangent has infinitesimal coefficient equal
to their integral lattice pairing. -/
theorem characterValue_cocharacterTangent (chi : characterLattice T)
    (y : cocharacterLattice T) :
    characterValue chi (cocharacterTangent y).val =
      splitTorus.infinitesimalUnit k (latticePairing T chi y : k) := by
  change Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k (DualNumber k))
    (((gmInfinitesimal (k := k) 1).val ≫ (CommGroupScheme.groupHom y).hom.hom) ≫
      (CommGroupScheme.groupHom chi).hom.hom) = _
  rw [← comp_groupHom_comp]
  conv_lhs => rw [← (gmEndEquiv k).symm_apply_apply (y ≫ chi)]
  rw [gmEndEquiv_symm_comp, map_zpow, gmInfinitesimal_value,
    splitTorus.infinitesimalUnit_zpow, mul_one, latticePairing_apply]

@[simp] theorem characterValue_cocharacterTangent_snd (chi : characterLattice T)
    (y : cocharacterLattice T) :
    (characterValue chi (cocharacterTangent y).val : DualNumber k).snd =
      (latticePairing T chi y : k) := by
  rw [characterValue_cocharacterTangent]
  rfl

/-- Cocharacter tangent points commute with postcomposition. -/
theorem cocharacterTangent_comp
    {T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (y : cocharacterLattice T) (f : T ⟶ T') :
    targetMap (CommGroupScheme.groupHom f) k (cocharacterTangent y) =
      cocharacterTangent (y ≫ f) := by
  apply Subtype.ext
  exact Category.assoc _ _ _

/-- The actual tangent point determines the integral cocharacter in characteristic zero. -/
theorem cocharacterTangent_injective [CharZero k] (hT : IsSplitTorus T.toGrp) :
    Function.Injective (cocharacterTangent (T := T)) := by
  intro y z hyz
  apply hT.hom_ext_of_characters
  intro chi
  apply (gmEndEquiv k).injective
  apply Int.cast_injective (α := k)
  have h := congrArg (fun X : lieKernel T.toGrp k =>
    (characterValue chi X.val : DualNumber k).snd) hyz
  simpa only [characterValue_cocharacterTangent_snd, latticePairing_apply] using h

section Standard

variable (I : Type u) [Fintype I] [DecidableEq I]

local instance : IsAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom :=
  isAffineHom_splitTorus_spec _ I

/-- A coordinate cocharacter differentiates to the corresponding coordinate tangent vector. -/
theorem cocharacterTangent_single (i : I) :
    cocharacterTangent (splitTorus.single (Spec (CommRingCat.of k)) I i) =
      splitTorus.infinitesimalPoint (R := CommRingCat.of k) I k (Pi.single i 1) := by
  apply Subtype.ext
  apply (splitTorus.algebraPointsEquiv I (DualNumber k)).injective
  funext j
  change characterValue (splitTorus.proj (Spec (CommRingCat.of k)) I j)
      (cocharacterTangent (splitTorus.single (Spec (CommRingCat.of k)) I i)).val = _
  rw [characterValue_cocharacterTangent, latticePairing_apply, splitTorus.single_comp_proj]
  simp only [splitTorus.infinitesimalPoint, MulEquiv.apply_symm_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

/-- Coordinate cocharacters span the actual Lie algebra of a standard split torus. -/
theorem span_cocharacterTangent_standard :
    Submodule.span k (Set.range fun y : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) =>
        Additive.ofMul (cocharacterTangent y)) = ⊤ := by
  apply eq_top_iff.mpr
  intro X _
  let e := splitTorus.infinitesimalLinearEquiv (R := CommRingCat.of k) I k
  let v := e.symm X
  have hv : v = ∑ i, v i • (Pi.single i 1 : I → k) := by
    ext j
    simp [Pi.single_apply]
  have hX : X = e v := (e.apply_symm_apply X).symm
  rw [hX, hv, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  change Additive.ofMul (splitTorus.infinitesimalPoint
    (R := CommRingCat.of k) I k (Pi.single i 1)) ∈ _
  rw [← cocharacterTangent_single]
  exact Submodule.subset_span (Set.mem_range_self _)

end Standard

/-- Cocharacter tangent vectors span the actual Lie algebra of every split torus. -/
theorem span_cocharacterTangent [IsAffineHom T.toGrp.X.hom] (hT : IsSplitTorus T.toGrp) :
    Submodule.span k (Set.range fun y : cocharacterLattice T =>
      Additive.ofMul (cocharacterTangent y)) = ⊤ := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let : IsAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom :=
    isAffineHom_splitTorus_spec _ I
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso e
  let S := Submodule.span k (Set.range fun y : cocharacterLattice T =>
    Additive.ofMul (cocharacterTangent y))
  let f := targetMapLinear (CommGroupScheme.groupHom eC.inv) k
  have hle : (⊤ : Submodule k (Additive (lieKernel
      (splitTorus (Spec (CommRingCat.of k)) I) k))) ≤ S.comap f := by
    rw [← span_cocharacterTangent_standard I]
    apply Submodule.span_le.mpr
    rintro _ ⟨y, rfl⟩
    change Additive.ofMul (targetMap (CommGroupScheme.groupHom eC.inv) k
      (cocharacterTangent y)) ∈ S
    rw [cocharacterTangent_comp]
    exact Submodule.subset_span (Set.mem_range_self _)
  apply eq_top_iff.mpr
  intro X _
  have h := hle (show targetMapLinear (CommGroupScheme.groupHom eC.hom) k X ∈ ⊤ from
    Submodule.mem_top)
  change f (targetMapLinear (CommGroupScheme.groupHom eC.hom) k X) ∈ S at h
  convert h using 1
  apply Additive.toMul.injective
  apply Subtype.ext
  change X.toMul.val = (X.toMul.val ≫ e.hom.hom.hom) ≫ e.inv.hom.hom
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
    Grp.id_hom_hom, Category.comp_id]

end Langlands.GroupScheme.Lie
