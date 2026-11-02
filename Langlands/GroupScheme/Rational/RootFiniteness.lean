import Langlands.GroupScheme.Rational.Statement
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Conditional finiteness of the actual relative roots and Weyl group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

private theorem rootPairing_indexHom_injective
    {J R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (P : RootPairing J R M N) [P.IsRootSystem] :
    Function.Injective (RootPairing.Equiv.indexHom P) := by
  intro f g h
  apply RootPairing.Equiv.weightHom_injective P
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range (RootPairing.IsRootSystem.span_root_eq_top (P := P))
  intro j
  change f.toHom.weightMap (P.root j) = g.toHom.weightMap (P.root j)
  rw [RootPairing.Hom.root_weightMap_apply, RootPairing.Hom.root_weightMap_apply]
  exact congrArg P.root (congrFun (congrArg Equiv.toFun h) j)

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Rationalization is injective on the character lattice of a split torus. -/
theorem IsSplitTorus.character_toRat_injective (hT : IsSplitTorus T.toGrp) :
    Function.Injective (toRat : characterLattice T → ℚ ⊗[ℤ] characterLattice T) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  have := hI
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  exact toRat_injective
    ((characterLattice.congr eC).trans (splitTorus.characterLatticeEquiv k I))

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- The actual relative Weyl quotient is finite under the published root-system hypothesis. -/
theorem HasRelativeRootSystem.finite_relativeWeylGroup (h : HasRelativeRootSystem i) :
    Finite (relativeWeylGroup i) := by
  obtain ⟨J, hJ, P, hP, _, _, _, hW, hfaithful⟩ := h
  have := hJ
  have := hP
  have : Finite P.Aut :=
    Finite.of_injective (RootPairing.Equiv.indexHom P) (rootPairing_indexHom_injective P)
  apply (Set.finite_range_iff hfaithful).mp
  rw [← MonoidHom.coe_range, ← hW, Subgroup.coe_map]
  exact (Set.toFinite _).image _

/-- The actual character-valued relative roots are finite when the torus is split
and the published root-system hypothesis holds. -/
theorem HasRelativeRootSystem.finite_relativeRoots
    (h : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp) :
    (relativeRoots i).Finite := by
  obtain ⟨J, hJ, P, _, _, _, hroots, _, _⟩ := h
  have := hJ
  apply (Set.finite_image_iff hT.character_toRat_injective.injOn).mp
  rw [← hroots]
  exact (Set.finite_range P.root).image Subtype.val

/-- Positivity for any cocharacter selects a finite subset of the actual relative roots. -/
theorem HasRelativeRootSystem.finite_positiveRelativeRoots
    (h : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp) (ν : cocharacterLattice T) :
    (positiveRelativeRoots i ν).Finite :=
  (h.finite_relativeRoots i hT).subset (positiveRelativeRoots_subset_relativeRoots i ν)

/-- The actual indecomposable positive relative roots are finite for any cocharacter. -/
theorem HasRelativeRootSystem.finite_simpleRelativeRoots
    (h : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp) (ν : cocharacterLattice T) :
    (simpleRelativeRoots i ν).Finite :=
  (h.finite_positiveRelativeRoots i hT ν).subset (simpleRelativeRoots_subset_positive i ν)

/-- A finite enumeration of the actual relative Weyl group, with its original quotient type. -/
@[instance_reducible]
def relativeWeylGroupFintype (h : HasRelativeRootSystem i) :
    Fintype (relativeWeylGroup i) :=
  letI := h.finite_relativeWeylGroup i
  Fintype.ofFinite _

/-- A finite enumeration of the actual character-valued relative roots. -/
@[instance_reducible]
def relativeRootFintype (h : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp) :
    Fintype (relativeRoots i) :=
  (h.finite_relativeRoots i hT).fintype

/-- A finite enumeration of the actual simple roots selected by the given cocharacter. -/
@[instance_reducible]
def simpleRelativeRootFintype (h : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T) : Fintype (simpleRelativeRoots i ν) :=
  (h.finite_simpleRelativeRoots i hT ν).fintype

/-- Each actual standard-Levi Weyl subgroup is finite under the same Weyl hypothesis. -/
@[instance_reducible]
def standardRelativeWeylGroupFintype (h : HasRelativeRootSystem i)
    (ν : cocharacterLattice T) (J : Set (characterLattice T)) :
    Fintype (standardRelativeWeylGroup i ν J) :=
  letI := h.finite_relativeWeylGroup i
  Fintype.ofFinite _

end Langlands.GroupScheme
