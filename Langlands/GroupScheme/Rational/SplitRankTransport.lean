import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Torus.Lattice
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Transport and finite-rank comparison for split subtori -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

section ClosedSubgroups

variable {S : Scheme.{u}} {H H' G G' : GroupScheme S}

/-- A composite of closed-subgroup homomorphisms is a closed-subgroup homomorphism. -/
theorem IsClosedSubgroup.comp {i : H ⟶ G} {j : G ⟶ G'}
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j) : IsClosedSubgroup (i ≫ j) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion j.hom.hom.left := hj
  change IsClosedImmersion (i.hom.hom.left ≫ j.hom.hom.left)
  infer_instance

/-- Postcomposition by an isomorphism preserves closed subgroups. -/
theorem IsClosedSubgroup.comp_iso {i : H ⟶ G} (hi : IsClosedSubgroup i) (e : G ≅ G') :
    IsClosedSubgroup (i ≫ e.hom) :=
  hi.comp (IsClosedSubgroup.of_iso e)

/-- Closedness is invariant under an isomorphism of the ambient group. -/
theorem IsClosedSubgroup.comp_iso_iff (i : H ⟶ G) (e : G ≅ G') :
    IsClosedSubgroup (i ≫ e.hom) ↔ IsClosedSubgroup i := by
  constructor
  · intro hi
    simpa using hi.comp_iso e.symm
  · exact fun hi => hi.comp_iso e

end ClosedSubgroups

section SplitSubtori

variable {k : Type u} [Field k]
variable {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
variable {G G' : GroupScheme (Spec (CommRingCat.of k))}

/-- Split-subtorus structure is invariant under an isomorphism of the ambient group. -/
theorem IsSplitSubtorus.comp_iso_iff (i : T.toGrp ⟶ G) (e : G ≅ G') :
    IsSplitSubtorus (i ≫ e.hom) ↔ IsSplitSubtorus i := by
  simp only [IsSplitSubtorus, IsClosedSubgroup.comp_iso_iff]

/-- Maximal split tori are preserved by ambient group isomorphisms. -/
theorem IsMaximalSplitTorus.comp_iso {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (e : G ≅ G') : IsMaximalSplitTorus (i ≫ e.hom) := by
  refine ⟨(IsSplitSubtorus.comp_iso_iff i e).2 hi.1, ?_⟩
  intro T' i' hi' f hf
  apply hi.2 T' (i' ≫ e.inv)
    ((IsSplitSubtorus.comp_iso_iff i' e.symm).2 hi') f
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun a => a ≫ e.inv) hf

/-- Maximal split-torus structure is invariant under an isomorphism of the ambient group. -/
theorem IsMaximalSplitTorus.comp_iso_iff (i : T.toGrp ⟶ G) (e : G ≅ G') :
    IsMaximalSplitTorus (i ≫ e.hom) ↔ IsMaximalSplitTorus i := by
  constructor
  · intro hi
    simpa using hi.comp_iso e.symm
  · exact fun hi => hi.comp_iso e

/-- The split rank increases under a closed immersion of group schemes. -/
theorem splitRank_le_of_isClosedSubgroup (j : G ⟶ G') (hj : IsClosedSubgroup j) :
    splitRank G ≤ splitRank G' := by
  refine iSup_le fun I => iSup_le fun _ => iSup_le fun i => iSup_le fun hi => ?_
  exact card_le_splitRank I (i ≫ j) (hi.comp hj)

/-- Isomorphic group schemes have the same split rank. -/
theorem splitRank_eq_of_iso (e : G ≅ G') : splitRank G = splitRank G' :=
  le_antisymm
    (splitRank_le_of_isClosedSubgroup e.hom (IsClosedSubgroup.of_iso e))
    (splitRank_le_of_isClosedSubgroup e.inv (IsClosedSubgroup.of_iso e.symm))

end SplitSubtori

namespace splitTorus

variable {k : Type u} [Field k] (I J : Type u) [Finite I] [Finite J]
local notation "S" => Spec (CommRingCat.of k)
local notation "TI" => splitTorus.commGroupScheme S I
local notation "TJ" => splitTorus.commGroupScheme S J

/-- In split-torus coordinates, postcomposition gives an integral linear map on cocharacters. -/
def cocharacterMap (f : splitTorus S I ⟶ splitTorus S J) : (I → ℤ) →ₗ[ℤ] (J → ℤ) :=
  (((cocharacterLatticeEquiv k J).toAddMonoidHom.comp
    { toFun := fun ν : cocharacterLattice TI => ν ≫ Additive.ofMul f
      map_zero' := by simp
      map_add' := fun ν μ => Preadditive.add_comp _ _ _ _ _ _ }).comp
    (cocharacterLatticeEquiv k I).symm.toAddMonoidHom).toIntLinearMap

/-- A monomorphism of split tori induces an injective map on cocharacters. -/
theorem cocharacterMap_injective (f : splitTorus S I ⟶ splitTorus S J)
    [Mono f.hom.hom] : Function.Injective (cocharacterMap I J f) := by
  intro x y h
  apply (cocharacterLatticeEquiv k I).symm.injective
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  apply (cancel_mono f.hom.hom).mp
  have h' := (cocharacterLatticeEquiv k J).injective h
  exact congrArg (fun ν : cocharacterLattice TJ => ν.toMul.hom.hom) h'

/-- A monomorphism between finite split tori cannot decrease their number of factors. -/
theorem card_le_card_of_mono (f : splitTorus S I ⟶ splitTorus S J) [Mono f.hom.hom] :
    Nat.card I ≤ Nat.card J := by
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using
    LinearMap.finrank_le_finrank_of_injective (cocharacterMap_injective I J f)

/-- A closed immersion between finite split tori cannot decrease their number of factors. -/
theorem card_le_card_of_isClosedSubgroup (f : splitTorus S I ⟶ splitTorus S J)
    (hf : IsClosedSubgroup f) : Nat.card I ≤ Nat.card J := by
  let : IsClosedImmersion f.hom.hom.left := hf
  let : Mono f.hom.hom := Over.mono_of_mono_left _
  exact card_le_card_of_mono I J f

/-- The number of factors in a finite split torus over a field is invariant under isomorphism. -/
theorem card_eq_card_of_iso (e : splitTorus S I ≅ splitTorus S J) : Nat.card I = Nat.card J := by
  apply le_antisymm
  · exact card_le_card_of_isClosedSubgroup I J e.hom (IsClosedSubgroup.of_iso e)
  · exact card_le_card_of_isClosedSubgroup J I e.inv (IsClosedSubgroup.of_iso e.symm)

end splitTorus

end Langlands.GroupScheme
