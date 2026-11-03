import Langlands.GroupScheme.CentralIsogeny.Transport

/-! # Algebraically simply connected semisimple groups and covering interfaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G H C C' : GroupScheme (Spec (CommRingCat.of k))}

/-- Algebraic simple connectedness for semisimple field groups: every incoming central
isogeny from a semisimple group is an isomorphism. -/
structure IsSimplyConnected (G : GroupScheme (Spec (CommRingCat.of k))) : Prop where
  isSemisimple : IsSemisimple G
  central_isogeny_isIso : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (f : H ⟶ G),
    IsSemisimple H → IsCentralIsogeny f → IsIso f

/-- Algebraic simple connectedness is preserved under isomorphism. -/
theorem IsSimplyConnected.of_iso (e : G ≅ H) (h : IsSimplyConnected H) :
    IsSimplyConnected G := by
  refine ⟨h.isSemisimple.of_iso e, ?_⟩
  intro C f hC hf
  have : IsIso (f ≫ e.hom) := h.central_isogeny_isIso C _ hC (hf.comp_iso e)
  exact IsIso.of_isIso_comp_right f e.hom

/-- The isomorphism-invariance comparison in both directions. -/
theorem isSimplyConnected_iff_of_iso (e : G ≅ H) :
    IsSimplyConnected G ↔ IsSimplyConnected H :=
  ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

/-- The universal property of a semisimple central cover: a unique factorization through
every incoming central isogeny from a semisimple group. -/
def HasCentralCoverUniversalProperty (π : C ⟶ G) : Prop :=
  ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (q : H ⟶ G),
    IsSemisimple H → IsCentralIsogeny q → ∃! a : C ⟶ H, a ≫ q = π

/-- An actual simply connected central cover, with its universal property explicit.
This predicate asserts properties of the supplied map and chooses no covering group. -/
structure IsSimplyConnectedCover (π : C ⟶ G) : Prop where
  isSemisimple : IsSemisimple G
  isSimplyConnected : IsSimplyConnected C
  isCentralIsogeny : IsCentralIsogeny π
  universal : HasCentralCoverUniversalProperty π

namespace IsSimplyConnectedCover

variable {π : C ⟶ G} (hπ : IsSimplyConnectedCover π)

/-- The actual factorization through another semisimple central cover. -/
def lift {H : GroupScheme (Spec (CommRingCat.of k))} {q : H ⟶ G}
    (hH : IsSemisimple H) (hq : IsCentralIsogeny q) : C ⟶ H :=
  (hπ.universal H q hH hq).choose

/-- The chosen factorization commutes with the two covering maps. -/
@[reassoc]
theorem lift_comp {H : GroupScheme (Spec (CommRingCat.of k))} {q : H ⟶ G}
    (hH : IsSemisimple H) (hq : IsCentralIsogeny q) :
    hπ.lift hH hq ≫ q = π :=
  (hπ.universal H q hH hq).choose_spec.1

/-- Every factorization through a fixed semisimple central cover is the chosen one. -/
theorem lift_unique {H : GroupScheme (Spec (CommRingCat.of k))} {q : H ⟶ G}
    (hH : IsSemisimple H) (hq : IsCentralIsogeny q) (a : C ⟶ H) (ha : a ≫ q = π) :
    a = hπ.lift hH hq :=
  (hπ.universal H q hH hq).choose_spec.2 a ha

include hπ in
/-- Factorizations through a fixed semisimple central cover are unique. -/
theorem hom_ext {H : GroupScheme (Spec (CommRingCat.of k))} {q : H ⟶ G}
    (hH : IsSemisimple H) (hq : IsCentralIsogeny q) {a b : C ⟶ H}
    (ha : a ≫ q = π) (hb : b ≫ q = π) : a = b :=
  (hπ.lift_unique hH hq a ha).trans (hπ.lift_unique hH hq b hb).symm

/-- Two actual simply connected covers are canonically isomorphic over their target. -/
def iso {π' : C' ⟶ G} (hπ' : IsSimplyConnectedCover π') : C ≅ C' where
  hom := hπ.lift hπ'.isSimplyConnected.isSemisimple hπ'.isCentralIsogeny
  inv := hπ'.lift hπ.isSimplyConnected.isSemisimple hπ.isCentralIsogeny
  hom_inv_id := by
    apply hπ.hom_ext hπ.isSimplyConnected.isSemisimple hπ.isCentralIsogeny
    · rw [Category.assoc, lift_comp, lift_comp]
    · exact Category.id_comp _
  inv_hom_id := by
    apply hπ'.hom_ext hπ'.isSimplyConnected.isSemisimple hπ'.isCentralIsogeny
    · rw [Category.assoc, lift_comp, lift_comp]
    · exact Category.id_comp _

/-- The canonical isomorphism commutes with the covering maps. -/
@[reassoc]
theorem iso_hom_comp {π' : C' ⟶ G} (hπ' : IsSimplyConnectedCover π') :
    (hπ.iso hπ').hom ≫ π' = π :=
  hπ.lift_comp hπ'.isSimplyConnected.isSemisimple hπ'.isCentralIsogeny

/-- Compatibility with the target determines the isomorphism uniquely. -/
theorem iso_unique {π' : C' ⟶ G} (hπ' : IsSimplyConnectedCover π')
    (e : C ≅ C') (he : e.hom ≫ π' = π) : e = hπ.iso hπ' := by
  apply Iso.ext
  exact hπ.lift_unique hπ'.isSimplyConnected.isSemisimple hπ'.isCentralIsogeny e.hom he

end IsSimplyConnectedCover

end Langlands.GroupScheme
