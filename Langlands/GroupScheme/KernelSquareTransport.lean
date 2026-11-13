import Langlands.GroupScheme.Unipotent.KernelCoordinateTransport
import Langlands.GroupScheme.KernelRepresentativeTransport

/-! # Scheme-theoretic kernels under an isomorphism of arrows -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H G' H' : GroupScheme S}

/-- An isomorphism of the source and target of a group-scheme homomorphism
induces an isomorphism of its actual scheme-theoretic kernel. -/
def kernelSquareIso (q : G ⟶ H) (q' : G' ⟶ H') (e : G ≅ G') (d : H ≅ H')
    (h : e.hom ≫ q' = q ≫ d.hom) : kernel q ≅ kernel q' where
  hom := pullback.map _ _ _ _ e.hom (𝟙 _) d.hom h.symm (by
    apply Grp.hom_ext
    change η[H.X] ≫ d.hom.hom.hom = 𝟙 _ ≫ η[H'.X]
    simpa only [Category.id_comp] using (IsMonHom.one_hom d.hom.hom.hom))
  inv := pullback.map _ _ _ _ e.inv (𝟙 _) d.inv (by
    apply (cancel_mono d.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← h, Iso.inv_hom_id_assoc]) (by
    apply Grp.hom_ext
    change η[H'.X] ≫ d.inv.hom.hom = 𝟙 _ ≫ η[H.X]
    simpa only [Category.id_comp] using (IsMonHom.one_hom d.inv.hom.hom))
  hom_inv_id := by
    apply pullback.hom_ext <;> simp [pullback.map, Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;> simp [pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem kernelSquareIso_hom_ι (q : G ⟶ H) (q' : G' ⟶ H')
    (e : G ≅ G') (d : H ≅ H') (h : e.hom ≫ q' = q ≫ d.hom) :
    (kernelSquareIso q q' e d h).hom ≫ kernelι q' = kernelι q ≫ e.hom := by
  simp [kernelSquareIso, kernelι, pullback.map]

/-- Smoothness and connectedness transfer over the unchanged base through
an isomorphism of actual group schemes. -/
theorem smooth_connected_of_groupIso {A B : GroupScheme S} (e : A ≅ B)
    (hs : Smooth B.X.hom) (hc : ConnectedSpace B.X.left) :
    Smooth A.X.hom ∧ ConnectedSpace A.X.left := by
  let eo := (Grp.forget (Over S)).mapIso e
  let ex := (Over.forget S).mapIso eo
  have : IsIso eo.hom.left := (Over.forget S).map_isIso eo.hom
  let : Smooth ((Grp.forget (Over S)).obj B).hom := hs
  constructor
  · change Smooth ((Grp.forget (Over S)).obj A).hom
    rw [← eo.hom.w]
    infer_instance
  · exact (Scheme.homeoOfIso ex).connectedSpace_iff.2 hc

section Field

variable {k : Type u} [Field k]
  {A B : GroupScheme (Spec (CommRingCat.of k))}

/-- The three geometric properties needed by the parahoric kernel theorem
are invariant under isomorphism of the actual group schemes. -/
theorem smooth_connected_unipotent_of_groupIso (e : A ≅ B)
    (hB : Smooth B.X.hom ∧ ConnectedSpace B.X.left ∧ IsUnipotent B) :
    Smooth A.X.hom ∧ ConnectedSpace A.X.left ∧ IsUnipotent A := by
  have h := smooth_connected_of_groupIso e hB.1 hB.2.1
  exact ⟨h.1, h.2, hB.2.2.of_iso e⟩

end Field

end Langlands.GroupScheme
