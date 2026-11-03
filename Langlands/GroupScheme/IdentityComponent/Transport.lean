import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Functoriality and reductivity transport for identity components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace IdentityComponent

variable {k : Type u} [Field k]
  {H H' H'' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H.X.hom] [IsAffineHom H.X.hom]
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]
  [Smooth H''.X.hom] [IsAffineHom H''.X.hom]

/-- A homomorphism of smooth affine group schemes restricts to their identity components. -/
def map (f : H ⟶ H') : identityComponent H ⟶ identityComponent H' :=
  factor H' (identityComponentι H ≫ f)

@[reassoc (attr := simp)]
theorem map_identityComponentι (f : H ⟶ H') :
    map f ≫ identityComponentι H' = identityComponentι H ≫ f :=
  factor_identityComponentι H' _

@[simp]
theorem map_id : map (𝟙 H) = 𝟙 (identityComponent H) := by
  apply hom_ext_of_isOpenImmersion (identityComponentι H)
  simp

@[simp]
theorem map_comp (f : H ⟶ H') (g : H' ⟶ H'') :
    map (f ≫ g) = map f ≫ map g := by
  apply hom_ext_of_isOpenImmersion (identityComponentι H'')
  simp

/-- An isomorphism of smooth affine group schemes restricts to an isomorphism of their
actual identity components. -/
def mapIso (e : H ≅ H') : identityComponent H ≅ identityComponent H' where
  hom := map e.hom
  inv := map e.inv
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

@[reassoc (attr := simp)]
theorem mapIso_hom_identityComponentι (e : H ≅ H') :
    (mapIso e).hom ≫ identityComponentι H' = identityComponentι H ≫ e.hom :=
  map_identityComponentι e.hom

@[reassoc (attr := simp)]
theorem mapIso_inv_identityComponentι (e : H ≅ H') :
    (mapIso e).inv ≫ identityComponentι H = identityComponentι H' ≫ e.inv :=
  map_identityComponentι e.inv

/-- For a connected smooth affine group scheme, the identity-component inclusion is an
isomorphism. -/
def connectedIso (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left] :
    identityComponent H ≅ H where
  hom := identityComponentι H
  inv := factor H (𝟙 H)
  hom_inv_id := by
    apply hom_ext_of_isOpenImmersion (identityComponentι H)
    simp
  inv_hom_id := factor_identityComponentι H (𝟙 H)

@[simp]
theorem connectedIso_hom (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left] :
    (connectedIso H).hom = identityComponentι H :=
  rfl

/-- Reductivity of the identity component is invariant under an isomorphism of the ambient
smooth affine group schemes. -/
theorem isConnectedReductive_of_iso (e : H ≅ H')
    (h : IsConnectedReductive (identityComponent H')) :
    IsConnectedReductive (identityComponent H) :=
  h.of_iso (mapIso e)

end IdentityComponent

/-- The actual identity component of a connected reductive group is connected reductive. -/
theorem IsConnectedReductive.identityComponent {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))} (h : IsConnectedReductive H) :
    letI : Smooth H.X.hom := h.smooth
    letI : IsAffineHom H.X.hom := h.isAffineHom
    IsConnectedReductive (identityComponent H) := by
  let := h.smooth
  let := h.isAffineHom
  let := h.connectedSpace
  exact h.of_iso (IdentityComponent.connectedIso H)

namespace SubgroupFunctor.IsRepresentedBy

variable {k : Type u} [Field k]
  {G M N : GroupScheme (Spec (CommRingCat.of k))} {F : SubgroupFunctor G}
  {j : M ⟶ G} {i : N ⟶ G}
  [Smooth M.X.hom] [IsAffineHom M.X.hom]
  [Smooth N.X.hom] [IsAffineHom N.X.hom]

/-- Smooth affine representatives of the same subgroup functor have canonically isomorphic
actual identity components. -/
def identityComponentIso (hj : F.IsRepresentedBy j) (hi : F.IsRepresentedBy i) :
    identityComponent M ≅ identityComponent N :=
  IdentityComponent.mapIso (hj.isoOfIsRepresentedBy hi)

@[reassoc (attr := simp)]
theorem identityComponentIso_hom_comp (hj : F.IsRepresentedBy j)
    (hi : F.IsRepresentedBy i) :
    (hj.identityComponentIso hi).hom ≫ identityComponentι N ≫ i =
      identityComponentι M ≫ j := by
  simp only [identityComponentIso,
    IdentityComponent.mapIso_hom_identityComponentι_assoc, isoOfIsRepresentedBy_hom_comp]

/-- Connected reductivity of the identity component depends only on the represented
subgroup functor. -/
theorem isConnectedReductive_identityComponent (hj : F.IsRepresentedBy j)
    (hi : F.IsRepresentedBy i) (hN : IsConnectedReductive (identityComponent N)) :
    IsConnectedReductive (identityComponent M) :=
  hN.of_iso (hj.identityComponentIso hi)

end SubgroupFunctor.IsRepresentedBy

end Langlands.GroupScheme
