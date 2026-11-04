import Langlands.Geometry.Building.CrossTorusApartmentComparison

/-! # Identity and composition for actual apartment transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme

/-- Two actual transport squares compose to the square for the composite isomorphisms. -/
theorem torusTransport_composition_square {B : Scheme.{u}}
    {S S' S'' : CommGroupScheme B} {G H K : GroupScheme B}
    {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H} {l : S''.toGrp ⟶ K}
    (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (e' : S' ≅ S'') (f' : H ≅ K)
    (h' : j ≫ f'.hom = CommGroupScheme.groupHom e'.hom ≫ l) :
    i ≫ (f ≪≫ f').hom = CommGroupScheme.groupHom (e ≪≫ e').hom ≫ l := by
  change i ≫ (f.hom ≫ f'.hom) = _
  rw [← Category.assoc i f.hom f'.hom, h, Category.assoc, h']
  rfl

/-- The identity isomorphisms give the identity transport square. -/
theorem torusTransport_identity_square {B : Scheme.{u}}
    {S : CommGroupScheme B} {G : GroupScheme B} (i : S.toGrp ⟶ G) :
    i ≫ (Iso.refl G).hom = CommGroupScheme.groupHom (Iso.refl S).hom ≫ i := by
  change i ≫ 𝟙 G = 𝟙 S.toGrp ≫ i
  simp only [Category.comp_id, Category.id_comp]

namespace RealTorusSpace

variable {k : Type u} [Field k]
  {S S' S'' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Actual real cocharacter transport respects identity. -/
@[simp] theorem cocharacterRealCongr_refl (v : V S) :
    cocharacterRealCongr (Iso.refl S) v = v := by
  induction v using TensorProduct.inductionOn with
  | tmul r ν => simp only [cocharacterRealCongr_tmul, Iso.refl_hom, Category.comp_id]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- Actual real cocharacter transport respects composition in its original order. -/
theorem cocharacterRealCongr_trans (e : S ≅ S') (e' : S' ≅ S'') (v : V S) :
    cocharacterRealCongr e' (cocharacterRealCongr e v) =
      cocharacterRealCongr (e ≪≫ e') v := by
  induction v using TensorProduct.inductionOn with
  | tmul r ν => simp only [cocharacterRealCongr_tmul, Iso.trans_hom, Category.assoc]
  | add v w hv hw => simp only [map_add, hv, hw]

end RealTorusSpace
end Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S S' S'' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H K : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H} {l : S''.toGrp ⟶ K}

namespace RootFunctionFamily

/-- Identity transport retains the full family at every character and point. -/
@[simp] theorem transportEquiv_refl (φ : RootFunctionFamily S G) :
    transportEquiv (Iso.refl S) (Iso.refl G) φ = φ := by
  ext a g
  simp only [transportEquiv_apply, characterLattice.congr_symm_apply, Iso.refl_hom,
    Iso.refl_inv, Category.id_comp, rationalPoints.map_apply, Grp.id_hom_hom,
    Category.comp_id]

/-- Two successive full-family transports agree with direct composite transport. -/
theorem transportEquiv_trans (e : S ≅ S') (f : G ≅ H)
    (e' : S' ≅ S'') (f' : H ≅ K) (φ : RootFunctionFamily S G) :
    transportEquiv e' f' (transportEquiv e f φ) =
      transportEquiv (e ≪≫ e') (f ≪≫ f') φ := by
  ext a g
  simp only [transportEquiv_apply, characterLattice.congr_symm_apply, Iso.trans_hom,
    Iso.trans_inv, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

end RootFunctionFamily

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]

/-- Quotient translation transport respects identity on representatives and hence on all points. -/
@[simp] theorem translationSpaceTransportEquiv_refl (v : TranslationSpace i) :
    translationSpaceTransportEquiv (Iso.refl S) (Iso.refl G)
      (torusTransport_identity_square i) v = v := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  rw [translationSpaceTransportEquiv_mk, cocharacterRealCongr_refl]

variable (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
  (e' : S' ≅ S'') (f' : H ≅ K)
  (h' : j ≫ f'.hom = CommGroupScheme.groupHom e'.hom ≫ l)

/-- The reduced translation derivative respects the same composite square. -/
theorem translationSpaceTransportEquiv_trans (v : TranslationSpace i) :
    translationSpaceTransportEquiv e' f' h' (translationSpaceTransportEquiv e f h v) =
      translationSpaceTransportEquiv (e ≪≫ e') (f ≪≫ f')
        (torusTransport_composition_square e f h e' f' h') v := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  rw [translationSpaceTransportEquiv_mk, translationSpaceTransportEquiv_mk,
    translationSpaceTransportEquiv_mk, cocharacterRealCongr_trans]

namespace KPApartmentData

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left] [Mono l.hom.hom.left]
  {ω : kˣ → ℝ}

/-- Identity transport fixes the entire supplied apartment data. -/
@[simp] theorem transport_refl (D : KPApartmentData i ω) :
    D.transport (Iso.refl S) (Iso.refl G) (torusTransport_identity_square i) = D := by
  apply ext
  ext φ
  change φ ∈ RootFunctionFamily.transportEquiv (Iso.refl S) (Iso.refl G) '' D.carrier ↔
    φ ∈ D.carrier
  simp only [Set.mem_image, RootFunctionFamily.transportEquiv_refl, exists_eq_right]

/-- Successive transport agrees with direct transport for the entire compatible orbit data. -/
theorem transport_trans (D : KPApartmentData i ω) :
    (D.transport e f h).transport e' f' h' =
      D.transport (e ≪≫ e') (f ≪≫ f')
        (torusTransport_composition_square e f h e' f' h') := by
  apply ext
  ext φ
  change φ ∈ RootFunctionFamily.transportEquiv e' f' ''
      (RootFunctionFamily.transportEquiv e f '' D.carrier) ↔
    φ ∈ RootFunctionFamily.transportEquiv (e ≪≫ e') (f ≪≫ f') '' D.carrier
  rw [Set.image_image]
  simp only [RootFunctionFamily.transportEquiv_trans]

/-- Compare successive and direct transported apartments by retaining their actual families. -/
def apartmentTransportComposition (D : KPApartmentData i ω) :
    ((D.transport e f h).transport e' f' h').Apartment ≃ᵃ[ℝ]
      (D.transport (e ≪≫ e') (f ≪≫ f')
        (torusTransport_composition_square e f h e' f' h')).Apartment :=
  apartmentAffineEquivOfCarrierEq _ _
    (congrArg KPApartmentData.carrier (D.transport_trans e f h e' f' h'))

/-- The composition comparison is the identity on the original target families. -/
@[simp] theorem apartmentTransportComposition_val (D : KPApartmentData i ω)
    (x : ((D.transport e f h).transport e' f' h').Apartment) :
    (D.apartmentTransportComposition e f h e' f' h' x).val = x.val := rfl

/-- Both target apartments have the same reduced translation space; the derivative is identity. -/
@[simp] theorem apartmentTransportComposition_linear (D : KPApartmentData i ω) :
    (D.apartmentTransportComposition e f h e' f' h').linear =
      LinearEquiv.refl ℝ (TranslationSpace l) := rfl

/-- After the comparison, the two actual point transports equal direct transport. -/
theorem apartmentTransportComposition_apply (D : KPApartmentData i ω) (x : D.Apartment) :
    D.apartmentTransportComposition e f h e' f' h'
        ((D.transport e f h).apartmentTransportAffineEquiv e' f' h'
          (D.apartmentTransportAffineEquiv e f h x)) =
      D.apartmentTransportAffineEquiv (e ≪≫ e') (f ≪≫ f')
        (torusTransport_composition_square e f h e' f' h') x := by
  apply Apartment.ext
  exact RootFunctionFamily.transportEquiv_trans e f e' f' x.val

/-- Equality of actual affine maps, including their reduced derivatives. -/
theorem apartmentTransportAffineEquiv_trans (D : KPApartmentData i ω) :
    ((D.apartmentTransportAffineEquiv e f h).trans
      ((D.transport e f h).apartmentTransportAffineEquiv e' f' h')).trans
        (D.apartmentTransportComposition e f h e' f' h') =
      D.apartmentTransportAffineEquiv (e ≪≫ e') (f ≪≫ f')
        (torusTransport_composition_square e f h e' f' h') := by
  apply AffineEquiv.ext
  exact D.apartmentTransportComposition_apply e f h e' f' h'

/-- Identify the identity-transported apartment with the original apartment. -/
def apartmentTransportIdentity (D : KPApartmentData i ω) :
    (D.transport (Iso.refl S) (Iso.refl G) (torusTransport_identity_square i)).Apartment ≃ᵃ[ℝ]
      D.Apartment :=
  apartmentAffineEquivOfCarrierEq _ _ (congrArg KPApartmentData.carrier (D.transport_refl))

/-- Identity comparison retains each full family. -/
@[simp] theorem apartmentTransportIdentity_val (D : KPApartmentData i ω)
    (x : (D.transport (Iso.refl S) (Iso.refl G)
      (torusTransport_identity_square i)).Apartment) :
    (D.apartmentTransportIdentity x).val = x.val := rfl

/-- The identity comparison also has the identity reduced derivative. -/
@[simp] theorem apartmentTransportIdentity_linear (D : KPApartmentData i ω) :
    D.apartmentTransportIdentity.linear = LinearEquiv.refl ℝ (TranslationSpace i) := rfl

/-- Actual identity transport followed by the comparison is the identity affine automorphism. -/
theorem apartmentTransportAffineEquiv_refl (D : KPApartmentData i ω) :
    (D.apartmentTransportAffineEquiv (Iso.refl S) (Iso.refl G)
      (torusTransport_identity_square i)).trans D.apartmentTransportIdentity =
        AffineEquiv.refl ℝ D.Apartment := by
  apply AffineEquiv.ext
  intro x
  apply Apartment.ext
  exact RootFunctionFamily.transportEquiv_refl x.val

end KPApartmentData
end Langlands.Geometry.Building
