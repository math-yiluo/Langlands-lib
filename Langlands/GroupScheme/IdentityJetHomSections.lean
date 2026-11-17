import Langlands.GroupScheme.IdentityJetCoordinates

/-! # Actual identity-jet sections under group homomorphisms -/

noncomputable section

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} {G H K : GroupScheme S}

attribute [local instance] sectionAlgebra

/-- A group homomorphism preserves opens pulled back from its base. -/
theorem hom_preimage (f : H ⟶ G) (U : S.Opens) :
    f.hom.hom.left ⁻¹ᵁ (G.X.hom ⁻¹ᵁ U) = H.X.hom ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, Over.w]

/-- Pullback of actual group functions over an open of the common base. -/
def homGroupSections (f : H ⟶ G) (U : S.Opens) :
    Γ(G.X.left, G.X.hom ⁻¹ᵁ U) →ₐ[Γ(S, U)]
      Γ(H.X.left, H.X.hom ⁻¹ᵁ U) where
  toRingHom := (f.hom.hom.left.appLE _ _ (le_of_eq (hom_preimage f U).symm)).hom
  commutes' r := by
    change (f.hom.hom.left.appLE _ _ _) (G.X.hom.app U r) = H.X.hom.app U r
    have hh := ConcreteCategory.congr_hom
      (Scheme.Hom.comp_appLE f.hom.hom.left G.X.hom U (H.X.hom ⁻¹ᵁ U)
        (le_of_eq (hom_preimage f U).symm)) r
    simpa only [Over.w, Scheme.Hom.appLE_eq_app, CommRingCat.comp_apply] using hh.symm

@[simp]
theorem homGroupSections_id (U : S.Opens) :
    homGroupSections (𝟙 G) U = AlgHom.id Γ(S, U) _ := by
  ext a
  change (𝟙 G.X.left : G.X.left ⟶ G.X.left).appLE _ _ _ a = a
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  have he : (homOfLE (le_of_eq (hom_preimage (𝟙 G) U).symm)).op =
      𝟙 (op (G.X.hom ⁻¹ᵁ U)) := Subsingleton.elim _ _
  rw [he]
  change G.X.left.presheaf.map (𝟙 (op (G.X.hom ⁻¹ᵁ U))) a = a
  exact ConcreteCategory.congr_hom (G.X.left.presheaf.map_id (op (G.X.hom ⁻¹ᵁ U))) a

theorem homGroupSections_comp (f : H ⟶ G) (g : G ⟶ K) (U : S.Opens) :
    homGroupSections (f ≫ g) U =
      (homGroupSections f U).comp (homGroupSections g U) := by
  ext a
  exact (ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE f.hom.hom.left g.hom.hom.left
      (K.X.hom ⁻¹ᵁ U) (G.X.hom ⁻¹ᵁ U) (H.X.hom ⁻¹ᵁ U)
      (le_of_eq (hom_preimage g U).symm) (le_of_eq (hom_preimage f U).symm)) a).symm

/-- Pulling back an ambient function is composition of its actual scheme map. -/
theorem homGroupSections_coordinateMap (f : H ⟶ G) {B : CommRingCat.{u}}
    (j : G.X.left ⟶ Spec B) (U : S.Opens) (a : B) :
    homGroupSections f U (coordinateMap G j U a) =
      coordinateMap H (f.hom.hom.left ≫ j) U a :=
  ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE f.hom.hom.left j ⊤
      (G.X.hom ⁻¹ᵁ U) (H.X.hom ⁻¹ᵁ U) (by simp)
      (le_of_eq (hom_preimage f U).symm)) ((Scheme.ΓSpecIso B).inv a)

/-- Ambient functions vanishing on the identity still vanish after a group map. -/
theorem vanishesAtIdentity_hom (f : H ⟶ G) {B : CommRingCat.{u}}
    (j : G.X.left ⟶ Spec B) (I : Ideal B) (hI : VanishesAtIdentity G j I) :
    VanishesAtIdentity H (f.hom.hom.left ≫ j) I := by
  intro a ha
  simpa only [← Category.assoc, identitySection_naturality] using hI a ha

/-- Pulling group functions back respects evaluation at the actual identity. -/
theorem augmentation_homGroupSections (f : H ⟶ G) (U : S.Opens) :
    (augmentation H U).comp (homGroupSections f U) = augmentation G U := by
  ext a
  change H.identitySection.appLE _ _ _
    (f.hom.hom.left.appLE _ _ _ a) = G.identitySection.appLE _ _ _ a
  have hh := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE H.identitySection f.hom.hom.left
      (G.X.hom ⁻¹ᵁ U) (H.X.hom ⁻¹ᵁ U) U
      (le_of_eq (hom_preimage f U).symm)
      (le_of_eq (identity_preimage H U).symm)) a
  simpa only [identitySection_naturality, CommRingCat.comp_apply] using hh

/-- The actual augmentation-power quotient map induced by a group homomorphism. -/
def homQuotientSections (f : H ⟶ G) (n : ℕ) (U : S.Opens) :
    Algebra.SectionJet.Quotient (augmentation G U) n →ₐ[Γ(S, U)]
      Algebra.SectionJet.Quotient (augmentation H U) n :=
  Ideal.quotientMapₐ _ (homGroupSections f U)
    (Ideal.map_le_iff_le_comap.mp (by
      rw [Ideal.map_pow]
      apply pow_le_pow_left'
      apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      change augmentation H U (homGroupSections f U a) = 0
      have hh := AlgHom.congr_fun (augmentation_homGroupSections f U) a
      exact hh.trans ha))

@[simp]
theorem homQuotientSections_mk (f : H ⟶ G) (n : ℕ) (U : S.Opens)
    (a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) :
    homQuotientSections f n U (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (homGroupSections f U a) := rfl

@[simp]
theorem homQuotientSections_id (n : ℕ) (U : S.Opens) :
    homQuotientSections (𝟙 G) n U = AlgHom.id Γ(S, U) _ := by
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp

theorem homQuotientSections_comp (f : H ⟶ G) (g : G ⟶ K) (n : ℕ) (U : S.Opens) :
    homQuotientSections (f ≫ g) n U =
      (homQuotientSections f n U).comp (homQuotientSections g n U) := by
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp [homGroupSections_comp]

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- The induced linear map on sections of the actual identity neighborhoods. -/
def homSections (f : H ⟶ G) (n : ℕ) (U : S.affineOpens) :
    Γ(module G n, U) →ₗ[Γ(S, U)] Γ(module H n, U) :=
  (sectionsEquiv H n U).symm.toLinearMap.comp
    ((homQuotientSections f n U).toLinearMap.comp (sectionsEquiv G n U).toLinearMap)

@[simp]
theorem sectionsEquiv_homSections (f : H ⟶ G) (n : ℕ) (U : S.affineOpens)
    (x : Γ(module G n, U)) :
    sectionsEquiv H n U (homSections f n U x) =
      homQuotientSections f n U (sectionsEquiv G n U x) :=
  (sectionsEquiv H n U).apply_symm_apply _

/-- The actual jet map is pullback on the restrictions of actual group functions. -/
theorem homSections_quotientMap (f : H ⟶ G) (n : ℕ) (U : S.affineOpens)
    (a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) :
    homSections f n U ((quotientMap G n).app U a) =
      (quotientMap H n).app U (homGroupSections f U a) := by
  apply (sectionsEquiv H n U).injective
  rw [sectionsEquiv_homSections, sectionsEquiv_quotientMap,
    homQuotientSections_mk, sectionsEquiv_quotientMap]

@[simp]
theorem homSections_id (n : ℕ) (U : S.affineOpens) :
    homSections (𝟙 G) n U = LinearMap.id := by
  ext x
  apply (sectionsEquiv G n U).injective
  simp

theorem homSections_comp [IsAffineHom K.X.hom]
    (f : H ⟶ G) (g : G ⟶ K) (n : ℕ) (U : S.affineOpens) :
    homSections (f ≫ g) n U = (homSections f n U).comp (homSections g n U) := by
  ext x
  apply (sectionsEquiv H n U).injective
  simp [homQuotientSections_comp]

/-- A group-scheme isomorphism induces an equivalence of actual affine jet sections. -/
def isoSections (e : H ≅ G) (n : ℕ) (U : S.affineOpens) :
    Γ(module G n, U) ≃ₗ[Γ(S, U)] Γ(module H n, U) :=
  LinearEquiv.ofLinearMap (homSections e.hom n U) (homSections e.inv n U)
    (by rw [← homSections_comp, e.hom_inv_id, homSections_id])
    (by rw [← homSections_comp, e.inv_hom_id, homSections_id])

@[simp]
theorem isoSections_apply (e : H ≅ G) (n : ℕ) (U : S.affineOpens)
    (x : Γ(module G n, U)) :
    isoSections e n U x = homSections e.hom n U x := rfl

/-- Actual ambient quotient-coordinate sections are preserved by group pullback. -/
theorem homSections_restrict_quotientCoordinates
    (f : H ⟶ G) {B : CommRingCat.{u}} (j : G.X.left ⟶ Spec B)
    (I : Ideal B) (hI : VanishesAtIdentity G j I)
    (n : ℕ) (U : S.affineOpens) (z : B ⧸ I ^ (n + 1)) :
    homSections f n U
      ((module G n).presheaf.map
        (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
          (quotientCoordinates G j I hI n z)) =
      (module H n).presheaf.map
        (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
          (quotientCoordinates H (f.hom.hom.left ≫ j) I
            (vanishesAtIdentity_hom f j I hI) n z) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply (sectionsEquiv H n U).injective
  rw [sectionsEquiv_homSections, sectionsEquiv_restrict_quotientCoordinates,
    homQuotientSections_mk, homGroupSections_coordinateMap,
    sectionsEquiv_restrict_quotientCoordinates]

end Langlands.GroupScheme.IdentityJet
