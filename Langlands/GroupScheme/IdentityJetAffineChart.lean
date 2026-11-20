import Langlands.GroupScheme.IdentityJetFiniteProjection
import Langlands.GroupScheme.MatrixRepresentation.LocalCentralKernelReduction

/-! # Identity jets inside an affine open containing the unit section -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdentityJet

section General

variable {S : Scheme.{u}} (G : GroupScheme S) [IsSeparated G.X.hom] (n : ℕ)
  (V : G.X.left.affineOpens) (hV : G.identitySection ⁻¹ᵁ V.1 = ⊤)

include hV in
/-- The identity jet lies inside every open containing the unit section. -/
theorem inclusion_preimage_eq_top : inclusion G n ⁻¹ᵁ V.1 = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  have hx : inclusion G n x ∈ Set.range G.identitySection :=
    range_inclusion_eq_range_identitySection G n ▸ ⟨x, rfl⟩
  obtain ⟨t, ht⟩ := hx
  change inclusion G n x ∈ V.1
  rw [← ht]
  have : t ∈ G.identitySection ⁻¹ᵁ V.1 := hV ▸ trivial
  exact this

include hV in
theorem isIso_subschemeCover_map : IsIso ((ideal G n).subschemeCover.f V) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
  exact inclusion_preimage_eq_top G n V hV

/-- The identity jet is the spectrum of the quotient of the functions on an affine open
containing the unit section by the jet ideal. -/
def affineChartIso :
    scheme G n ≅ Spec (CommRingCat.of (Γ(G.X.left, V.1) ⧸ (ideal G n).ideal V)) :=
  have := isIso_subschemeCover_map G n V hV
  (asIso ((ideal G n).subschemeCover.f V)).symm

theorem affineChartIso_inv_inclusion :
    (affineChartIso G n V hV).inv ≫ inclusion G n =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ V.2.fromSpec := by
  change (ideal G n).subschemeCover.f V ≫ (ideal G n).subschemeι = _
  rw [Scheme.IdealSheafData.subschemeCover_map_subschemeι,
    Scheme.IdealSheafData.glueDataObjι_ι]

omit hV in
/-- The jet ideal on an affine open is the power of the kernel of evaluation at the unit. -/
theorem ideal_ideal_eq :
    (ideal G n).ideal V = (RingHom.ker (G.identitySection.app V.1).hom) ^ (n + 1) := by
  have : IsClosedImmersion G.identitySection := isClosedImmersion_identitySection G
  change (G.identitySection.ker ^ (n + 1)).ideal V = _
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply]

end General

section AffineBase

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
  [IsSeparated G.X.hom] (n : ℕ) (V : G.X.left.affineOpens)
  (hV : G.identitySection ⁻¹ᵁ V.1 = ⊤)

/-- Functions on `V` as an algebra over the base ring. -/
def chartRingHom : R →+* Γ(G.X.left, V.1) :=
  (G.X.hom.appLE ⊤ V.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- Evaluation at the unit section, as a ring map to the base ring. -/
def chartAugmentation : Γ(G.X.left, V.1) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (G.identitySection.appLE V.1 ⊤ hV.ge).hom

omit [IsSeparated G.X.hom] in
private theorem appLE_eq_id_of_eq_id {X : Scheme.{u}} (q : X ⟶ X) (hq : q = 𝟙 X)
    (h : (⊤ : X.Opens) ≤ q ⁻¹ᵁ ⊤) : q.appLE ⊤ ⊤ h = 𝟙 _ := by
  subst hq
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  exact X.presheaf.map_id _

omit [IsSeparated G.X.hom] in
theorem chartAugmentation_chartRingHom (r : R) :
    chartAugmentation G V hV (chartRingHom G V r) = r := by
  have h := Scheme.Hom.appLE_comp_appLE G.identitySection G.X.hom ⊤ V.1 ⊤ le_top hV.ge
  rw [appLE_eq_id_of_eq_id _ (G.identitySection_comp)] at h
  have h₂ := congrArg (fun φ : Γ(Spec (CommRingCat.of R), ⊤) ⟶ Γ(Spec (CommRingCat.of R), ⊤) =>
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom (φ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) h
  simp only [CommRingCat.comp_apply, CommRingCat.id_apply, Iso.inv_hom_id_apply] at h₂
  exact h₂

omit [IsSeparated G.X.hom] in
theorem ker_chartAugmentation :
    RingHom.ker (chartAugmentation G V hV) = RingHom.ker (G.identitySection.app V.1).hom := by
  rw [chartAugmentation, RingHom.ker_comp_of_injective _
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective]
  change RingHom.ker (((Spec (CommRingCat.of R)).presheaf.map (homOfLE hV.ge).op).hom.comp
    (G.identitySection.app V.1).hom) = _
  apply RingHom.ker_comp_of_injective
  intro a b hab
  have hinv : ∀ x, (Spec (CommRingCat.of R)).presheaf.map (homOfLE (le_top :
      G.identitySection ⁻¹ᵁ V.1 ≤ ⊤)).op
      ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hV.ge).op x) = x := by
    intro x
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    have : (homOfLE hV.ge).op ≫ (homOfLE (le_top : G.identitySection ⁻¹ᵁ V.1 ≤ ⊤)).op =
        𝟙 _ := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  rw [← hinv a, ← hinv b, hab]

theorem ideal_eq_ker_chartAugmentation_pow :
    (ideal G n).ideal V = RingHom.ker (chartAugmentation G V hV) ^ (n + 1) := by
  rw [ideal_ideal_eq, ker_chartAugmentation]

omit [IsSeparated G.X.hom] in
theorem smooth_chartRingHom [Smooth G.X.hom] : (chartRingHom G V).Smooth :=
  RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective)
    (G.X.hom.smooth_appLE (isAffineOpen_top _) V.2 le_top)

/-- The coordinate ring of the jet in the affine chart, as an algebra over the base. -/
def chartJetAlgebra : CommAlgCat.{u} R :=
  letI := (chartRingHom G V).toAlgebra
  CommAlgCat.of R (Γ(G.X.left, V.1) ⧸ (ideal G n).ideal V)

include hV in
theorem chartJetAlgebra_finite_projective [Smooth G.X.hom] :
    Module.Finite R (chartJetAlgebra G n V) ∧ Module.Projective R (chartJetAlgebra G n V) := by
  let := (chartRingHom G V).toAlgebra
  have : Algebra.Smooth R Γ(G.X.left, V.1) := (smooth_chartRingHom G V).toAlgebra
  let ε : Γ(G.X.left, V.1) →ₐ[R] R :=
    { chartAugmentation G V hV with
      commutes' := chartAugmentation_chartRingHom G V hV }
  have hε : RingHom.ker ε = RingHom.ker (chartAugmentation G V hV) := rfl
  obtain ⟨hfin, hproj⟩ := Algebra.FormallySmooth.finite_projective_quotient_ker_pow ε n
  let φ := Ideal.quotientEquivAlgOfEq R
    (show RingHom.ker ε ^ (n + 1) = (ideal G n).ideal V by
      rw [hε, ideal_eq_ker_chartAugmentation_pow G n V hV])
  exact ⟨Module.Finite.equiv φ.toLinearEquiv, Module.Projective.of_equiv φ.toLinearEquiv⟩

/-- The identity jet as the spectrum of the chart jet algebra. -/
def chartJetIso : scheme G n ≅ Spec (CommRingCat.of (chartJetAlgebra G n V)) :=
  affineChartIso G n V hV

theorem chartJetIso_projection :
    (chartJetIso G n V hV).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (chartJetAlgebra G n V))) =
      projection G n := by
  rw [← Iso.eq_inv_comp]
  change _ = (affineChartIso G n V hV).inv ≫ inclusion G n ≫ G.X.hom
  rw [← Category.assoc, affineChartIso_inv_inclusion, Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec G.X.hom (isAffineOpen_top _) V.2 le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
  rfl

end AffineBase

end Langlands.GroupScheme.IdentityJet
