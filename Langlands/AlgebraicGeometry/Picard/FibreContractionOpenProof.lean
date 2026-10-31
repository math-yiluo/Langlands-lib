import Langlands.AlgebraicGeometry.Picard.FibreContractionOpenStatement
import Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctionsProof

/-! # Openness of the locus where a morphism contracts the fibres of an abelian scheme -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

/-- A morphism to an affine scheme factors through a given morphism to an affine spectrum
when the latter induces an isomorphism on global sections. -/
lemma exists_factor_of_isIso_appTop {F W : Scheme.{u}} {K : CommRingCat.{u}}
    (π : F ⟶ Spec K) [IsIso π.appTop] [IsAffine W] (h : F ⟶ W) :
    ∃ g : Spec K ⟶ W, h = π ≫ g := by
  refine ⟨(Spec K).toSpecΓ ≫ inv (Spec.map π.appTop) ≫ Spec.map h.appTop ≫ W.isoSpec.inv, ?_⟩
  have h1 : h = F.toSpecΓ ≫ Spec.map h.appTop ≫ W.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id,
      Category.comp_id]
  have h2 : F.toSpecΓ = π ≫ (Spec K).toSpecΓ ≫ inv (Spec.map π.appTop) := by
    rw [Scheme.toSpecΓ_naturality_assoc, IsIso.hom_inv_id, Category.comp_id]
  conv_lhs => rw [h1]
  rw [h2]
  simp only [Category.assoc]

variable {Y Z : Scheme.{u}} (B : AbelianScheme Y) (Ψ : B.X.left ⟶ Z)

/-- If `Ψ` maps the fibre of `B` over `y` into an affine open subset, then `Ψ` is constant
on that fibre, with the value it takes on the unit section. -/
lemma apply_eq_of_fibre_subset_affine (y : Y) (V : Z.Opens) (hV : IsAffineOpen V)
    (hfib : ∀ x, B.X.hom x = y → Ψ x ∈ V) (x : B.X.left) (hx : B.X.hom x = y) :
    Ψ x = Ψ (unitSection B y) := by
  let s := Y.fromSpecResidueField y
  let Fs : Scheme.{u} := pullback B.X.hom s
  let π : Fs ⟶ Spec (Y.residueField y) := pullback.snd B.X.hom s
  have : IsIso π.appTop :=
    Langlands.AlgebraicGeometry.fieldSmoothProperConnectedGlobalFunctions
      (Y.residueField y) _ π inferInstance inferInstance inferInstance
  let Ψs : Fs ⟶ Z := pullback.fst B.X.hom s ≫ Ψ
  have hrange : Set.range Ψs ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    apply hfib
    change (pullback.fst B.X.hom s ≫ B.X.hom) w = y
    rw [pullback.condition]
    simp [s]
  have : IsAffine V := hV
  obtain ⟨g, hg⟩ := exists_factor_of_isIso_appTop π (IsOpenImmersion.lift V.ι Ψs hrange)
  have hΨs : Ψs = π ≫ g ≫ V.ι := by
    rw [← Category.assoc, ← hg, IsOpenImmersion.lift_fac]
  let p0 : Spec (Y.residueField y) := IsLocalRing.closedPoint _
  let z : Fs := (pullback.lift (s ≫ unitSection B) (𝟙 _)
    (by rw [Category.assoc, unitSection_comp, Category.comp_id, Category.id_comp]) :
      Spec (Y.residueField y) ⟶ Fs) p0
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.X.hom) (g := s)
    x p0 (by rw [hx]; exact (Scheme.fromSpecResidueField_apply y p0).symm)
  have key : ∀ w' : Fs, Ψs w' = (g ≫ V.ι) p0 := by
    intro w'
    rw [hΨs, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have e1 : Ψ x = Ψs w := by
    simp only [Ψs, Scheme.Hom.comp_apply, hw1]
  have e2 : Ψ (unitSection B y) = Ψs z := by
    simp only [Ψs, z, ← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
      Function.comp_apply, s, Scheme.fromSpecResidueField_apply]
  rw [e1, e2, key, key]

/-- The set of points over which `Ψ` sends the whole fibre to a point `z₀` is open,
provided `Ψ` sends the unit section to `z₀`. -/
theorem isOpen_setOf_fibre_eq (z₀ : Z) (h0 : ∀ y, Ψ (unitSection B y) = z₀) :
    IsOpen {y : Y | ∀ x, B.X.hom x = y → Ψ x = z₀} := by
  rw [isOpen_iff_forall_mem_open]
  intro y₀ hy₀
  obtain ⟨_, ⟨V, hV, rfl⟩, hz₀V, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z₀) isOpen_univ
  let F : Set B.X.left := (Ψ ⁻¹' (V : Set Z))ᶜ
  have hF : IsClosed F := (V.isOpen.preimage Ψ.continuous).isClosed_compl
  have hC : IsClosed (B.X.hom '' F) := B.X.hom.isClosedMap F hF
  refine ⟨(B.X.hom '' F)ᶜ, ?_, hC.isOpen_compl, ?_⟩
  · intro y hy x hx
    rw [apply_eq_of_fibre_subset_affine B Ψ y V hV ?_ x hx, h0]
    intro x' hx'
    by_contra hcon
    exact hy ⟨x', hcon, hx'⟩
  · rintro ⟨x, hxF, hx⟩
    exact hxF (by rw [Set.mem_preimage, hy₀ x hx]; exact hz₀V)

/-- The published statement `FibreContractionOpenStatement`. -/
theorem fibreContractionOpen : FibreContractionOpenStatement.{u} :=
  fun _ _ B Ψ z₀ h0 => isOpen_setOf_fibre_eq B Ψ z₀ h0

end Langlands.AbelianScheme
