import Langlands.GroupScheme.Dynamic.AffineExtension
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk

/-! # Orbit extensions into proper schemes over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace AffineLine

variable {k : Type u} [Field k]

/-- The stalk of `Spec k[X]` at a point whose prime contains `X` is a valuation ring. -/
theorem valuationRing_stalk_of_X_mem (x : Spec (CommRingCat.of (Polynomial k)))
    (hx : (Polynomial.X : Polynomial k) ∈ x.asIdeal) :
    ValuationRing ((Spec (CommRingCat.of (Polynomial k))).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := x.isPrime
  let _ : Algebra (Polynomial k) ((Spec (CommRingCat.of (Polynomial k))).presheaf.stalk x) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of (Polynomial k)) x
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of (Polynomial k))).presheaf.stalk x)
      x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (Polynomial k)) x
  have : IsDomain ((Spec (CommRingCat.of (Polynomial k))).presheaf.stalk x) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      ((Spec (CommRingCat.of (Polynomial k))).presheaf.stalk x)
      (Ideal.primeCompl_le_nonZeroDivisors x.asIdeal)
  have hne : x.asIdeal ≠ ⊥ := fun h => Polynomial.X_ne_zero (h ▸ hx)
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k) hne
    ((Spec (CommRingCat.of (Polynomial k))).presheaf.stalk x)
  infer_instance

/-- A morphism `Spec k[X, X⁻¹] ⟶ Y` over `k` into a proper `k`-scheme extends over
`Spec k[X]`. -/
theorem exists_polynomial_extension_of_isProper {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (CommRingCat.of k)) [IsProper sY]
    (φ : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ Y)
    (hφ : φ ≫ sY = Spec.map (polynomialToLaurent (CommRingCat.of k)) ≫
      Spec.map (polynomialC (CommRingCat.of k))) :
    ∃ ψ : Spec (CommRingCat.of (Polynomial k)) ⟶ Y,
      Spec.map (polynomialToLaurent (CommRingCat.of k)) ≫ ψ = φ ∧
        ψ ≫ sY = Spec.map (polynomialC (CommRingCat.of k)) := by
  let X := Spec (CommRingCat.of (Polynomial k))
  let ι : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ X :=
    Spec.map (polynomialToLaurent (CommRingCat.of k))
  have : IsOpenImmersion ι :=
    IsOpenImmersion.of_isLocalization (R := Polynomial k) (S := LaurentPolynomial k)
      Polynomial.X
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from sY]; infer_instance⟩
  have hE : ValuativeCriterion.Existence sY := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) sY := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  have hrange (x : X) (hx : (Polynomial.X : Polynomial k) ∉ x.asIdeal) : x ∈ ι.opensRange := by
    have hr := PrimeSpectrum.localization_away_comap_range (LaurentPolynomial k)
      (Polynomial.X : Polynomial k)
    have hb : x ∈ (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) :
        Set (PrimeSpectrum (Polynomial k))) := hx
    rw [← hr] at hb
    obtain ⟨y, hy⟩ := hb
    exact ⟨y, hy⟩
  have hdense : Dense (ι.opensRange : Set X) := by
    refine ι.opensRange.isOpen.dense ⟨⟨⊥, Ideal.isPrime_bot⟩, hrange _ ?_⟩
    exact Polynomial.X_ne_zero
  let g : X.PartialMap Y := ⟨ι.opensRange, hdense, ι.isoOpensRange.inv ≫ φ⟩
  have hg : g.hom ≫ sY = g.domain.ι ≫ Spec.map (polynomialC (CommRingCat.of k)) := by
    change (ι.isoOpensRange.inv ≫ φ) ≫ sY = ι.opensRange.ι ≫ _
    rw [Category.assoc, hφ, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  have hdom : g.toRationalMap.domain = ⊤ := by
    refine top_unique fun x _ => ?_
    by_cases hx : (Polynomial.X : Polynomial k) ∈ x.asIdeal
    · exact Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk
        (Spec.map (polynomialC (CommRingCat.of k))) sY hE g hg x
        (valuationRing_stalk_of_X_mem x hx)
    · exact g.le_domain_toRationalMap (hrange x hx)
  let h := g.toRationalMap.toPartialMap
  have hdom' : h.domain = ⊤ := hdom
  let ψ : X ⟶ Y := X.topIso.inv ≫ X.homOfLE hdom'.ge ≫ h.hom
  have hres : X.homOfLE (U := g.domain) (V := h.domain) g.le_domain_toRationalMap ≫ h.hom =
      g.hom :=
    g.toPartialMap_toRationalMap_restrict
  have hψ : ι ≫ ψ = φ := by
    have hle : ι.opensRange.ι ≫ X.topIso.inv ≫ X.homOfLE hdom'.ge =
        X.homOfLE (U := g.domain) (V := h.domain) g.le_domain_toRationalMap := by
      rw [← cancel_mono h.domain.ι, Category.assoc, Category.assoc,
        Scheme.homOfLE_ι, Scheme.toIso_inv_ι, Category.comp_id]
      exact (X.homOfLE_ι _).symm
    calc ι ≫ ψ
        = ι.isoOpensRange.hom ≫ (ι.opensRange.ι ≫ X.topIso.inv ≫ X.homOfLE hdom'.ge) ≫
            h.hom := by
          simp only [ψ, Category.assoc]
          rw [← Category.assoc ι.isoOpensRange.hom, Scheme.Hom.isoOpensRange_hom_ι]
      _ = ι.isoOpensRange.hom ≫ g.hom := by
          rw [hle, hres]
      _ = φ := Iso.hom_inv_id_assoc _ _
  refine ⟨ψ, hψ, ?_⟩
  have : IsSchemeTheoreticallyDominant ι :=
    isSchemeTheoreticallyDominant_specMap Polynomial.toLaurent_injective
  refine ext_of_isSchemeTheoreticallyDominant (terminal.from _) (terminal.hom_ext _ _) ι ?_
  rw [reassoc_of% hψ, hφ]

/-- A `𝔾_m`-orbit map into a proper scheme over a field extends over `𝔸¹`. -/
theorem exists_extension_of_isProper (Q : Over (Spec (CommRingCat.of k))) [IsProper Q.hom]
    (o : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗ (Gm (Spec (CommRingCat.of k))).X ⟶ Q) :
    ∃ e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗ scheme (Spec (CommRingCat.of k)) ⟶ Q,
      Over.mk (𝟙 (Spec (CommRingCat.of k))) ◁ unitInclusion (Spec (CommRingCat.of k)) ≫ e =
        o := by
  let f := 𝟙 (Spec (CommRingCat.of k))
  obtain ⟨ψ, hψ, hψQ⟩ := exists_polynomial_extension_of_isProper Q.hom
    (laurentPoint f ≫ o).left (by rw [Over.w (laurentPoint f ≫ o)]; simp [f])
  let e' : polynomialScheme f ⟶ Q := Over.homMk ψ (by rw [hψQ]; simp [f])
  exact ⟨polynomialPointInv f ≫ e',
    whiskerLeft_comp_of_laurentInclusion f (Over.OverMorphism.ext hψ)⟩

end AffineLine

end Langlands.GroupScheme
