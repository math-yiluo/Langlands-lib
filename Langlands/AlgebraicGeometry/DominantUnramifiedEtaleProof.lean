import Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement
import Langlands.AlgebraicGeometry.UnramifiedGeometricallyUnibranchLocalCriterionProof
import Mathlib.RingTheory.RingHom.Injective

/-! # Dominant unramified morphisms over geometrically unibranch integral bases -/

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace Langlands.AlgebraicGeometry.DominantUnramifiedEtaleProof

theorem etale_ringHom_of_exists_away
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (h : ∀ q : PrimeSpectrum S, ∃ g : S, g ∉ q.asIdeal ∧
      ((algebraMap S (Localization.Away g)).comp f).Etale) :
    f.Etale := by
  let s : Set S := {g | ((algebraMap S (Localization.Away g)).comp f).Etale}
  have hs : Ideal.span s = ⊤ := by
    by_contra hs
    obtain ⟨q, hq, hsq⟩ := Ideal.exists_le_maximal (Ideal.span s) hs
    obtain ⟨g, hg, he⟩ := h ⟨q, hq.isPrime⟩
    exact hg (hsq (Ideal.subset_span he))
  exact RingHom.Etale.ofLocalizationSpanTarget f s hs (fun g => g.property)

theorem injective_appLE_of_dominant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f]
    {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) [Nonempty V] :
    Function.Injective (f.appLE U V e).hom := by
  have hv : Dense (V : Set X) := V.isOpen.dense (by simpa using ‹Nonempty V›)
  have : IsDominant hV.fromSpec :=
    ⟨by simpa [DenseRange, hV.range_fromSpec] using hv⟩
  have : IsDominant (Spec.map (f.appLE U V e) ≫ hU.fromSpec) := by
    rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e]
    infer_instance
  have hd : IsDominant (Spec.map (f.appLE U V e)) :=
    IsDominant.of_comp_of_isOpenImmersion _ hU.fromSpec
  have hker := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (f.appLE U V e).hom).mp hd.denseRange
  rw [RingHom.injective_iff_ker_eq_bot]
  exact bot_unique (hker.trans (by simp))

theorem dominantUnramifiedEtale_of_localCriterion
    (H : UnramifiedGeometricallyUnibranchLocalCriterionStatement.{u,u,u}) :
    DominantUnramifiedEtaleStatement.{u} := by
  intro X Y _ _ f hY _ _ _
  constructor
  intro U hU V hV e
  apply etale_ringHom_of_exists_away
  intro q
  let x : V := hV.isoSpec.inv q
  have hq : hV.primeIdealOf x = q := by
    exact congrArg (fun k : Spec Γ(X, V) ⟶ Spec Γ(X, V) => k q)
      hV.isoSpec.inv_hom_id
  have : Nonempty V := ⟨x⟩
  have : Nonempty U := ⟨⟨f x, e x.property⟩⟩
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let Rp := Y.presheaf.stalk (f x)
  let : Algebra R S := (f.appLE U V e).hom.toAlgebra
  let : Algebra R Rp := Y.presheaf.algebra_section_stalk ⟨f x, e x.property⟩
  have : Algebra.FiniteType R S := by
    rw [← RingHom.finiteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact f.finiteType_appLE hU hV e
  have : Algebra.FormallyUnramified R S := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact f.formallyUnramified_appLE hU hV e
  have hp : (q.comap (algebraMap R S)).asIdeal =
      (hU.primeIdealOf ⟨f x, e x.property⟩).asIdeal := by
    rw [← hq]
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e x.property)
  have : IsLocalization.AtPrime Rp (q.asIdeal.under R) := by
    change IsLocalization.AtPrime Rp (q.comap (algebraMap R S)).asIdeal
    simpa only [hp] using hU.isLocalization_stalk ⟨f x, e x.property⟩
  obtain ⟨g, hg, he⟩ := H R S Rp q.asIdeal (hY (f x))
    (injective_appLE_of_dominant f hU hV e)
  refine ⟨g, hg, ?_⟩
  exact (RingHom.etale_algebraMap).mpr he

/-- The dominant unramified criterion for arbitrary integral schemes over an
integral geometrically unibranch base. -/
theorem dominantUnramifiedEtale : DominantUnramifiedEtaleStatement.{u} :=
  dominantUnramifiedEtale_of_localCriterion
    UnramifiedGeometricallyUnibranchLocalCriterionProof.unramifiedGeometricallyUnibranchLocalCriterion.{u,u,u}

end Langlands.AlgebraicGeometry.DominantUnramifiedEtaleProof
