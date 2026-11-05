import Langlands.GroupScheme.Dynamic.ProperAffineExtension

/-! # Affine-line lifts through proper morphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineLine

variable {k : Type u} [Field k]

/-- A punctured affine-line lift through a proper morphism extends over zero. -/
theorem exists_polynomial_lift_of_isProper {Y Z : Scheme.{u}}
    [Y.IsSeparated] [Z.IsSeparated] (q : Y ⟶ Z) [IsProper q]
    (r : Spec (CommRingCat.of (Polynomial k)) ⟶ Z)
    (c : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ Y)
    (hc : c ≫ q = Spec.map (polynomialToLaurent (CommRingCat.of k)) ≫ r) :
    ∃ e : Spec (CommRingCat.of (Polynomial k)) ⟶ Y,
      Spec.map (polynomialToLaurent (CommRingCat.of k)) ≫ e = c ∧ e ≫ q = r := by
  let X := Spec (CommRingCat.of (Polynomial k))
  let jUnit : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ X :=
    Spec.map (polynomialToLaurent (CommRingCat.of k))
  have : IsOpenImmersion jUnit :=
    IsOpenImmersion.of_isLocalization (R := Polynomial k) (S := LaurentPolynomial k)
      Polynomial.X
  have hE : ValuativeCriterion.Existence q := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) q := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  have hrange (x : X) (hx : (Polynomial.X : Polynomial k) ∉ x.asIdeal) :
      x ∈ jUnit.opensRange := by
    have hr := PrimeSpectrum.localization_away_comap_range (LaurentPolynomial k)
      (Polynomial.X : Polynomial k)
    have hb : x ∈ (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) :
        Set (PrimeSpectrum (Polynomial k))) := hx
    rw [← hr] at hb
    obtain ⟨y, hy⟩ := hb
    exact ⟨y, hy⟩
  have hdense : Dense (jUnit.opensRange : Set X) := by
    refine jUnit.opensRange.isOpen.dense ⟨⟨⊥, Ideal.isPrime_bot⟩, hrange _ ?_⟩
    exact Polynomial.X_ne_zero
  let g : X.PartialMap Y := ⟨jUnit.opensRange, hdense, jUnit.isoOpensRange.inv ≫ c⟩
  have hg : g.hom ≫ q = g.domain.ι ≫ r := by
    change (jUnit.isoOpensRange.inv ≫ c) ≫ q = jUnit.opensRange.ι ≫ r
    rw [Category.assoc, hc, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  have hdom : g.toRationalMap.domain = ⊤ := by
    refine top_unique fun x _ => ?_
    by_cases hx : (Polynomial.X : Polynomial k) ∈ x.asIdeal
    · exact Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk
        r q hE g hg x (valuationRing_stalk_of_X_mem x hx)
    · exact g.le_domain_toRationalMap (hrange x hx)
  let h := g.toRationalMap.toPartialMap
  have hdom' : h.domain = ⊤ := hdom
  let e : X ⟶ Y := X.topIso.inv ≫ X.homOfLE hdom'.ge ≫ h.hom
  have hres : X.homOfLE (U := g.domain) (V := h.domain) g.le_domain_toRationalMap ≫ h.hom =
      g.hom := g.toPartialMap_toRationalMap_restrict
  have he : jUnit ≫ e = c := by
    have hle : jUnit.opensRange.ι ≫ X.topIso.inv ≫ X.homOfLE hdom'.ge =
        X.homOfLE (U := g.domain) (V := h.domain) g.le_domain_toRationalMap := by
      rw [← cancel_mono h.domain.ι, Category.assoc, Category.assoc,
        Scheme.homOfLE_ι, Scheme.toIso_inv_ι, Category.comp_id]
      exact (X.homOfLE_ι _).symm
    calc jUnit ≫ e = jUnit.isoOpensRange.hom ≫
          (jUnit.opensRange.ι ≫ X.topIso.inv ≫ X.homOfLE hdom'.ge) ≫ h.hom := by
            simp only [e, Category.assoc]
            rw [← Category.assoc jUnit.isoOpensRange.hom, Scheme.Hom.isoOpensRange_hom_ι]
      _ = jUnit.isoOpensRange.hom ≫ g.hom := by rw [hle, hres]
      _ = c := Iso.hom_inv_id_assoc _ _
  refine ⟨e, he, ?_⟩
  have : IsSchemeTheoreticallyDominant jUnit :=
    isSchemeTheoreticallyDominant_specMap Polynomial.toLaurent_injective
  refine ext_of_isSchemeTheoreticallyDominant (terminal.from Z)
    (terminal.hom_ext _ _) jUnit ?_
  rw [reassoc_of% he, hc]

/-- The same proper extension on the actual relative affine line over a field. -/
theorem exists_base_lift_of_isProper
    {Y Z : Over (Spec (CommRingCat.of k))}
    [Y.left.IsSeparated] [Z.left.IsSeparated] (q : Y ⟶ Z) [IsProper q.left]
    (r : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗ scheme (Spec (CommRingCat.of k)) ⟶ Z)
    (c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗ (Gm (Spec (CommRingCat.of k))).X ⟶ Y)
    (hc : c ≫ q = Over.mk (𝟙 _) ◁ unitInclusion _ ≫ r) :
    ∃ e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗ scheme (Spec (CommRingCat.of k)) ⟶ Y,
      Over.mk (𝟙 _) ◁ unitInclusion _ ≫ e = c ∧ e ≫ q = r := by
  let f := 𝟙 (Spec (CommRingCat.of k))
  obtain ⟨e, he, heq⟩ := exists_polynomial_lift_of_isProper q.left
    (polynomialPoint f ≫ r).left (laurentPoint f ≫ c).left (by
      have h : laurentPoint f ≫ c ≫ q = laurentInclusion f ≫ polynomialPoint f ≫ r := by
        rw [hc, ← Category.assoc, ← laurentInclusion_comp_polynomialPoint, Category.assoc]
      exact congrArg (fun z => z.left) h)
  let e' : polynomialScheme f ⟶ Y := Over.homMk e (by
    rw [← Over.w q, ← Category.assoc, heq, Over.w])
  refine ⟨polynomialPointInv f ≫ e',
    whiskerLeft_comp_of_laurentInclusion f (Over.OverMorphism.ext he), ?_⟩
  have he'q : e' ≫ q = polynomialPoint f ≫ r := Over.OverMorphism.ext heq
  rw [Category.assoc, he'q, ← Category.assoc,
    polynomialPointInv_comp_polynomialPoint, Category.id_comp]


variable {Y Z : Over (Spec (CommRingCat.of k))}
    [Y.left.IsSeparated] [Z.left.IsSeparated] (q : Y ⟶ Z) [IsProper q.left]
    (r : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗ scheme (Spec (CommRingCat.of k)) ⟶ Z)
    (c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗ (Gm (Spec (CommRingCat.of k))).X ⟶ Y)
    (hc : c ≫ q = Over.mk (𝟙 _) ◁ unitInclusion _ ≫ r)

/-- A chosen actual affine-line lift retaining the supplied punctured curve and target. -/
def baseLiftOfIsProper :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗ scheme (Spec (CommRingCat.of k)) ⟶ Y :=
  (exists_base_lift_of_isProper q r c hc).choose

/-- The chosen lift restricts to the supplied punctured curve. -/
theorem unitInclusion_comp_baseLiftOfIsProper :
    Over.mk (𝟙 _) ◁ unitInclusion _ ≫ baseLiftOfIsProper q r c hc = c :=
  (exists_base_lift_of_isProper q r c hc).choose_spec.1

/-- The chosen lift has exactly the prescribed target curve as composite. -/
theorem baseLiftOfIsProper_comp : baseLiftOfIsProper q r c hc ≫ q = r :=
  (exists_base_lift_of_isProper q r c hc).choose_spec.2

end AffineLine

end Langlands.GroupScheme
