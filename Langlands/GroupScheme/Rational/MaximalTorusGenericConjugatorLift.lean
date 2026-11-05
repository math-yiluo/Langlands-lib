import Langlands.GroupScheme.Rational.MaximalTorusGenericConjugator

/-! # Lifting generic torus conjugators along homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G G' : GroupScheme (Spec (CommRingCat.of k))}
  {T₀ T₀' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A homomorphism `φ : G ⟶ G'` reflects torus normalizers from `j₀'` to `j₀` when every point
of `G` whose image normalizes the torus `j₀'` normalizes the torus `j₀`. -/
def ReflectsTorusNormalizer (φ : G ⟶ G') (j₀ : T₀.toGrp ⟶ G) (j₀' : T₀'.toGrp ⟶ G') : Prop :=
  ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ G.X),
    x ≫ φ.hom.hom ∈ (torusNormalizer j₀').carrier U → x ∈ (torusNormalizer j₀).carrier U

variable {j₀ : T₀.toGrp ⟶ G} {j₀' : T₀'.toGrp ⟶ G'}

/-- A generic conjugator for `j₀'` lifts to a generic conjugator for `j₀` along a flat,
surjective, quasi-compact, universally open homomorphism `φ : G ⟶ G'` that reflects torus
normalizers. -/
theorem HasGenericTorusConjugator.of_hom (φ : G ⟶ G')
    [Flat φ.hom.hom.left] [Surjective φ.hom.hom.left] [QuasiCompact φ.hom.hom.left]
    [UniversallyOpen φ.hom.hom.left] (hφ : ReflectsTorusNormalizer φ j₀ j₀')
    (h : HasGenericTorusConjugator j₀') : HasGenericTorusConjugator j₀ := by
  obtain ⟨n, hn, X', π', g', hflat, hsurj, hqc, hdesc, hdense⟩ := h
  let f : X'.left ⟶ G'.X.left := g'.left
  let p : G.X.left ⟶ G'.X.left := φ.hom.hom.left
  let X : Over (Spec (CommRingCat.of k)) := Over.mk (pullback.fst f p ≫ X'.hom)
  let pr : X ⟶ X' := Over.homMk (pullback.fst f p) rfl
  have hg : pullback.snd f p ≫ G.X.hom = pullback.fst f p ≫ X'.hom := by
    calc pullback.snd f p ≫ G.X.hom = pullback.snd f p ≫ p ≫ G'.X.hom := by
          rw [Over.w φ.hom.hom]
      _ = pullback.fst f p ≫ f ≫ G'.X.hom := by rw [pullback.condition_assoc]
      _ = pullback.fst f p ≫ X'.hom := by rw [Over.w g']
  let g : X ⟶ G.X := Over.homMk (pullback.snd f p) hg
  have hgφ : g ≫ φ.hom.hom = pr ≫ g' := by
    ext
    exact pullback.condition.symm
  refine ⟨n, hn, X, pr ≫ π', g, ?_, ?_, ?_, ?_, ?_⟩
  · change Flat (pullback.fst f p ≫ π'.left)
    infer_instance
  · change Surjective (pullback.fst f p ≫ π'.left)
    have : Surjective (pullback.fst f p) := by
      rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst, range_eq_univ,
        Set.preimage_univ]
    infer_instance
  · change QuasiCompact (pullback.fst f p ≫ π'.left)
    infer_instance
  · intro U a₁ a₂ ha
    apply hφ
    have h' := hdesc U (a₁ ≫ pr) (a₂ ≫ pr) (by simpa only [Category.assoc] using ha)
    have hmap : ((a₁ ≫ g)⁻¹ * (a₂ ≫ g)) ≫ φ.hom.hom =
        ((a₁ ≫ pr) ≫ g')⁻¹ * ((a₂ ≫ pr) ≫ g') := by
      have := map_mul (IsMonHom.monoidHom φ.hom.hom U) (a₁ ≫ g)⁻¹ (a₂ ≫ g)
      simp only [IsMonHom.monoidHom, MonoidHom.coe_mk, OneHom.coe_mk] at this
      have hinv : (a₁ ≫ g)⁻¹ ≫ φ.hom.hom = ((a₁ ≫ g) ≫ φ.hom.hom)⁻¹ :=
        map_inv (IsMonHom.monoidHom φ.hom.hom U) (a₁ ≫ g)
      rw [this, hinv]
      simp only [Category.assoc, hgφ]
    rw [hmap]
    exact h'
  · change DenseRange (pullback.snd f p)
    rw [DenseRange, Scheme.Pullback.range_snd]
    exact hdense.preimage (Scheme.Hom.isOpenMap p)

/-- If every point of `G` over every test scheme centralizes the torus, then `j₀` has a generic
conjugator. -/
theorem hasGenericTorusConjugator_of_centralizer_eq_top {j : T₀.toGrp ⟶ G}
    (hC : ∀ (U : Over (Spec (CommRingCat.of k))) (g : U ⟶ G.X),
      g ∈ (torusCentralizer j).carrier U) [Flat G.X.hom] [QuasiCompact G.X.hom] :
    HasGenericTorusConjugator j :=
  hasGenericTorusConjugator_of_normalizer_eq_top fun U g =>
    torusCentralizer_le_torusNormalizer j U (hC U g)

end Langlands.GroupScheme
