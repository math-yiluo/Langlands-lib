import Langlands.GroupScheme.Rational.PointedPrimitiveFrobeniusGenerators
import Langlands.GroupScheme.Rational.LaurentPrimitiveIndependence

/-! # Polynomial primitive coordinates from pointed torus domination -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace Langlands.GroupScheme.Corepresented

variable {k : Type u} [Field k]
    {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} (CommRingCat.of k)}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- Polynomial primitive coordinates give an actual vector-group isomorphism. -/
def primitiveCoordinatesIso {N : ℕ} {y : Fin N → B}
    (hy : VectorGroup.IsPrimitiveFamily e y)
    (hbij : Function.Bijective (aeval y : MvPolynomial (Fin N) k →ₐ[k] B)) :
    groupScheme F e ≅ VectorGroup.groupScheme (CommRingCat.of k) N := by
  let q := VectorGroup.quotientMap hy
  let φ : MvPolynomial (Fin N) k ≃+* B := RingEquiv.ofBijective (aeval y) hbij
  have : IsIso q.hom.hom.left := by
    rw [VectorGroup.quotientMap_left]
    exact (inferInstance : IsIso (Spec.map φ.toCommRingCatIso.hom))
  have : IsIso ((Over.forget _).map q.hom.hom) := by
    change IsIso q.hom.hom.left
    infer_instance
  have : IsIso q.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  exact Grp.mkIso' (asIso q.hom.hom)

variable {p : ℕ} [Fact p.Prime] [CharP k p]

include p

open LaurentAugmentation in
/-- Pointed split-torus domination turns a supplied finite primitive algebra-generating
family into polynomial primitive coordinates over the original field. -/
theorem exists_pointed_primitivePolynomialCoordinates
    [IsReduced (groupScheme F e).X.left]
    (hdom : HasPointedSplitTorusDomination (groupScheme F e))
    (T : Finset (primitiveFunctions e))
    (hT : Algebra.adjoin k (Subtype.val '' (T : Set (primitiveFunctions e))) = ⊤) :
    ∃ (N : ℕ) (y : Fin N → B), VectorGroup.IsPrimitiveFamily e y ∧
      Function.Bijective (aeval y : MvPolynomial (Fin N) k →ₐ[k] B) := by
  classical
  let := AffineLinearEmbedding.bialgebra e
  obtain ⟨I, hI, σ, hε, s, G, hσ, hs, halg, hind⟩ :=
    exists_pointed_primitiveFrobGenerators e (p := p) hdom T
  let g : Fin G.card → primitiveFunctions e := fun j => (G.equivFin.symm j).val
  let y : Fin G.card → B := fun j => (g j).val
  let φ := primitiveLaurentPullback e σ hε
  have hg : ∀ j, g j ∈ G := fun j => (G.equivFin.symm j).property
  have hginj : Function.Injective g := by
    intro i j hij
    apply G.equivFin.symm.injective
    exact Subtype.ext hij
  have hgrange : Set.range g = (G : Set (primitiveFunctions e)) := by
    ext b
    constructor
    · rintro ⟨j, rfl⟩
      exact hg j
    · intro hb
      exact ⟨G.equivFin ⟨b, hb⟩, congrArg Subtype.val (G.equivFin.symm_apply_apply ⟨b, hb⟩)⟩
  have hmem : ∀ j, φ (g j) ∈ finiteOrbitSpace k p I s := by
    intro j
    exact hs (subset_frobSpan _ ⟨g j, hg j, rfl⟩)
  have hinj : Function.Injective (fun j => finiteEncoding k p I s (φ (g j))) := by
    intro i j hij
    apply hginj
    apply primitiveLaurentPullback_injective e σ hε hσ
    exact finiteEncoding_injOn s (hmem i) (hmem j) hij
  have himage : Finset.univ.image (fun j => finiteEncoding k p I s (φ (g j))) =
      G.image (finiteEncoding k p I s ∘ φ) := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.coe_image]
    change Set.range ((finiteEncoding k p I s ∘ φ) ∘ g) = _
    rw [Set.range_comp, hgrange]
  have hy : VectorGroup.IsPrimitiveFamily e y := by
    intro A a b j
    exact (mem_primitiveFunctions_iff e).mp (g j).property A a b
  have hyind : AlgebraicIndependent k y :=
    PrimitivePolynomial.algebraicIndependent_of_frobIndep_encoding σ y
      (fun j => (g j).property) (fun j => φ (g j)) (fun _ => rfl) s hinj (himage.symm ▸ hind)
  have hyrange : Set.range y = Subtype.val '' (G : Set (primitiveFunctions e)) := by
    change Set.range (Subtype.val ∘ g) = _
    rw [Set.range_comp, hgrange]
  have hsurj : Function.Surjective (aeval y : MvPolynomial (Fin G.card) k →ₐ[k] B) := by
    rw [← AlgHom.range_eq_top, aeval_range, hyrange, ← halg, hT]
  exact ⟨G.card, y, hy, hyind, hsurj⟩

/-- A reduced group with finite primitive algebra generators and pointed split-torus
domination is an actual vector group in characteristic p. -/
theorem exists_vectorGroupIso_of_pointed_primitiveGenerators
    [IsReduced (groupScheme F e).X.left]
    (hdom : HasPointedSplitTorusDomination (groupScheme F e))
    (T : Finset (primitiveFunctions e))
    (hT : Algebra.adjoin k (Subtype.val '' (T : Set (primitiveFunctions e))) = ⊤) :
    ∃ N : ℕ, Nonempty (groupScheme F e ≅ VectorGroup.groupScheme (CommRingCat.of k) N) := by
  obtain ⟨N, y, hy, hbij⟩ := exists_pointed_primitivePolynomialCoordinates e (p := p) hdom T hT
  exact ⟨N, ⟨primitiveCoordinatesIso e hy hbij⟩⟩

end Langlands.GroupScheme.Corepresented
