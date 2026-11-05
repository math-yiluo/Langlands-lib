import Langlands.GroupScheme.Rational.PolynomialHomFiniteDescent

/-! # Full centrality in finite coefficient models -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.PolynomialPoint

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    (G : GroupScheme (Spec (CommRingCat.of k)))

local notation "G_L" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G

/-- The actual affine pullback comparison reflects full-center membership. -/
theorem mem_center_of_affineBaseChangeEquiv
    {A : Type u} [CommRing A] [Algebra k A] [Algebra L A] [IsScalarTower k L A]
    {x : Lie.AffinePoints G_L A}
    (hx : Lie.affineBaseChangeEquiv k L G A x ∈ (center G).carrier
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)))) :
    x ∈ (center G_L).carrier
      ((algSpec (CommRingCat.of L)).obj (op (CommAlgCat.of L A))) := by
  rw [center_baseChange, SubgroupFunctor.mem_baseChange]
  have h := (center G).comp_mem (Lie.affineBaseTestIso k L A).hom hx
  change (Lie.affineBaseTestIso k L A).hom ≫
      ((Lie.affineBaseTestIso k L A).inv ≫
        baseChangePointsEquiv (algebraBaseMap k L) G _ x) ∈ _ at h
  simp only [Iso.hom_inv_id_assoc] at h
  exact h

variable {k L G}

/-- Coefficient embeddings between extension fields detect full centrality in
the original target group, without a finite-extension hypothesis. -/
theorem mem_center_of_mapCoefficients_extension
    {E : Type u} [Field E] [Algebra k E] (f : E →ₐ[k] L) (I : Type)
    {x : Lie.AffinePoints G (MvPolynomial I E)}
    (hx : mapCoefficients (G := G) f x ∈ (center G).carrier
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k (MvPolynomial I L))))) :
    x ∈ (center G).carrier
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k (MvPolynomial I E)))) := by
  let : Algebra E L := f.toAlgebra
  let q := (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (MvPolynomial.mapAlgHom f :
      MvPolynomial I E →ₐ[k] MvPolynomial I L)).op
  have hq : Flat q.left ∧ Surjective q.left := by
    apply (flat_and_surjective_SpecMap_iff _).2
    exact polynomialCoefficients_faithfullyFlat E L I
  let : Flat q.left := hq.1
  let : Surjective q.left := hq.2
  exact mem_center_of_flat_surjective q hx

/-- Full centrality of the universal polynomial point gives centrality of the
actual extension-field homomorphism. -/
theorem isCentral_of_polynomialOfHom {n : ℕ}
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : polynomialOfHom (k := k) (L := L) (G := G) f ∈ (center G).carrier
      ((algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of k (MvPolynomial (Fin n) L))))) :
    IsCentral f := by
  have hhom := mem_center_of_affineBaseChangeEquiv k L G (x := f.hom.hom) hf
  intro T x
  exact (center _).comp_mem x hhom

/-- A finite Galois coefficient model of a full-central homomorphism is
full-central on every scheme test. -/
theorem FiniteGaloisHomModel.isCentral {n : ℕ}
    {f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L}
    (D : FiniteGaloisHomModel (k := k) (L := L) (G := G) f)
    (hf : IsCentral f) : IsCentral D.hom := by
  have hL : polynomialOfHom (k := k) (L := L) (G := G) f ∈ (center G).carrier
      ((algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of k (MvPolynomial (Fin n) L)))) :=
    (centralInput k L G f hf).property
  apply isCentral_of_polynomialOfHom D.hom
  apply mem_center_of_mapCoefficients_extension
    (k := k) (L := L) (G := G) (E := D.field) D.field.toIntermediateField.val (Fin n)
    (x := polynomialOfHom (k := k) (L := D.field) (G := G) D.hom)
  rw [D.extension_eq]
  exact hL

/-- Choose a finite Galois coefficient model together with its full centrality. -/
def centralFiniteGaloisHomModel [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsGalois k L] {n : ℕ}
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) (hf : IsCentral f) :
    {D : FiniteGaloisHomModel (k := k) (L := L) (G := G) f // IsCentral D.hom} :=
  ⟨finiteGaloisHomModel f, (finiteGaloisHomModel f).isCentral hf⟩

end Langlands.GroupScheme.PolynomialPoint
