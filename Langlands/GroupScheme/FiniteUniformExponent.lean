import Langlands.Algebra.FiniteHopfUniformExponent
import Langlands.GroupScheme.CentralIsogeny.KernelTorsion
import Langlands.GroupScheme.FiniteUniformExponentStatement

/-! # Uniform exponents for finite group schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FiniteUniformExponent

variable {k : Type u} [Field k]

/-- The coordinate Hopf algebra of a finite group scheme is finite dimensional. -/
theorem finite_hopfAlgebra (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [IsFinite G.X.hom] :
    Module.Finite k (AffineCoordinates.hopfAlgebra G) := by
  let A := AffineCoordinates.hopfAlgebra G
  let e := AffineCoordinates.hopfSpecIso G
  let Y := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))
  let f : Y ⟶ G.X := e.hom.hom.hom
  let g : G.X ⟶ Y := e.inv.hom.hom
  have hgf : g ≫ f = 𝟙 G.X := congrArg (fun φ => φ.hom.hom) e.inv_hom_id
  have hfg : f ≫ g = 𝟙 Y := congrArg (fun φ => φ.hom.hom) e.hom_inv_id
  have : IsIso f := ⟨g, hfg, hgf⟩
  have : IsIso f.left := (Over.forget _).map_isIso f
  have hfin : IsFinite (f.left ≫ G.X.hom) := inferInstance
  rw [Over.w] at hfin
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A))) at hfin
  rw [IsFinite.SpecMap_iff] at hfin
  exact RingHom.finite_algebraMap.mp hfin

/-- A power killing the coordinate-valued universal point kills all scheme-valued
points, with no commutativity condition on the group scheme. -/
theorem pow_eq_one_of_hopf_id (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] (n : ℕ)
    (hn : (toConv (AlgHom.id k (AffineCoordinates.hopfAlgebra G)) :
      WithConv (AffineCoordinates.hopfAlgebra G →ₐ[k] AffineCoordinates.hopfAlgebra G)) ^ n = 1) :
    ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X), x ^ n = 1 := by
  let A := AffineCoordinates.hopfAlgebra G
  let e := AffineCoordinates.hopfSpecIso G
  let Y := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))
  let f : Y ⟶ G.X := e.hom.hom.hom
  let g : G.X ⟶ Y := e.inv.hom.hom
  have : IsMonHom f := e.hom.hom.isMonHom_hom
  have hgf : g ≫ f = 𝟙 G.X := congrArg (fun φ => φ.hom.hom) e.inv_hom_id
  have hY : (𝟙 Y) ^ n = 1 := by
    rw [id_spec_asOver_eq_mapMulEquiv, ← map_pow, hn, map_one]
  intro T x
  have hx : x = (x ≫ g) ≫ f := by rw [Category.assoc, hgf, Category.comp_id]
  have hy : (x ≫ g) ^ n = 1 := by
    rw [← Category.comp_id (x ≫ g), ← MonObj.comp_pow, hY, MonObj.comp_one]
  rw [hx, ← MonObj.pow_comp, hy, MonObj.one_comp]

/-- Finite group schemes in positive characteristic have a uniform positive
exponent on all schemes over the base. -/
theorem exists_pow_eq_one_of_charP (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsFinite G.X.hom] (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ n : ℕ, 0 < n ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X), x ^ n = 1 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := finite_hopfAlgebra G
  obtain ⟨n, hn, hpow⟩ :=
    Langlands.FiniteHopfUniformExponent.exists_pow_eq_one_of_charP
      (k := k) (H := AffineCoordinates.hopfAlgebra G) p
  exact ⟨n, hn, pow_eq_one_of_hopf_id G n hpow⟩

/-- Reduced finite group schemes have a uniform positive exponent. -/
theorem exists_pow_eq_one_of_reduced_coordinates
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
    [IsFinite G.X.hom] [IsReduced (AffineCoordinates.hopfAlgebra G)] :
    ∃ n : ℕ, 0 < n ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X), x ^ n = 1 := by
  have := finite_hopfAlgebra G
  obtain ⟨n, hn, hpow⟩ :=
    Langlands.FiniteHopfUniformExponent.exists_pow_eq_one_of_isReduced
      (k := k) (H := AffineCoordinates.hopfAlgebra G)
  exact ⟨n, hn, pow_eq_one_of_hopf_id G n hpow⟩

end Langlands.GroupScheme.FiniteUniformExponent

namespace Langlands.GroupScheme

/-- Every finite group scheme over a field is killed by a positive integer on
all schemes over that field. -/
theorem finiteGroupSchemeUniformExponent :
    FiniteGroupSchemeUniformExponentStatement.{u} := by
  intro k _ G hfinite
  let : IsFinite G.X.hom := hfinite
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := FiniteUniformExponent.finite_hopfAlgebra G
  obtain ⟨n, hn, hpow⟩ :=
    Langlands.FiniteHopfUniformExponent.exists_pow_eq_one
      (k := k) (H := AffineCoordinates.hopfAlgebra G)
  exact ⟨n, hn, FiniteUniformExponent.pow_eq_one_of_hopf_id G n hpow⟩

end Langlands.GroupScheme
