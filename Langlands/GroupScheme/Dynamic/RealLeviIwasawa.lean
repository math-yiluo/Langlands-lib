import Langlands.GroupScheme.Dynamic.RealStarCore
import Langlands.GroupScheme.Dynamic.ComplexLeviIwasawa

/-! # Real Levi-compatible Iwasawa from ambient star realization -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k S : Type u} [RCLike k] [RCLike S] [Algebra k S]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Base-field adjoint stability suffices for internal real conjugation to
Hermitian cocharacter weights, using the polynomial adjoint core. -/
theorem exists_real_internal_conjugate_hermitian_of_base_star
    [IsScalarTower ℝ k S] [IsAlgClosed S]
    (hreal : ∀ z : k, star z = z)
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range,
      star g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ g : GL n k, g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range ∧
      GeneralLinear.HasHermitianWeightProjectors
        (χ ≫ ρ.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of k) g)) := by
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let ψ := χ ≫ ρ
  obtain ⟨r, t, ht, hsep⟩ :=
    GeneralLinear.exists_two_power_unit_separating
      (𝕜 := S) (GeneralLinear.cocharacterWeightSupport ψ)
  have htχ : GeneralLinear.cocharacterUnitsHom ψ S t ∈
      Langlands.Group.AlgebraicMatrixPowers.starCore
        (ρ.affineMatrix (CommAlgCat.of k S)).range :=
    ρ.cocharacterUnitsHom_mem_starCore hreal hstar χ t
  have hbar := GeneralLinear.conjugateEntries_cocharacterUnitsHom ψ
    (GeneralLinear.star_algebraMap_eq_self_of_real (S := S) hreal) t
    (GeneralLinear.norm_eq_one_of_two_power_eq_one t r ht)
  have hpow : (GeneralLinear.cocharacterUnitsHom ψ S t) ^ (2 ^ r) = 1 := by
    rw [← map_pow, ht, map_one]
  obtain ⟨c, hc, hcr, hcu⟩ :=
    Langlands.Group.RealTwoPowerUnitaryConjugation.exists_real_conjugator_of_two_power_eq_one
      (Langlands.Group.AlgebraicMatrixPowers.starCore
        (ρ.affineMatrix (CommAlgCat.of k S)).range)
      (ρ.starCore_affineMatrix_range_isPolynomiallyDefined
        (GeneralLinear.star_algebraMap_eq_self_of_real hreal))
      (Langlands.Group.AlgebraicMatrixPowers.star_mem_starCore _) r
      (GeneralLinear.cocharacterUnitsHom ψ S t) htχ hbar hpow
  obtain ⟨g, hg⟩ :=
    Langlands.Group.RealTwoPowerUnitaryConjugation.exists_base_matrix_of_conjugateEntries_eq_self
      (k := k) c hcr
  have hgm : g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range :=
    (ρ.map_mem_affineMatrix_range_iff (S := S) g).mp (by rw [hg]; exact hc.1)
  let θ := ψ ≫ (innerIso (GeneralLinear.groupScheme n (CommRingCat.of k))
    (GeneralLinear.baseOfMatrix (CommRingCat.of k) g)).hom
  have hθu : (GeneralLinear.cocharacterUnitsHom θ S t : Matrix n n S) ∈
      Matrix.unitaryGroup n S := by
    simpa only [θ, GeneralLinear.cocharacterUnitsHom_innerIso_baseOfMatrix_extension,
      hg] using hcu
  let : IsStarNormal (GeneralLinear.cocharacterUnitsHom θ S t : Matrix n n S) :=
    isStarNormal_of_mem_unitary hθu
  have hw : GeneralLinear.HasHermitianExtensionWeightProjectors (S := S) θ :=
    GeneralLinear.hasHermitianExtensionWeightProjectors_of_normal_separating_unit θ t
      (hsep.mono (GeneralLinear.cocharacterWeightSupport_innerIso_subset ψ g))
  refine ⟨g, hgm, ?_⟩
  have hw' := GeneralLinear.hasHermitianWeightProjectors_of_extension hreal θ hw
  simpa only [θ, ψ, MatrixRepresentation.conjugate, Category.assoc] using hw'


section RealHermitianRepresentation

variable [IsScalarTower ℝ k S] [IsAlgClosed S]
  (hreal : ∀ z : k, star z = z)
  (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
  (hstar : ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range,
    star g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range)
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

/-- Choose the internally conjugated actual representation with Hermitian
weights, using only star stability of its base-field image. -/
def realHermitianConjugate : MatrixRepresentation G n :=
  ρ.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of k)
    (Classical.choose
      (exists_real_internal_conjugate_hermitian_of_base_star
        (S := S) hreal ρ hρ hstar χ)))

/-- The chosen representation is closed, has Hermitian cocharacter weights,
and has exactly the original base-field point image. -/
theorem realHermitianConjugate_spec :
    IsClosedSubgroup (ρ.realHermitianConjugate (S := S) hreal hρ hstar χ) ∧
      GeneralLinear.HasHermitianWeightProjectors
        (χ ≫ ρ.realHermitianConjugate (S := S) hreal hρ hstar χ) ∧
      ((ρ.realHermitianConjugate (S := S) hreal hρ hstar χ).affineMatrix
        (CommAlgCat.of k k)).range =
        (ρ.affineMatrix (CommAlgCat.of k k)).range := by
  let g := Classical.choose
    (exists_real_internal_conjugate_hermitian_of_base_star
      (S := S) hreal ρ hρ hstar χ)
  have hg := Classical.choose_spec
    (exists_real_internal_conjugate_hermitian_of_base_star
      (S := S) hreal ρ hρ hstar χ)
  constructor
  · let : IsClosedImmersion ρ.hom.hom.left := hρ
    change IsClosedImmersion (ρ.hom.hom.left ≫ _)
    infer_instance
  · exact ⟨hg.2, ρ.conjugate_baseOfMatrix_range_eq_of_mem g hg.1⟩

end RealHermitianRepresentation

variable {P M : GroupScheme (Spec (CommRingCat.of k))}

/-- A closed star realization over a real coefficient field accommodates a
supplied dynamic pair after internal conjugation through the adjoint core. -/
theorem HasClosedStarRealization.hasRealHermitianStarLeviRealization
    [IsScalarTower ℝ k S] [IsAlgClosed S]
    (hreal : ∀ z : k, star z = z)
    (h : HasClosedStarRealization G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hm : (Dynamic.centralizer χ).IsRepresentedBy m) :
    Dynamic.HasHermitianStarLeviRealization p m := by
  obtain ⟨d, ρ, hρ, hs⟩ := h
  let σ := ρ.realHermitianConjugate (S := S) hreal hρ hs χ
  obtain ⟨hc, hw, hr⟩ := ρ.realHermitianConjugate_spec (S := S) hreal hρ hs χ
  have hσs : ∀ q ∈ (σ.affineMatrix (CommAlgCat.of k k)).range,
      star q ∈ (σ.affineMatrix (CommAlgCat.of k k)).range := by
    simpa only [σ, hr] using hs
  exact ⟨d, σ, χ, hc, hw, hp, hm, hσs⟩

/-- Real ambient star data suffice for compatible diagonal realization of
the original dynamic parabolic and Levi. -/
theorem HasClosedStarRealization.hasRealDiagonalStarLeviRealization
    [IsScalarTower ℝ k S] [IsAlgClosed S]
    (hreal : ∀ z : k, star z = z)
    (h : HasClosedStarRealization G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hm : (Dynamic.centralizer χ).IsRepresentedBy m) :
    Dynamic.HasDiagonalStarLeviRealization p m :=
  (h.hasRealHermitianStarLeviRealization (S := S) hreal χ hp hm).hasDiagonalStarLeviRealization

local instance realLeviIwasawaPointTopology
    (H : GroupScheme (Spec (CommRingCat.of k))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of k k)) :=
  H.affinePointsTopologicalSpace (CommAlgCat.of k k)

/-- Construct all four actual-point conclusions over real coefficients from
ambient star realization and a common dynamic cocharacter. -/
theorem HasClosedStarRealization.hasRealLeviCompatibleDecomposition
    [IsScalarTower ℝ k S] [IsAlgClosed S] [IsAffine G.X.left]
    (hreal : ∀ z : k, star z = z)
    (h : HasClosedStarRealization G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hm : (Dynamic.centralizer χ).IsRepresentedBy m) :
    CompactIwasawa.HasLeviCompatibleDecomposition
      (P.affinePointsTarget p (CommAlgCat.of k k))
      (M.affinePointsTarget m (CommAlgCat.of k k)) :=
  (h.hasRealDiagonalStarLeviRealization (S := S) hreal χ hp hm).hasLeviCompatibleDecomposition

end Langlands.GroupScheme.MatrixRepresentation
