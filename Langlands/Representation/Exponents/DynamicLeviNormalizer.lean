import Langlands.Representation.Exponents.FiniteNormalizerRepresentatives
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Rational.OriginalLeviCocharacter
import Langlands.GroupScheme.Rational.SplitComponentProof

/-! # Normalizers of rational Levis with a supplied dynamic presentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P}

/-- The normalizer of the original rational Levi has finitely many right cosets
from a single supplied dynamic presentation of its parabolic. -/
theorem IsRationalLeviSubgroup.exists_finite_normalizer_representatives_of_dynamicParabolic
    (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G)
    (hp : IsParabolicSubgroup p)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy p) :
    ∃ (n : ℕ) (g : Fin n → rationalPoints G),
      (∀ t, ∃ φ : M ≅ M, φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso (g t)).hom) ∧
      ∀ (w : rationalPoints G) (φ : M ≅ M),
        φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom →
          ∃ (t : Fin n) (m : rationalPoints M),
            w = g t * rationalPoints.map (l ≫ p) m := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hl.isConnectedReductive).1
  obtain ⟨ν, -, -, hZ⟩ :=
    hl.exists_splitComponentCocharacter_of_dynamicParabolic hG χ hP ha
  exact ha.exists_finite_normalizer_representatives
    (hl.isClosedSubgroup.comp hp.isClosedSubgroup) hZ

variable (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G)
  (hp : IsParabolicSubgroup p)
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (hP : (Dynamic.parabolic χ).IsRepresentedBy p)

/-- A chosen finite family of normalizing points representing every right
coset of the original Levi image. -/
def IsRationalLeviSubgroup.normalizerRepresentativesOfDynamicParabolic :
    Σ n : ℕ, Fin n → rationalPoints G :=
  ⟨(hl.exists_finite_normalizer_representatives_of_dynamicParabolic hG hp χ hP).choose,
    (hl.exists_finite_normalizer_representatives_of_dynamicParabolic hG hp χ hP).choose_spec.choose⟩

/-- The chosen representatives normalize the original Levi and give actual
rational-point factorizations of every normalizing point. -/
theorem IsRationalLeviSubgroup.normalizerRepresentativesOfDynamicParabolic_spec :
    (∀ t, ∃ φ : M ≅ M,
      φ.hom ≫ l ≫ p =
        l ≫ p ≫ (G.innerIso
          ((hl.normalizerRepresentativesOfDynamicParabolic hG hp χ hP).2 t)).hom) ∧
      ∀ (w : rationalPoints G) (φ : M ≅ M),
        φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom →
          ∃ (t : Fin (hl.normalizerRepresentativesOfDynamicParabolic hG hp χ hP).1)
            (m : rationalPoints M),
            w = (hl.normalizerRepresentativesOfDynamicParabolic hG hp χ hP).2 t *
              rationalPoints.map (l ≫ p) m :=
  (hl.exists_finite_normalizer_representatives_of_dynamicParabolic hG hp χ hP).choose_spec.choose_spec

section Norm

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- A normalizing point preserving all rational-character norms on central
Levi points belongs to the original Levi image. -/
theorem IsRationalLeviSubgroup.mem_pointImage_of_normalizes_of_norm_of_dynamicParabolic
    (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy p)
    {w : rationalPoints G} {φ : M ≅ M}
    (hw : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom)
    (hnorm : ∀ x ∈ Subgroup.center (rationalPoints M), ∀ ψ : rationalCharacters M,
      (Plancherel.rationalNormCharacters M ψ).toMul (rationalPoints.map φ.hom x) =
        (Plancherel.rationalNormCharacters M ψ).toMul x) :
    w ∈ Aubert.General.RepresentedParabolic.pointImage (l ≫ p) := by
  let : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hl.isConnectedReductive).1
  obtain ⟨ν, -, -, hZ⟩ :=
    hl.exists_splitComponentCocharacter_of_dynamicParabolic hG χ hP ha
  rw [Aubert.General.RepresentedParabolic.pointImage_eq_range_carrier]
  exact ha.mem_range_of_normalizes_of_norm hl.isConnectedReductive hZ hw hnorm

end Norm

end Langlands.GroupScheme
