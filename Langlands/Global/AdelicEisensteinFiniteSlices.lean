import Langlands.Global.AdelicEisensteinFiniteParameters
import Langlands.Global.AdelicOpenIwasawaCompact

/-! # Finite translations in the archimedean slices of a deformed section -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000

namespace Langlands.Global.AdelicGroupPoints.IsIwasawaCompact

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K)

local notation "Adeles" => AdelicGroupPoints F G
local notation "FinitePoints" => FiniteAdelicGroupPoints F G
local notation "InfinitePoints" => InfiniteAdelicGroupPoints F G

omit [IsClosedImmersion p.hom.hom.left] in
private theorem infinite_map_apply (g : AdelicGroupPoints F P) :
    infinite F G (map F P G p g) = P.affinePointsTarget p (CommAlgCat.of F (InfiniteAdeleRing F))
      (infinite F P g) :=
  DFunLike.congr_fun (P.affinePointsTarget_naturality p
    (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))) g

/-- The finite displacement is invariant under the left parabolic action. -/
theorem finiteHeightDisplacement_map_mul (d : FinitePoints)
    (q : AdelicGroupPoints F P) (g : Adeles) :
    hK.finiteHeightDisplacement d (map F P G p q * g) = hK.finiteHeightDisplacement d g := by
  simp only [finiteHeightDisplacement, mul_assoc, hK.height_map_mul, add_sub_add_left_eq_sub]

/-- The finite displacement is invariant under the right infinite compact action. -/
theorem finiteHeightDisplacement_mul_ofInfinite (d : FinitePoints) (g : Adeles)
    {a : InfinitePoints} (ha : ofInfinite F G a ∈ K) :
    hK.finiteHeightDisplacement d (g * ofInfinite F G a) = hK.finiteHeightDisplacement d g := by
  rw [finiteHeightDisplacement, mul_assoc, (factors_commute F G a d).eq, ← mul_assoc,
    hK.height_mul_right _ ha, hK.height_mul_right _ ha]
  rfl

/-- With a product Iwasawa compact, the displacement under finite right
translation is independent of the infinite argument of the section. -/
theorem finiteHeightDisplacement_pair (hInf : ∀ k ∈ K, ofInfinite F G (infinite F G k) ∈ K)
    (d b : FinitePoints) (a : InfinitePoints) :
    hK.finiteHeightDisplacement d (pair F G a b) = hK.finiteHeightDisplacement d (ofFinite F G b) := by
  obtain ⟨q, k, hk, h⟩ := hK.exists_eq (ofInfinite F G a)
  have hinf := congrArg (infinite F G) h
  rw [map_mul, infinite_map_apply, infinite_ofInfinite] at hinf
  have heq : ofInfinite F G a =
      map F P G p (ofInfinite F P (infinite F P q)) * ofInfinite F G (infinite F G k) := by
    rw [map_ofInfinite, ← map_mul, hinf]
  have hpair : pair F G a b = ofInfinite F G a * ofFinite F G b := by
    rw [ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one, one_mul]
  rw [hpair, heq, mul_assoc, (factors_commute F G (infinite F G k) b).eq,
    hK.finiteHeightDisplacement_map_mul, hK.finiteHeightDisplacement_mul_ofInfinite d _ (hInf k hk)]

/-- The parameter scalar for finite right translation at the fixed finite argument. -/
def finiteTranslationFactor (lam : ComplexCharacterParameter F P) (d b : FinitePoints) : ℂ :=
  Complex.exp (complexParameterPairing F P lam (hK.finiteHeightDisplacement d (ofFinite F G b)))

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- The changed height multiplies the ordinary finite translate by an exponential. -/
theorem parameterRightAction_finite_eq (lam : ComplexCharacterParameter F P)
    (d : FinitePoints) (φ : Adeles → ℂ) (g : Adeles) :
    hK.parameterRightAction lam (ofFinite F G d) φ g =
      φ (g * ofFinite F G d) * Complex.exp
        (complexParameterPairing F P lam (hK.finiteHeightDisplacement d g)) := by
  rw [hK.parameterRightAction_apply, mul_div_assoc, heightPower, heightPower,
    ← Complex.exp_sub, ← map_sub]
  rfl

/-- The deformed finite translate on an infinite slice is the translate of
its finite argument multiplied by a constant on the infinite slice. -/
theorem parameterRightAction_apply_pair (hInf : ∀ k ∈ K, ofInfinite F G (infinite F G k) ∈ K)
    (lam : ComplexCharacterParameter F P) (d b : FinitePoints) (a : InfinitePoints)
    (φ : Adeles → ℂ) :
    hK.parameterRightAction lam (ofFinite F G d) φ (pair F G a b) =
      φ (pair F G a (b * d)) * hK.finiteTranslationFactor lam d b := by
  have hmul : pair F G a b * ofFinite F G d = pair F G a (b * d) := by
    rw [ofFinite_eq_pair, pair_mul, mul_one]
  rw [hK.parameterRightAction_finite_eq, hK.finiteHeightDisplacement_pair hInf, hmul]
  rfl

end Langlands.Global.AdelicGroupPoints.IsIwasawaCompact
