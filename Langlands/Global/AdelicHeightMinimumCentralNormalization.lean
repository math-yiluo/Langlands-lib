import Langlands.Global.AdelicHeightMinimumLeviRestriction
import Langlands.Global.AdelicLineCharacterHeight
import Langlands.Global.AdelicNormOneDecomposition
import Langlands.GroupScheme.Rational.CharacterRestrictionProof

/-! # Central positive normalization preserves actual height minima -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix NNReal

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The same finite family of orbit-height inequalities on the full adelic
group, before imposing all algebraic character-norm-one conditions. -/
def adelicChainHeightMinimalSet (r : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (v : (i : ℕ) → Fin (d i) → F)
    (Q : ℕ → Subgroup (RationalGroupPoints F G)) (c : ℝ) :
    Set (AdelicGroupPoints F G) :=
  {g | ∀ i, i < r → ∀ q : Q i,
    orbitHeight F G (ρ i) (v i) g ≤
      c * orbitHeight F G (ρ i) (v i) (g * rational F G q)}

@[simp] theorem mem_adelicChainHeightMinimalSet_coe
    (r : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (v : (i : ℕ) → Fin (d i) → F)
    (Q : ℕ → Subgroup (RationalGroupPoints F G)) (c : ℝ)
    (g : normOneSubgroup F G) :
    (g : AdelicGroupPoints F G) ∈ adelicChainHeightMinimalSet F G r d ρ v Q c ↔
      g ∈ chainHeightMinimalSet F G r d ρ v Q c :=
  Iff.rfl

/-- Fixed-factor restriction of the inequalities does not require norm-one
membership of the subgroup factor. Only the tested rational points must
normalize the fixing subgroup. -/
theorem mem_adelicChainHeightMinimalSet_restrict_of_fixed_factor
    (H : GroupScheme (Spec (CommRingCat.of F))) (f : H ⟶ G)
    (r s : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (v : (i : ℕ) → Fin (d i) → F)
    (Q : ℕ → Subgroup (RationalGroupPoints F G))
    (R : ℕ → Subgroup (RationalGroupPoints F H))
    (σ : ℕ → ℕ) (hσ : ∀ i, i < s → σ i < r)
    (N : Subgroup (AdelicGroupPoints F G))
    (hfix : ∀ i, i < s → IsOrbitVectorFixedBy F G (ρ (σ i)) (v (σ i)) N)
    (hQ : ∀ i, i < s → ∀ q : R i,
      H.affinePointsTarget f (CommAlgCat.of F F) q ∈ Q (σ i))
    (hnorm : ∀ i, i < s → ∀ q : R i,
      rational F G (H.affinePointsTarget f (CommAlgCat.of F F) q) ∈
        Subgroup.normalizer (N : Set (AdelicGroupPoints F G)))
    (c : ℝ) (h : AdelicGroupPoints F H) (x : AdelicGroupPoints F G) (hx : x ∈ N)
    (p : AdelicGroupPoints F G) (hp : p = map F H G f h * x)
    (hmin : p ∈ adelicChainHeightMinimalSet F G r d ρ v Q c) :
    h ∈ adelicChainHeightMinimalSet F H s (fun i => d (σ i))
      (fun i => (ρ (σ i)).restrict f) (fun i => v (σ i)) R c := by
  intro i hi q
  let qG : Q (σ i) :=
    ⟨H.affinePointsTarget f (CommAlgCat.of F F) q, hQ i hi q⟩
  have hm := hmin (σ i) (hσ i hi) qG
  change orbitHeight F G (ρ (σ i)) (v (σ i)) p ≤
    c * orbitHeight F G (ρ (σ i)) (v (σ i))
      (p * rational F G (H.affinePointsTarget f (CommAlgCat.of F F) q)) at hm
  rw [hp, orbitHeight_mul_eq_of_fixed F G _ _ N (hfix i hi) _ _ hx,
    orbitHeight_mul_mul_eq_of_normalizer F G _ _ N (hfix i hi) _ _ _ hx
      (hnorm i hi q)] at hm
  have hnat :
      map F H G f (rational F H q) =
        rational F G (H.affinePointsTarget f (CommAlgCat.of F F) q) :=
    (DFunLike.congr_fun (rational_naturality F H f) (q : RationalGroupPoints F H)).symm
  simpa only [orbitHeight_restrict, map_mul, hnat] using hm

/-- A central point scaling each selected line preserves every comparison
inequality, with the same arbitrary real constant. Its positive character
norm cancels before and after each rational translation. -/
theorem mem_adelicChainHeightMinimalSet_central_mul_iff
    (A : GroupScheme (Spec (CommRingCat.of F))) (z : A ⟶ G)
    (hz : IsCentral z)
    (r : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (j : (i : ℕ) → Fin (d i))
    (hline : ∀ i, i < r → ((ρ i).restrict z).PreservesCoordinateLine (j i))
    (Q : ℕ → Subgroup (RationalGroupPoints F G)) (c : ℝ)
    (a : AdelicGroupPoints F A) (g : AdelicGroupPoints F G) :
    map F A G z a * g ∈
        adelicChainHeightMinimalSet F G r d ρ (fun i => Pi.single (j i) 1) Q c ↔
      g ∈ adelicChainHeightMinimalSet F G r d ρ (fun i => Pi.single (j i) 1) Q c := by
  have hcomm (y : AdelicGroupPoints F G) :
      map F A G z a * y = y * map F A G z a :=
    (commute_of_mem_center (hz _ a) y).eq
  have hscale (i : ℕ) (hi : i < r) (y : AdelicGroupPoints F G) :
      orbitHeight F G (ρ i) (Pi.single (j i) 1) (map F A G z a * y) =
        ((lineCharacterNorm F G A z (ρ i) (j i) (hline i hi) a : ℝ≥0) : ℝ) *
          orbitHeight F G (ρ i) (Pi.single (j i) 1) y := by
    rw [hcomm]
    exact orbitHeight_mul_map_eq_lineCharacterNorm F G A z (ρ i) (j i)
      (hline i hi) y a
  have hiff (i : ℕ) (hi : i < r) (q : Q i) :
      (orbitHeight F G (ρ i) (Pi.single (j i) 1) (map F A G z a * g) ≤
        c * orbitHeight F G (ρ i) (Pi.single (j i) 1)
          ((map F A G z a * g) * rational F G q)) ↔
      (orbitHeight F G (ρ i) (Pi.single (j i) 1) g ≤
        c * orbitHeight F G (ρ i) (Pi.single (j i) 1) (g * rational F G q)) := by
    rw [mul_assoc, hscale i hi, hscale i hi]
    have hpos : 0 <
        ((lineCharacterNorm F G A z (ρ i) (j i) (hline i hi) a : ℝ≥0) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    rw [mul_left_comm c]
    exact mul_le_mul_iff_right₀ hpos
  constructor
  · intro h i hi q
    exact (hiff i hi q).mp (h i hi q)
  · intro h i hi q
    exact (hiff i hi q).mpr (h i hi q)

/-- The actual positive/norm-one decomposition for a split component normalizes
an arbitrary adelic point satisfying the minimum inequalities. No norm-one
membership of that original point is supplied or inferred. -/
theorem exists_normOne_chainHeightMinimalSet_of_splitComponent
    (hG : IsConnectedReductive G)
    (A : CommGroupScheme (Spec (CommRingCat.of F))) (z : A.toGrp ⟶ G)
    (hz : IsSplitComponent z)
    (r : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (j : (i : ℕ) → Fin (d i))
    (hline : ∀ i, i < r → ((ρ i).restrict z).PreservesCoordinateLine (j i))
    (Q : ℕ → Subgroup (RationalGroupPoints F G)) (c : ℝ)
    (g : AdelicGroupPoints F G)
    (hg : g ∈ adelicChainHeightMinimalSet F G r d ρ (fun i => Pi.single (j i) 1) Q c) :
    ∃ (a : PositiveRealTorus.intrinsicSubgroup F A) (m : normOneSubgroup F G),
      PositiveRealTorus.positivePointMap F G A z a * m = g ∧
        m ∈ chainHeightMinimalSet F G r d ρ (fun i => Pi.single (j i) 1) Q c := by
  classical
  obtain ⟨hinj, hindex⟩ := characterRestriction F G hG A z hz
  let : (characterRestrict z).range.FiniteIndex := hindex
  obtain ⟨I, hI, ⟨e⟩⟩ := hz.1.1.1
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let a := PositiveRealTorus.positiveFactor F G A z hinj I e g
  let m := PositiveRealTorus.normOneFactor F G A z hinj I e g
  have hfact :
      PositiveRealTorus.positivePointMap F G A z a * m = g :=
    PositiveRealTorus.positivePointMap_mul_normOneFactor F G A z hinj I e g
  refine ⟨a, m, hfact, ?_⟩
  apply (mem_adelicChainHeightMinimalSet_central_mul_iff F G A.toGrp z hz.1.2
    r d ρ j hline Q c (a : AdelicGroupPoints F A.toGrp) m).mp
  exact hfact ▸ hg

end Langlands.Global.RepresentationGrowth
