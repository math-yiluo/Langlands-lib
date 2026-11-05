import Langlands.Algebra.SandwichDimensionBoundProof
import Langlands.Representation.CompactCoefficient.FixedLevelFiniteness
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Dimension and compression bounds at one compact-open level -/

noncomputable section

namespace Langlands.Hecke

open MeasureTheory

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- Finite sandwich data in the actual compact-open Hecke corner. The data
depend on the level and measure, before any representation is chosen. -/
structure FixedLevelSandwich where
  size : ℕ
  generators : ℕ
  edge : Fin size → HeckeAlgebra.Corner μ K hK
  middle : Fin generators → HeckeAlgebra.Corner μ K hK
  commute : ∀ i j, Commute (middle i) (middle j)
  span : Submodule.span ℂ
    {y | ∃ i j, ∃ m ∈ Algebra.adjoin ℂ (Set.range middle),
      y = edge i * m * edge j} = ⊤

namespace FixedLevelSandwich

variable {μ K hK}

/-- A bound determined solely by the sandwich data at the level. -/
def dimensionBound (D : FixedLevelSandwich μ K hK) : ℕ :=
  D.size ^ (2 ^ D.generators)

/-- Every irreducible smooth representation with finite-dimensional fixed
vectors obeys the same numerical bound. This includes a zero fixed space. -/
theorem finrank_le (D : FixedLevelSandwich μ K hK)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (hirr : ρ.IsIrreducible)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)) :
    Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ D.dimensionBound := by
  by_cases h0 : fixedVectors ρ K.toSubgroup = ⊥
  · let := hfin
    rw [Submodule.finrank_eq_zero.mpr h0]
    exact Nat.zero_le _
  · let := hfin
    let := cornerModule μ ρ hρ K hK
    let := cornerModule_isScalarTower μ ρ hρ K hK
    exact sandwichSimpleModuleDimensionBound (HeckeAlgebra.Corner μ K hK)
      D.size D.generators D.edge D.middle D.commute D.span
      (fixedVectors ρ K.toSubgroup)
      (CompactCoefficientClass.isSimpleModule_fixedVectors μ ρ hρ K hK hirr h0) hfin

/-- Compact smooth-dual coefficients supply the finite-dimensionality needed
by the common dimension bound, without assuming admissibility. -/
theorem finrank_le_of_compactCoefficients (D : FixedLevelSandwich μ K hK)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (hirr : ρ.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients ρ) :
    Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ D.dimensionBound :=
  D.finrank_le ρ hρ hirr
    (CompactCoefficientClass.finiteDimensional_fixedVectors μ ρ hρ K hK hirr hc)

end FixedLevelSandwich

end Langlands.Hecke

namespace Langlands.Jacquet

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
  {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
  {N M Nbar : Subgroup G} {g : G}

omit [IsTopologicalGroup G] in
/-- The lower contraction inclusion holds for all nonnegative powers. -/
theorem IsIwahoriContraction.lower_pow (h : IsIwahoriContraction K N M Nbar g)
    (s : ℕ) : ∀ l ∈ K.toSubgroup ⊓ Nbar,
      (g ^ s)⁻¹ * l * g ^ s ∈ K.toSubgroup ⊓ Nbar := by
  induction s with
  | zero => intro l hl; simpa using hl
  | succ s ih =>
    intro l hl
    have e : (g ^ (s + 1))⁻¹ * l * g ^ (s + 1) =
        g⁻¹ * ((g ^ s)⁻¹ * l * g ^ s) * g := by group
    rw [e]
    exact h.lower _ (ih l hl)

/-- When the Jacquet coinvariants vanish, a bound on the dimension of the
fixed space is a nilpotence exponent for actual compact compression. -/
theorem compressedAction_pow_eq_zero_of_relations_eq_top
    (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (hrel : relations ρ N = ⊤)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (d : ℕ) (hd : Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ d) :
    compressedAction ρ hρ K hK g ^ d = 0 := by
  let := hfin
  let C := compressedAction ρ hρ K hK g
  have hker : powerKernelSup ρ hρ K hK g = ⊤ := by
    rw [powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK h hMN]
    apply top_unique
    intro v _
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change mk ρ N v.val = 0
    rw [mk_eq_zero, hrel]
    exact Submodule.mem_top
  have hle : powerKernelSup ρ hρ K hK g ≤ LinearMap.ker (C ^ d) := by
    apply iSup_le
    intro r
    rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le hd]
    exact Module.End.ker_pow_le_ker_pow_finrank C r
  apply LinearMap.ext
  intro v
  exact hle (hker.symm ▸ Submodule.mem_top)

/-- The same exponent kills compression by the actual group power. -/
theorem compressedAction_group_pow_eq_zero_of_relations_eq_top
    (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (hrel : relations ρ N = ⊤)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (d : ℕ) (hd : Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ d) :
    compressedAction ρ hρ K hK (g ^ d) = 0 := by
  rw [h.compressedAction_pow ρ hρ hK]
  exact compressedAction_pow_eq_zero_of_relations_eq_top ρ hρ hK h hMN hrel hfin d hd

/-- An adapted left factor preserves the common vanishing exponent. This is
the operator factorization used outside the bounded positive chamber box. -/
theorem compressedAction_mul_pow_eq_zero_of_relations_eq_top
    (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (hrel : relations ρ N = ⊤)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (d : ℕ) (hd : Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ d)
    (a : G) (ha : ∀ n ∈ K.toSubgroup ⊓ N, a * n * a⁻¹ ∈ K) :
    compressedAction ρ hρ K hK (a * g ^ d) = 0 := by
  rw [compressedAction_mul_of_factor ρ hρ K hK N M Nbar h.factor a (g ^ d)
    ha (fun n hn => (h.lower_pow d n hn).1)
    (fun m hm => (h.levi_pow d m hm).1),
    compressedAction_group_pow_eq_zero_of_relations_eq_top
      ρ hρ hK h hMN hrel hfin d hd, mul_zero]

include hρ hK in
/-- Every invariant linear output vanishes on the same adapted translates
of every fixed vector. The bound is independent of both coefficient inputs. -/
theorem invariant_map_mul_pow_eq_zero_of_relations_eq_top
    (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (hrel : relations ρ N = ⊤)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (d : ℕ) (hd : Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ d)
    (a : G) (ha : ∀ n ∈ K.toSubgroup ⊓ N, a * n * a⁻¹ ∈ K)
    (L : V →ₗ[ℂ] W) (hL : ∀ k ∈ K, ∀ w, L (ρ k w) = L w)
    (v : fixedVectors ρ K.toSubgroup) :
    L (ρ (a * g ^ d) v.val) = 0 := by
  have hz : Compact.averageMap ρ hρ K hK (ρ (a * g ^ d) v.val) = 0 := by
    have he := LinearMap.congr_fun
      (compressedAction_mul_pow_eq_zero_of_relations_eq_top
        ρ hρ hK h hMN hrel hfin d hd a ha) v
    exact congrArg Subtype.val he
  rw [← map_averageMap_of_forall_eq ρ hρ K hK L
    (ρ (a * g ^ d) v.val) _ (fun k => hL k k.property _), hz, map_zero]

end Langlands.Jacquet
