import Langlands.Representation.Exponents.Jacquet
import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Category.Contragredient
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Dual eigenfunctionals from generalized eigencharacters of central actions

For an admissible representation of a topological group with cofinal compact
open subgroups, a generalized eigencharacter of a family of central elements
is the eigencharacter of a nonzero functional on the whole carrier, through
the transposed action. The functional is a dual eigenvector on a
finite-dimensional space of fixed vectors, composed with the Hecke projection
onto that space.
-/

noncomputable section

namespace Langlands

namespace DualEigenfunctional

universe uK uM uι uG uA uV

section CommonKernel

variable {K : Type uK} [Field K] {ι : Type uι}

/-- Strong induction on the dimension for `exists_ne_zero_forall_apply_eq_zero`. -/
theorem exists_ne_zero_forall_apply_eq_zero_aux (d : ℕ) :
    ∀ (M : Type uM) [AddCommGroup M] [Module K M] [FiniteDimensional K M] [Nontrivial M]
      (g : ι → Module.End K M), (∀ i j, Commute (g i) (g j)) → (∀ i, IsNilpotent (g i)) →
      Module.finrank K M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, g i v = 0 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ _ g hc hn hd
  by_cases hall : ∀ i, g i = 0
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact ⟨v, hv, fun i => by rw [hall i, LinearMap.zero_apply]⟩
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  let W : Submodule K M := LinearMap.ker (g i)
  have hW : ∀ j, ∀ w ∈ W, g j w ∈ W := by
    intro j w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [← Module.End.mul_apply, (hc i j).eq, Module.End.mul_apply, hw, map_zero]
  have hWbot : W ≠ ⊥ := by
    intro h
    have hinj : Function.Injective (g i) := LinearMap.ker_eq_bot.mp h
    obtain ⟨k, hk⟩ := hn i
    have hinjk : Function.Injective ((g i) ^ k) := by
      rw [Module.End.coe_pow]
      exact hinj.iterate k
    obtain ⟨v, hv⟩ := exists_ne (0 : M)
    apply hv
    apply hinjk
    rw [hk, LinearMap.zero_apply, map_zero]
  have hWtop : W ≠ ⊤ := fun h => hi (LinearMap.ker_eq_top.mp h)
  have hlt : Module.finrank K W < d :=
    hd ▸ Submodule.finrank_lt hWtop
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWbot
  let g' : ι → Module.End K W := fun j => (g j).restrict (hW j)
  have hc' : ∀ j l, Commute (g' j) (g' l) := by
    intro j l
    refine LinearMap.ext fun w => Subtype.ext ?_
    change g j (g l w) = g l (g j w)
    exact LinearMap.congr_fun (hc j l).eq (w : M)
  have hn' : ∀ j, IsNilpotent (g' j) := fun j => Module.End.isNilpotent.restrict (hW j) (hn j)
  obtain ⟨w, hw0, hw⟩ := ih _ hlt W g' hc' hn' rfl
  refine ⟨w, fun h => hw0 (Subtype.ext h), fun j => ?_⟩
  exact congrArg Subtype.val (hw j)

/-- A commuting family of nilpotent endomorphisms of a nonzero finite-dimensional
vector space has a common nonzero kernel vector. -/
theorem exists_ne_zero_forall_apply_eq_zero {M : Type uM} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [Nontrivial M] (g : ι → Module.End K M)
    (hc : ∀ i j, Commute (g i) (g j)) (hn : ∀ i, IsNilpotent (g i)) :
    ∃ v : M, v ≠ 0 ∧ ∀ i, g i v = 0 :=
  exists_ne_zero_forall_apply_eq_zero_aux _ M g hc hn rfl

/-- Powers of a transpose evaluate through powers of the original map. -/
theorem dualMap_pow_apply {M : Type uM} [AddCommGroup M] [Module K M]
    (N : Module.End K M) (k : ℕ) (φ : Module.Dual K M) (w : M) :
    ((N.dualMap ^ k) φ) w = φ ((N ^ k) w) := by
  induction k generalizing φ with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, LinearMap.dualMap_apply, ← Module.End.mul_apply,
      ← pow_succ']

end CommonKernel

section FiniteDimensional

variable {Y : Type uM} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] {ι : Type uι}

/-- A nonzero joint generalized eigenvector of a commuting family of
endomorphisms of a finite-dimensional complex space gives a nonzero dual
eigenvector with the same eigenvalues. -/
theorem exists_dual_eigenvector (f : ι → Module.End ℂ Y) (hc : ∀ i j, Commute (f i) (f j))
    (χ : ι → ℂ) {y : Y} (hy0 : y ≠ 0) (hy : ∀ i, y ∈ (f i).maxGenEigenspace (χ i)) :
    ∃ φ : Module.Dual ℂ Y, φ ≠ 0 ∧ ∀ i w, φ (f i w) = χ i * φ w := by
  classical
  let E : (ι → ℂ) → Submodule ℂ Y := fun χ' => ⨅ i, (f i).maxGenEigenspace (χ' i)
  have hmaps : ∀ i j μ, Set.MapsTo (f i) ((f j).maxGenEigenspace μ)
      ((f j).maxGenEigenspace μ) :=
    fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) μ
  have hstab : ∀ i χ', ∀ w ∈ E χ', f i w ∈ E χ' := by
    intro i χ' w hw
    simp only [E, Submodule.mem_iInf] at hw ⊢
    exact fun j => hmaps i j (χ' j) (hw j)
  have htop : ⨆ χ', E χ' = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun i j _ => hc i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  have hind : iSupIndep E := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hmaps
  let W := E χ
  let C : Submodule ℂ Y := ⨆ (χ' : ι → ℂ) (_ : χ' ≠ χ), E χ'
  have hdisj : Disjoint W C := hind χ
  have hsup : W ⊔ C = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun χ' => ?_
    by_cases h : χ' = χ
    · subst h
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂ (f := fun χ' (_ : χ' ≠ χ) => E χ') χ' h)
  have hcompl : IsCompl W C := ⟨hdisj, codisjoint_iff.mpr hsup⟩
  have hCstab : ∀ i, ∀ c ∈ C, f i c ∈ C := by
    intro i c hc'
    have hle : C ≤ C.comap (f i) := by
      refine iSup₂_le fun χ' h => ?_
      intro w hw
      exact Submodule.mem_comap.mpr
        ((le_iSup₂ (f := fun χ' (_ : χ' ≠ χ) => E χ') χ' h) (hstab i χ' w hw))
    exact hle hc'
  have hyW : y ∈ W := by
    simp only [W, E, Submodule.mem_iInf]
    exact hy
  have : Nontrivial W := ⟨⟨⟨y, hyW⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  have hNmaps : ∀ i, Set.MapsTo (f i - algebraMap ℂ (Module.End ℂ Y) (χ i)) W W := by
    intro i w hw
    rw [LinearMap.sub_apply, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply]
    exact W.sub_mem (hstab i χ w hw) (W.smul_mem _ hw)
  let N : ι → Module.End ℂ W := fun i =>
    (f i - algebraMap ℂ (Module.End ℂ Y) (χ i)).restrict (hNmaps i)
  have hNc : ∀ i j, Commute (N i) (N j) := by
    intro i j
    have h : Commute (f i - algebraMap ℂ (Module.End ℂ Y) (χ i))
        (f j - algebraMap ℂ (Module.End ℂ Y) (χ j)) :=
      ((hc i j).sub_right (Algebra.commute_algebraMap_right _ _)).sub_left
        (Algebra.commute_algebraMap_left _ _)
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact LinearMap.congr_fun h.eq (w : Y)
  have hNn : ∀ i, IsNilpotent (N i) := by
    intro i
    have hle : W ≤ (f i).maxGenEigenspace (χ i) := by
      intro w hw
      simp only [W, E, Submodule.mem_iInf] at hw
      exact hw i
    exact Module.End.isNilpotent_restrict_of_le hle
      (Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (f i) (χ i))
  have hdc : ∀ i j, Commute (N i).dualMap (N j).dualMap := by
    intro i j
    change (N i).dualMap ∘ₗ (N j).dualMap = (N j).dualMap ∘ₗ (N i).dualMap
    rw [LinearMap.dualMap_comp_dualMap, LinearMap.dualMap_comp_dualMap]
    exact congrArg LinearMap.dualMap (hNc j i).eq
  have hdn : ∀ i, IsNilpotent (N i).dualMap := by
    intro i
    obtain ⟨k, hk⟩ := hNn i
    refine ⟨k, LinearMap.ext fun φ => LinearMap.ext fun w => ?_⟩
    rw [dualMap_pow_apply, hk]
    simp
  have : Nontrivial (Module.Dual ℂ W) := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
      by_contra h
      push Not at h
      exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).mp h)
    exact ⟨⟨φ, 0, fun h => hφ (by rw [h, LinearMap.zero_apply])⟩⟩
  obtain ⟨ψ₀, hψ₀, hψN⟩ := exists_ne_zero_forall_apply_eq_zero (fun i => (N i).dualMap) hdc hdn
  have hψ : ∀ i (w : Y) (hw : w ∈ W), ψ₀ ⟨f i w, hstab i χ w hw⟩ = χ i * ψ₀ ⟨w, hw⟩ := by
    intro i w hw
    have h0 : ψ₀ (N i ⟨w, hw⟩) = 0 := by
      have := LinearMap.congr_fun (hψN i) ⟨w, hw⟩
      simpa only [LinearMap.dualMap_apply, LinearMap.zero_apply] using this
    have hsplit : (⟨f i w, hstab i χ w hw⟩ : W) = N i ⟨w, hw⟩ + χ i • ⟨w, hw⟩ := by
      apply Subtype.ext
      simp [N, Algebra.algebraMap_eq_smul_one]
    rw [hsplit, map_add, map_smul, h0, zero_add, smul_eq_mul]
  refine ⟨ψ₀.comp (W.projectionOnto C hcompl), ?_, ?_⟩
  · intro h0
    apply hψ₀
    refine LinearMap.ext fun w => ?_
    have := LinearMap.congr_fun h0 (w : Y)
    rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_left] at this
    exact this
  · intro i v
    have hv : v ∈ W ⊔ C := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨w, hw, c, hc', rfl⟩ := Submodule.mem_sup.mp hv
    have hPw : W.projectionOnto C hcompl w = ⟨w, hw⟩ :=
      Submodule.projectionOnto_apply_of_mem_left hcompl hw
    have hPc : W.projectionOnto C hcompl c = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hcompl hc'
    have hPfw : W.projectionOnto C hcompl (f i w) = ⟨f i w, hstab i χ w hw⟩ :=
      Submodule.projectionOnto_apply_of_mem_left hcompl (hstab i χ w hw)
    have hPfc : W.projectionOnto C hcompl (f i c) = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hcompl (hCstab i c hc')
    simp only [LinearMap.comp_apply, map_add, hPw, hPc, hPfw, hPfc, map_zero, add_zero]
    exact hψ i w hw

end FiniteDimensional

section Admissible

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type uA} [Monoid A] {X : Type uV} [AddCommGroup X] [Module ℂ X]

/-- A generalized eigencharacter of central elements acting on an admissible
representation is the eigencharacter of a nonzero full-dual functional, for the
transposed action and without inversion of the character. -/
theorem exists_dualEigenfunctional_of_isGeneralizedEigencharacter
    (ρ : Representation ℂ G X) (hρ : IsAdmissible ρ) (hG : CompactOpenCofinal G)
    (z : A →* G) (hz : ∀ a, z a ∈ Subgroup.center G) (χ : A →* ℂˣ)
    (h : IsGeneralizedEigencharacter (ρ.comp z) χ) :
    ∃ φ : Module.Dual ℂ X, φ ≠ 0 ∧ ∀ a x, φ (ρ (z a) x) = (χ a : ℂ) * φ x := by
  classical
  obtain ⟨k, y, hy0, hy⟩ := (isGeneralizedEigencharacter_iff _ _).mp h
  obtain ⟨H, hyH⟩ := hρ.1 y
  obtain ⟨K, hKc, hKH⟩ := hG H
  have hyK : y ∈ fixedVectors ρ K.toSubgroup := fun g => hyH ⟨g.1, hKH g.2⟩
  have : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  let ι : A → ρ.IntertwiningMap ρ := fun a =>
    { toLinearMap := ρ (z a)
      isIntertwining' := fun g => by
        rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul,
          (Subgroup.mem_center_iff.mp (hz a) g)] }
  let f : A → Module.End ℂ (fixedVectors ρ K.toSubgroup) := fun a =>
    fixedVectorsMap (ι a) K.toSubgroup
  have hfc : ∀ a b, Commute (f a) (f b) := by
    intro a b
    refine LinearMap.ext fun w => Subtype.ext ?_
    change ρ (z a) (ρ (z b) w) = ρ (z b) (ρ (z a) w)
    rw [← Module.End.mul_apply, ← map_mul ρ, ← Module.End.mul_apply, ← map_mul ρ,
      (Subgroup.mem_center_iff.mp (hz a) (z b))]
  have hpow : ∀ (a : A) (c : ℂ) (m : ℕ) (w : fixedVectors ρ K.toSubgroup),
      (((f a - c • 1) ^ m) w : X) = ((ρ (z a) - c • 1) ^ m) (w : X) := by
    intro a c m
    induction m with
    | zero => intro w; rfl
    | succ m ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      rfl
  let y' : fixedVectors ρ K.toSubgroup := ⟨y, hyK⟩
  have hy' : ∀ a, y' ∈ (f a).maxGenEigenspace (χ a : ℂ) := by
    intro a
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨k, Subtype.ext ?_⟩
    rw [hpow]
    exact hy a
  obtain ⟨φ₀, hφ₀, heig₀⟩ := exists_dual_eigenvector f hfc (fun a => (χ a : ℂ))
    (y := y') (fun h => hy0 (congrArg Subtype.val h)) hy'
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts G :=
    ⟨⟨(K : Set G), hKc⟩, by
      simpa only [K.isOpen.interior_eq] using
        (show (K : Set G).Nonempty from ⟨1, K.one_mem⟩)⟩
  let μ : MeasureTheory.Measure G := MeasureTheory.Measure.haarMeasure K₀
  have : μ.IsHaarMeasure := MeasureTheory.Measure.isHaarMeasure_haarMeasure K₀
  let P := Hecke.fixedProjection μ ρ hρ.1 K hKc
  refine ⟨φ₀.comp P, ?_, ?_⟩
  · intro h0
    apply hφ₀
    refine LinearMap.ext fun w => ?_
    have := LinearMap.congr_fun h0 (w : X)
    rw [LinearMap.comp_apply, Hecke.fixedProjection_fixed] at this
    exact this
  · intro a x
    have hP : P (ρ (z a) x) = f a (P x) :=
      (Hecke.fixedProjection_intertwiner μ ρ hρ.1 K hKc hρ.1 (ι a) x).symm
    change φ₀ (P (ρ (z a) x)) = _ * φ₀ (P x)
    rw [hP, heig₀]

end Admissible

end DualEigenfunctional

end Langlands
