import Langlands.BaseChange.OrbitalIntegral
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.Analysis.Local.FiniteExtensionNormedField
import Langlands.Group.GL.NormCongruence

/-!
# Twisted descent in congruence subgroups for cyclic base change

For a field `F`, a field `E` that is a cyclic `F`-algebra of group `⟨σ⟩` of order `l`
(`IsCyclicAlgebra σ l`) and `n : ℕ`:

* `IsTwistedDescentSubgroup F σ l K`: a subgroup `K` of `GL_n(E)` stable under `σ`, such that an
  element of `GL_n(E)` that σ-conjugates two rational elements of `K` is rational, and two rational
  elements `u`, `u'` of `K` with `y⁻¹ u^l y = u'^l` (`y ∈ GL_n(F)`) satisfy `y⁻¹ u y = u'`;
* on such a `K`, the σ-centralizer of a rational `u ∈ K` is the image of the centralizer of `u^l`
  in `GL_n(F)` (`IsTwistedDescentSubgroup.sigmaCentralizer_eq`);
* over a nonarchimedean local field `F`, with the spectral norm on `E`
  (`LocalGalois.finiteExtensionNormedField`): for `0 ≤ r < ‖l‖` the congruence subgroup
  `normCongruenceSubgroup E n` of radius `r` is a descent subgroup; every element of
  `u₀ · normCongruence E n (r ‖l‖)` (`u₀` rational in `normCongruence F n r`) is σ-conjugate by an
  element of `normCongruence E n r` to a rational element `u₀ u`, `u ∈ normCongruence F n r`; the set
  `{κ⁻¹ u κ^σ}` of such σ-conjugates is open for `r > 0`; and the `l`-th power map sends
  `normCongruence F n r` onto `normCongruence F n (r ‖l‖)`.

See the paired Markdown.
-/

noncomputable section

open Matrix Set Topology

namespace Langlands.BaseChange

open Langlands.GeneralLinear Langlands.TraceFormula

universe u v

section Algebra

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] {n : ℕ}

/-- The scalar extension `GL_n(F) → GL_n(E)` is injective. -/
theorem baseChange_injective : Function.Injective (baseChange F E n) := fun x y h => by
  ext i j
  exact (algebraMap F E).injective (congrArg (fun g : GeneralLinear n E => (g : Matrix _ _ E) i j) h)

/-- The norm of a rational element is its `l`-th power. -/
theorem cyclicNorm_baseChange (σ : E ≃ₐ[F] E) (l : ℕ) (y : GeneralLinear n F) :
    cyclicNorm σ l (baseChange F E n y) = baseChange F E n (y ^ l) := by
  simpa [cyclicNorm, map_pow] using cyclicNorm_mul_baseChange σ l 1 y (Commute.one_left _)

variable (F) in
/-- A subgroup `K` of `GL_n(E)` on which σ-conjugacy and `l`-th powers descend (Henniart–Lemaire
I.2.2 near the identity): `K` is stable under `σ`; an element of `GL_n(E)` σ-conjugating two rational
elements of `K` is rational; and two rational elements of `K` whose `l`-th powers are conjugate under
`GL_n(F)` are conjugate by the same element. -/
structure IsTwistedDescentSubgroup (σ : E ≃ₐ[F] E) (l : ℕ) (K : Subgroup (GeneralLinear n E)) :
    Prop where
  entrywiseAut_mem : ∀ g ∈ K, entrywiseAut σ n g ∈ K
  rational_of_twistedConj : ∀ (u u' : GeneralLinear n F), baseChange F E n u ∈ K →
    baseChange F E n u' ∈ K → ∀ g : GeneralLinear n E,
      g⁻¹ * baseChange F E n u * entrywiseAut σ n g = baseChange F E n u' →
        ∃ x : GeneralLinear n F, baseChange F E n x = g
  conj_of_conj_pow : ∀ (u u' : GeneralLinear n F), baseChange F E n u ∈ K →
    baseChange F E n u' ∈ K → ∀ y : GeneralLinear n F, y⁻¹ * u ^ l * y = u' ^ l →
      y⁻¹ * u * y = u'

/-- On a descent subgroup, the σ-centralizer of a rational element `u` of `K` is the image of the
centralizer of `u ^ l` in `GL_n(F)` (source `cent_eq`). -/
theorem IsTwistedDescentSubgroup.sigmaCentralizer_eq {σ : E ≃ₐ[F] E} {l : ℕ}
    {K : Subgroup (GeneralLinear n E)} (hK : IsTwistedDescentSubgroup F σ l K)
    {u : GeneralLinear n F} (hu : baseChange F E n u ∈ K) :
    sigmaCentralizer σ n (baseChange F E n u) = (glCentralizer (u ^ l)).map (baseChange F E n) := by
  ext x
  rw [mem_twistedCentralizer, Subgroup.mem_map]
  constructor
  · intro h
    obtain ⟨z, rfl⟩ := hK.rational_of_twistedConj u u hu hu x h
    refine ⟨z, ?_, rfl⟩
    rw [entrywiseAut_baseChange, ← map_inv, ← map_mul, ← map_mul] at h
    have h1 := baseChange_injective h
    rw [mem_twistedCentralizer, MonoidHom.id_apply]
    have hc := conj_pow (a := z⁻¹) (b := u) (i := l)
    rw [inv_inv] at hc
    rw [← hc, h1]
  · rintro ⟨z, hz, rfl⟩
    rw [mem_twistedCentralizer, MonoidHom.id_apply] at hz
    have h1 := hK.conj_of_conj_pow u u hu hu z hz
    rw [entrywiseAut_baseChange, ← map_inv, ← map_mul, ← map_mul, h1]

end Algebra


section Spectral

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [Algebra F E] [FiniteDimensional F E] [TopologicalSpace E]
  [IsModuleTopology F E] {n : ℕ}

/-- Membership of a rational element in the spectral congruence neighbourhood of `GL_n(E)` is
membership in that of `GL_n(F)` with the same radius. -/
theorem baseChange_mem_normCongruence_iff (r : ℝ) (γ : GeneralLinear n F) :
    letI := LocalGalois.localNormedField F
    letI := LocalGalois.finiteExtensionNormedField F E
    baseChange F E n γ ∈ normCongruence E n r ↔ γ ∈ normCongruence F n r := by
  let := LocalGalois.localNormedField F
  let := LocalGalois.finiteExtensionNormedField F E
  exact map_mem_normCongruence_iff (algebraMap F E)
    (LocalGalois.finiteExtensionNormedField_norm_algebraMap F E) γ

/-- The spectral congruence neighbourhoods of `GL_n(E)` are stable under `σ`. -/
theorem entrywiseAut_mem_normCongruence_iff (σ : E ≃ₐ[F] E) (r : ℝ) (g : GeneralLinear n E) :
    letI := LocalGalois.finiteExtensionNormedField F E
    entrywiseAut σ n g ∈ normCongruence E n r ↔ g ∈ normCongruence E n r := by
  let := LocalGalois.finiteExtensionNormedField F E
  exact map_mem_normCongruence_iff (σ : E →+* E)
    (LocalGalois.finiteExtensionNormedField_norm_algEquiv F E σ) g

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E]
  [TopologicalSpace E] [IsModuleTopology F E] in
private theorem iterate_algEquiv (σ : E ≃ₐ[F] E) (j : ℕ) (x : E) :
    (σ : E →+* E)^[j] x = (σ ^ j) x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, pow_succ', AlgEquiv.mul_apply]; rfl

/-- For `0 ≤ r < ‖l‖` (`r < 1`), the spectral congruence subgroup of radius `r` is a descent
subgroup. -/
theorem isTwistedDescentSubgroup_normCongruence {σ : E ≃ₐ[F] E} {l : ℕ}
    (hσ : IsCyclicAlgebra σ l) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    letI := LocalGalois.localNormedField F
    letI := LocalGalois.finiteExtensionNormedField F E
    letI := LocalGalois.finiteExtensionNormedField_ultrametric F E
    r < ‖(l : F)‖ → IsTwistedDescentSubgroup F σ l (normCongruenceSubgroup E n hr₀ hr₁) := by
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_ultrametric F
  let := LocalGalois.finiteExtensionNormedField F E
  let := LocalGalois.finiteExtensionNormedField_ultrametric F E
  intro hr
  have hrE : r < ‖(l : E)‖ := by rwa [LocalGalois.finiteExtensionNormedField_norm_natCast F E l]
  refine ⟨fun g hg => (entrywiseAut_mem_normCongruence_iff σ r g).mpr hg, ?_, ?_⟩
  · intro u u' hu hu' g hg
    have hN := congrArg (cyclicNorm σ l) hg
    rw [cyclicNorm_twistedConj, hσ.pow_eq_one, entrywiseAut_one_apply, cyclicNorm_baseChange,
      cyclicNorm_baseChange, map_pow, map_pow] at hN
    have h1 := conj_eq_of_conj_pow_eq hr₀ hrE hu hu' g hN
    have h2 : entrywiseAut σ n g = g := by
      have h3 : g⁻¹ * baseChange F E n u * entrywiseAut σ n g =
          g⁻¹ * baseChange F E n u * g := hg.trans h1.symm
      exact mul_left_cancel h3
    exact hσ.exists_baseChange_eq_of_entrywiseAut_eq h2
  · intro u u' hu hu' y hy
    have hu₁ : u ∈ normCongruence F n r := (baseChange_mem_normCongruence_iff r u).mp hu
    have hu'₁ : u' ∈ normCongruence F n r := (baseChange_mem_normCongruence_iff r u').mp hu'
    exact conj_eq_of_conj_pow_eq hr₀ hr hu₁ hu'₁ y hy

/-- Twisted descent in the spectral congruence neighbourhoods (source `OpenNear`): for
`0 ≤ r < ‖l‖`, `u₀ ∈ normCongruence F n r` and `g ∈ normCongruence E n (r * ‖l‖)`, there are
`κ ∈ normCongruence E n r` and `u ∈ normCongruence F n r` with `u₀ g = κ⁻¹ (u₀ u) κ^σ`. -/
theorem exists_twistedConj_baseChange_mul_eq {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : IsCyclicAlgebra σ l)
    {r : ℝ} (hr₀ : 0 ≤ r) :
    letI := LocalGalois.localNormedField F
    letI := LocalGalois.finiteExtensionNormedField F E
    r < ‖(l : F)‖ → ∀ {u₀ : GeneralLinear n F}, u₀ ∈ normCongruence F n r →
      ∀ {g : GeneralLinear n E}, g ∈ normCongruence E n (r * ‖(l : F)‖) →
        ∃ κ ∈ normCongruence E n r, ∃ u ∈ normCongruence F n r,
          baseChange F E n u₀ * g =
            κ⁻¹ * baseChange F E n (u₀ * u) * entrywiseAut σ n κ := by
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_ultrametric F
  let := LocalGalois.finiteExtensionNormedField F E
  let := LocalGalois.finiteExtensionNormedField_ultrametric F E
  let := LocalGalois.finiteExtensionNormedField_properSpace F E
  intro hr u₀ hu₀ g hg
  have hnat := LocalGalois.finiteExtensionNormedField_norm_natCast F E l
  have hrE : r < ‖(l : E)‖ := by rwa [hnat]
  have hτq : ∀ x : E, (σ : E →+* E)^[l] x = x := fun x => by
    rw [iterate_algEquiv, hσ.pow_eq_one, AlgEquiv.one_apply]
  have hu₀E : baseChange F E n u₀ ∈ normCongruence E n r :=
    (baseChange_mem_normCongruence_iff r u₀).mpr hu₀
  rw [← hnat] at hg
  obtain ⟨κ, hκ, u, hu, hfix, he⟩ := exists_mul_eq_twistedConj (σ : E →+* E)
    (LocalGalois.finiteExtensionNormedField_norm_algEquiv F E σ) hτq hr₀ le_rfl hrE hu₀E hg
  obtain ⟨x, rfl⟩ := hσ.exists_baseChange_eq_of_entrywiseAut_eq (g := u) hfix
  refine ⟨κ, hκ, x, (baseChange_mem_normCongruence_iff r x).mp hu, ?_⟩
  rw [map_mul]
  exact he

/-- For `0 < r < ‖l‖`, the set `{κ⁻¹ u κ^σ | κ ∈ normCongruence E n r, u ∈ normCongruence F n r}`
is open in `GL_n(E)`. -/
theorem isOpen_twistedConj_normCongruence [IsTopologicalRing E] {σ : E ≃ₐ[F] E} {l : ℕ}
    (hσ : IsCyclicAlgebra σ l) {r : ℝ} (hr₀ : 0 < r) :
    letI := LocalGalois.localNormedField F
    letI := LocalGalois.finiteExtensionNormedField F E
    r < ‖(l : F)‖ →
      IsOpen {g : GeneralLinear n E | ∃ κ ∈ normCongruence E n r, ∃ u ∈ normCongruence F n r,
        g = κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ} := by
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_ultrametric F
  let := LocalGalois.finiteExtensionNormedField F E
  let := LocalGalois.finiteExtensionNormedField_ultrametric F E
  intro hr
  have hl0 : 0 < ‖(l : F)‖ := hr₀.trans hr
  have hr₁ : r < 1 := hr.trans_le (IsUltrametricDist.norm_natCast_le_one F l)
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨κ₀, hκ₀, u₀, hu₀, rfl⟩
  let e : GeneralLinear n E ≃ₜ GeneralLinear n E :=
    (Homeomorph.mulLeft (κ₀⁻¹ * baseChange F E n u₀)).trans
      (Homeomorph.mulRight (entrywiseAut σ n κ₀))
  have hopen : IsOpen (e '' normCongruence E n (r * ‖(l : F)‖)) :=
    e.isOpenMap _ (isOpen_normCongruence (mul_pos hr₀ hl0))
  have hmem : κ₀⁻¹ * baseChange F E n u₀ * entrywiseAut σ n κ₀ ∈
      e '' normCongruence E n (r * ‖(l : F)‖) :=
    ⟨1, one_mem_normCongruence (mul_pos hr₀ hl0).le, by simp [e]⟩
  refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨κ, hκ, u, hu, he⟩ := exists_twistedConj_baseChange_mul_eq hσ hr₀.le hr hu₀ hg
  refine ⟨κ * κ₀, mul_mem_normCongruence hr₀.le hr₁.le hκ hκ₀, u₀ * u,
    mul_mem_normCongruence hr₀.le hr₁.le hu₀ hu, ?_⟩
  change κ₀⁻¹ * baseChange F E n u₀ * g * entrywiseAut σ n κ₀ = _
  rw [mul_assoc (κ₀⁻¹) _ g, he, map_mul, map_mul, _root_.mul_inv_rev]
  group

/-- For `0 ≤ r < ‖l‖`, the `l`-th power map sends `normCongruence F n r` onto
`normCongruence F n (r * ‖l‖)`. -/
theorem pow_image_normCongruence {l : ℕ} {r : ℝ} (hr₀ : 0 ≤ r) :
    letI := LocalGalois.localNormedField F
    r < ‖(l : F)‖ →
      (fun u : GeneralLinear n F => u ^ l) '' normCongruence F n r =
        normCongruence F n (r * ‖(l : F)‖) := by
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_ultrametric F
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  intro hr
  ext γ
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact pow_mem_normCongruence hr₀ hr hu
  · intro hγ
    obtain ⟨u, hu, rfl⟩ := exists_pow_eq hr₀ hr hγ
    exact ⟨u, hu, rfl⟩

end Spectral

end Langlands.BaseChange
