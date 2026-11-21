import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations
import Langlands.Representation.Archimedean.SmoothIntertwiner
import Langlands.Representation.Archimedean.SmoothFixedSubspace
import Langlands.Representation.Smooth.SmoothPart.Definitions
import Langlands.Topology.CompactOpen.OpenSubgroup

/-! # Genuine smooth vectors for commuting finite and archimedean actions -/

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace Langlands.Archimedean.MixedSmooth

open Langlands.HarishChandraSchwartz SmoothInvariantSubspace

universe uA uG uL uE

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  {L : Type uL} [Group L]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (σ : L →* (E →L[ℂ] E)) (π : G →* (E →L[ℂ] E))
  (hcomm : ∀ g l x, π g (σ l x) = σ l (π g x))

local notation "I" => 𝓘(ℝ, A)
local notation "V∞" => Langlands.Archimedean.smoothVectors I π

/-- A bounded finite translation gives a linear operator on genuine
archimedean smooth vectors. -/
def finiteOnSmooth : Representation ℂ L V∞ where
  toFun l := SmoothIntertwiner.map I π π (σ l) (fun g x => (hcomm g l x).symm)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change σ 1 v.val = v.val
    simp
  map_mul' l d := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change σ (l * d) v.val = σ l (σ d v.val)
    simp

@[simp]
theorem finiteOnSmooth_val (l : L) (v : V∞) :
    (finiteOnSmooth σ π hcomm l v).val = σ l v.val :=
  rfl

/-- The smooth part of the finite representation on genuine archimedean
smooth vectors. -/
abbrev Vectors [TopologicalSpace L] :=
  Langlands.smoothVectors (finiteOnSmooth (A := A) σ π hcomm)

/-- The fixed-space condition on the smooth vector is exactly the original
bounded fixed-space condition on its underlying Hilbert vector. -/
theorem mem_fixedVectors_finiteOnSmooth (J : Subgroup L) (v : V∞) :
    v ∈ Langlands.fixedVectors (finiteOnSmooth σ π hcomm) J ↔
      v.val ∈ fixedSubspace σ J := by
  constructor
  · intro h l
    exact congrArg Subtype.val (h l)
  · intro h l
    exact Subtype.ext (h l)

variable [TopologicalSpace L]

/-- Compact open levels suffice to witness the finite smoothness of a
genuine archimedean smooth vector. -/
theorem exists_compactLevel [LocallyCompactSpace L] [NonarchimedeanGroup L]
    (v : Vectors (A := A) σ π hcomm) :
    ∃ J : CompactOpenSubgroup L, v.val.val ∈ fixedSubspace σ J.toSubgroup := by
  obtain ⟨K, hK⟩ := v.property
  obtain ⟨J, hJ, hJK⟩ := openSubgroupContainsCompactOpen L K
  exact ⟨⟨J, hJ⟩,
    fun l => congrArg Subtype.val (hK ⟨l.val, hJK l.property⟩)⟩

/-- A fixed genuine smooth vector belongs to the mixed smooth space. -/
def ofFixed (J : OpenSubgroup L) (v : V∞) (hv : v.val ∈ fixedSubspace σ J.toSubgroup) :
    Vectors (A := A) σ π hcomm :=
  ⟨v, ⟨J, (mem_fixedVectors_finiteOnSmooth σ π hcomm J.toSubgroup v).mpr hv⟩⟩

@[simp]
theorem ofFixed_val (J : OpenSubgroup L) (v : V∞) (hv : v.val ∈ fixedSubspace σ J.toSubgroup) :
    (ofFixed σ π hcomm J v hv).val = v :=
  rfl

variable [IsTopologicalGroup L]

/-- The actual finite action on the mixed smooth space. -/
abbrev finiteRepresentation : Representation ℂ L (Vectors (A := A) σ π hcomm) :=
  Langlands.smoothPart (finiteOnSmooth (A := A) σ π hcomm)

@[simp]
theorem finiteRepresentation_val (l : L) (v : Vectors (A := A) σ π hcomm) :
    (finiteRepresentation σ π hcomm l v).val = finiteOnSmooth σ π hcomm l v.val :=
  rfl

/-- Finite translation identifies the fixed condition at `J` with that at `l J l⁻¹`. -/
theorem finiteOnSmooth_fixed_conj_iff (l : L) (J : CompactOpenSubgroup L) (v : V∞) :
    (finiteOnSmooth σ π hcomm l v).val ∈ fixedSubspace σ (J.conj l).toSubgroup ↔
      v.val ∈ fixedSubspace σ J.toSubgroup := by
  let ρ := finiteOnSmooth (A := A) σ π hcomm
  rw [← mem_fixedVectors_finiteOnSmooth σ π hcomm (J.conj l).toSubgroup (ρ l v),
    ← mem_fixedVectors_finiteOnSmooth σ π hcomm J.toSubgroup v]
  constructor
  · intro hv j
    let k : (J.conj l).toSubgroup :=
      ⟨l * (j : L) * l⁻¹, mem_conjSubgroup.mpr (by simp [mul_assoc, j.property])⟩
    change ρ (j : L) v = v
    apply (ρ.apply_bijective l).injective
    have heq : l * (j : L) = (k : L) * l := by
      dsimp [k]
      group
    rw [← Module.End.mul_apply, ← map_mul, heq, map_mul, Module.End.mul_apply]
    exact hv k
  · intro hv k
    let j : J.toSubgroup := ⟨l⁻¹ * (k : L) * l, mem_conjSubgroup.mp k.property⟩
    change ρ (k : L) (ρ l v) = ρ l v
    have heq : (k : L) * l = l * (j : L) := by
      dsimp [j]
      group
    rw [← Module.End.mul_apply, ← map_mul, heq, map_mul, Module.End.mul_apply]
    exact congrArg (ρ l) (hv j)

/-- Finite translation carries a fixed vector to the conjugate level. -/
theorem finiteOnSmooth_fixed_conj (l : L) (J : CompactOpenSubgroup L) (v : V∞)
    (hv : v.val ∈ fixedSubspace σ J.toSubgroup) :
    (finiteOnSmooth σ π hcomm l v).val ∈ fixedSubspace σ (J.conj l).toSubgroup :=
  (finiteOnSmooth_fixed_conj_iff σ π hcomm l J v).mpr hv

/-- The finite action on mixed smooth vectors transports fixedness to the conjugate level. -/
theorem finiteRepresentation_fixed_conj_iff (l : L) (J : CompactOpenSubgroup L)
    (v : Vectors (A := A) σ π hcomm) :
    (finiteRepresentation σ π hcomm l v).val.val ∈ fixedSubspace σ (J.conj l).toSubgroup ↔
      v.val.val ∈ fixedSubspace σ J.toSubgroup :=
  finiteOnSmooth_fixed_conj_iff σ π hcomm l J v.val

omit [IsTopologicalGroup L]

variable [LieGroup 𝓘(ℝ, A) ∞ G]

omit [TopologicalSpace L] in
include hcomm in
/-- Archimedean translation preserves the same finite level. -/
theorem smoothRepresentation_fixed (g : G) (J : Subgroup L) (v : V∞)
    (hv : v.val ∈ fixedSubspace σ J) :
    (smoothRepresentation I π g v).val ∈ fixedSubspace σ J :=
  fixedSubspace_invariant σ J π hcomm g v.val hv

omit [TopologicalSpace L] in
include hcomm in
/-- Archimedean translation and its inverse both preserve the same finite level. -/
theorem smoothRepresentation_fixed_iff (g : G) (J : Subgroup L) (v : V∞) :
    (smoothRepresentation I π g v).val ∈ fixedSubspace σ J ↔
      v.val ∈ fixedSubspace σ J := by
  constructor
  · intro hv
    simpa only [Representation.inv_self_apply] using
      (smoothRepresentation_fixed σ π hcomm g⁻¹ J (smoothRepresentation I π g v) hv)
  · exact smoothRepresentation_fixed σ π hcomm g J v

/-- Genuine archimedean translation on the mixed smooth space. -/
def archimedeanRepresentation : Representation ℂ G (Vectors (A := A) σ π hcomm) where
  toFun g := ((smoothRepresentation I π g).comp (Vectors (A := A) σ π hcomm).subtype).codRestrict
    (Vectors (A := A) σ π hcomm) fun v => by
      obtain ⟨J, hJ⟩ := v.property
      have hv := (mem_fixedVectors_finiteOnSmooth σ π hcomm J.toSubgroup v.val).mp hJ
      exact ⟨J, (mem_fixedVectors_finiteOnSmooth σ π hcomm J.toSubgroup _).mpr
        (smoothRepresentation_fixed σ π hcomm g J.toSubgroup v.val hv)⟩
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change smoothRepresentation I π 1 v.val = v.val
    simp
  map_mul' g a := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change smoothRepresentation I π (g * a) v.val =
      smoothRepresentation I π g (smoothRepresentation I π a v.val)
    simp only [map_mul, Module.End.mul_apply]

@[simp]
theorem archimedeanRepresentation_val (g : G) (v : Vectors (A := A) σ π hcomm) :
    (archimedeanRepresentation σ π hcomm g v).val = smoothRepresentation I π g v.val :=
  rfl

/-- The archimedean action on mixed smooth vectors preserves and reflects fixedness at `J`. -/
theorem archimedeanRepresentation_fixed_iff (g : G) (J : Subgroup L)
    (v : Vectors (A := A) σ π hcomm) :
    (archimedeanRepresentation σ π hcomm g v).val.val ∈ fixedSubspace σ J ↔
      v.val.val ∈ fixedSubspace σ J :=
  smoothRepresentation_fixed_iff σ π hcomm g J v.val

/-- The two actual actions commute on the mixed smooth space. -/
theorem archimedeanRepresentation_finite_commute [IsTopologicalGroup L]
    (g : G) (l : L) (v : Vectors (A := A) σ π hcomm) :
    archimedeanRepresentation σ π hcomm g (finiteRepresentation σ π hcomm l v) =
      finiteRepresentation σ π hcomm l (archimedeanRepresentation σ π hcomm g v) := by
  apply Subtype.ext
  apply Subtype.ext
  exact hcomm g l v.val.val

end Langlands.Archimedean.MixedSmooth
