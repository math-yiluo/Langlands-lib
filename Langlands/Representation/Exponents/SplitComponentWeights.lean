import Langlands.Representation.Exponents.Jacquet
import Langlands.Representation.Exponents.Central
import Langlands.Representation.Exponents.SmoothOpenKernelProof
import Langlands.Representation.Smooth.FixedVectors.FiniteTypes
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations

/-!
# Compact-open generalized weight spaces of a central action

Renard, *Représentations des groupes réductifs p-adiques* (9 July 2026), VII.1.1,
printed p.220/PDF p.226. A group `A` acts on a representation `π` of `M` through a
homomorphism `ι : A →* M` with central image. For a compact open subgroup `K` of `M`
and a character `χ` of `A`, the `K`-fixed generalized character space consists of the
`K`-fixed vectors killed by one power `d` of every `π(ι t) - χ(t)`. The generalized
weight subrepresentation is their union over compact open `K` and powers `d`.

The algebra reuses `characterSpace` and `IsGeneralizedEigencharacter` from
`Langlands.Representation.Exponents.Jacquet`. No decomposition or finiteness is asserted.
-/

noncomputable section

open Topology

namespace Langlands

universe uR uA uM uV uW uX

open HarishChandraSchwartz (CompactOpenSubgroup conjSubgroup mem_conjSubgroup)

/-- A weakly locally compact nonarchimedean group has a compact open subgroup. -/
theorem nonempty_compactOpenSubgroup (M : Type uM) [Group M] [TopologicalSpace M]
    [NonarchimedeanGroup M] [WeaklyLocallyCompactSpace M] :
    Nonempty (CompactOpenSubgroup M) := by
  obtain ⟨K, hK, -⟩ := compactOpenSubgroupBasis M Set.univ Filter.univ_mem
  exact ⟨⟨K, hK⟩⟩

section Power

variable {R : Type uR} [CommRing R] {A : Type uA} [Monoid A]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]

/-- The uniform character spaces increase with the power. -/
theorem characterSpace_mono (π : Representation R A V) (χ : A →* Rˣ) :
    Monotone (characterSpace π χ) := by
  intro m n hmn
  apply iInf_mono
  intro a
  exact (Module.End.genEigenspace (π a) (χ a : R)).monotone
    (show (m : ℕ∞) ≤ (n : ℕ∞) by exact_mod_cast hmn)

/-- A linear map commuting with the two actions preserves each uniform character space. -/
theorem map_mem_characterSpace_of_intertwining {π : Representation R A V} {σ : Representation R A W}
    (f : V →ₗ[R] W) (hf : ∀ a : A, (σ a).comp f = f.comp (π a)) (χ : A →* Rˣ) (d : ℕ)
    {v : V} (hv : v ∈ characterSpace π χ d) : f v ∈ characterSpace σ χ d := by
  simp only [characterSpace, Submodule.mem_iInf] at hv ⊢
  intro a
  exact Module.End.mapsTo_genEigenspace_of_comp f (hf a) (χ a : R) d (hv a)

end Power

section Fixed

variable {R : Type uR} [CommRing R] {A : Type uA} [Group A] {M : Type uM} [Group M]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  {X : Type uX} [AddCommGroup X] [Module R X]

variable (π : Representation R M V) (ι : A →* M) (χ : A →* Rˣ)

/-- The `K`-fixed vectors killed by the `d`-th power of every `π(ι t) - χ(t)`, with the
same `d` for all `t`. -/
def fixedCharacterSpace (K : Subgroup M) (d : ℕ) : Submodule R V :=
  fixedVectors π K ⊓ characterSpace (π.comp ι) χ d

theorem mem_fixedCharacterSpace (K : Subgroup M) (d : ℕ) (v : V) :
    v ∈ fixedCharacterSpace π ι χ K d ↔
      v ∈ fixedVectors π K ∧ ∀ t : A, ((π (ι t) - (χ t : R) • 1) ^ d) v = 0 := by
  rw [fixedCharacterSpace, Submodule.mem_inf, mem_characterSpace]
  rfl

/-- Renard's `(r V)^{K_M}_χ`: the `K`-fixed vectors killed by some single power of every
`π(ι t) - χ(t)`. -/
def fixedGeneralizedCharacterSpace (K : Subgroup M) : Submodule R V :=
  ⨆ d : ℕ, fixedCharacterSpace π ι χ K d

/-- The fixed character spaces increase with the power. -/
theorem fixedCharacterSpace_mono (K : Subgroup M) :
    Monotone (fixedCharacterSpace π ι χ K) :=
  fun _ _ h => inf_le_inf_left _ (characterSpace_mono (π.comp ι) χ h)

/-- The fixed character spaces increase as the subgroup shrinks. -/
theorem fixedCharacterSpace_antitone (d : ℕ) :
    Antitone (fun K : Subgroup M => fixedCharacterSpace π ι χ K d) :=
  fun _ _ h => inf_le_inf_right _ (fixedVectors_antitone π h)

theorem mem_fixedGeneralizedCharacterSpace (K : Subgroup M) (v : V) :
    v ∈ fixedGeneralizedCharacterSpace π ι χ K ↔
      v ∈ fixedVectors π K ∧
        ∃ d : ℕ, ∀ t : A, ((π (ι t) - (χ t : R) • 1) ^ d) v = 0 := by
  rw [fixedGeneralizedCharacterSpace,
    Submodule.mem_iSup_of_directed _ (fixedCharacterSpace_mono π ι χ K).directed_le]
  simp only [mem_fixedCharacterSpace]
  constructor
  · rintro ⟨d, hv, hd⟩
    exact ⟨hv, d, hd⟩
  · rintro ⟨hv, d, hd⟩
    exact ⟨d, hv, hd⟩

theorem fixedCharacterSpace_le_fixedGeneralizedCharacterSpace (K : Subgroup M) (d : ℕ) :
    fixedCharacterSpace π ι χ K d ≤ fixedGeneralizedCharacterSpace π ι χ K :=
  le_iSup (fun d : ℕ => fixedCharacterSpace π ι χ K d) d

theorem fixedGeneralizedCharacterSpace_le_fixedVectors (K : Subgroup M) :
    fixedGeneralizedCharacterSpace π ι χ K ≤ fixedVectors π K :=
  iSup_le fun _ => inf_le_left

/-- Renard: if `K' ⊆ K`, then `(r V)^{K}_χ ⊆ (r V)^{K'}_χ`. -/
theorem fixedGeneralizedCharacterSpace_antitone :
    Antitone (fixedGeneralizedCharacterSpace π ι χ) :=
  fun _ _ h => iSup_mono fun d => fixedCharacterSpace_antitone π ι χ d h

/-- `π(m)` commutes with every `π(ι t)` when `ι` has central image. -/
theorem comp_apply_central (hι : ∀ t : A, ι t ∈ Subgroup.center M) (m : M) (t : A) :
    ((π.comp ι) t).comp (π m) = (π m).comp ((π.comp ι) t) := by
  change π (ι t) * π m = π m * π (ι t)
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hι t) m]

/-- Levi stability: `π(m)` carries the `K`-fixed character space to the `m K m⁻¹`-fixed
one when `ι` has central image. -/
theorem apply_mem_fixedCharacterSpace_conj (hι : ∀ t : A, ι t ∈ Subgroup.center M)
    (m : M) {K : Subgroup M} {d : ℕ} {v : V} (hv : v ∈ fixedCharacterSpace π ι χ K d) :
    π m v ∈ fixedCharacterSpace π ι χ (conjSubgroup m K) d := by
  obtain ⟨hfix, hchar⟩ := Submodule.mem_inf.mp hv
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · change ∀ x : conjSubgroup m K, π (x : M) (π m v) = π m v
    intro x
    have hx : m⁻¹ * (x : M) * m ∈ K := mem_conjSubgroup.mp x.property
    have hfx : π (m⁻¹ * (x : M) * m) v = v := hfix ⟨_, hx⟩
    have hmul : (x : M) * m = m * (m⁻¹ * (x : M) * m) := by group
    calc π (x : M) (π m v) = π ((x : M) * m) v := by rw [map_mul, Module.End.mul_apply]
      _ = π m (π (m⁻¹ * (x : M) * m) v) := by rw [hmul, map_mul, Module.End.mul_apply]
      _ = π m v := by rw [hfx]
  · exact map_mem_characterSpace_of_intertwining (π m) (comp_apply_central π ι hι m) χ d hchar

/-- Central elements of `M`, in particular the points `ι t`, preserve each `K`-fixed
character space. -/
theorem apply_mem_fixedCharacterSpace_of_mem_center (hι : ∀ t : A, ι t ∈ Subgroup.center M)
    {z : M} (hz : z ∈ Subgroup.center M) {K : Subgroup M} {d : ℕ} {v : V}
    (hv : v ∈ fixedCharacterSpace π ι χ K d) :
    π z v ∈ fixedCharacterSpace π ι χ K d := by
  have h := apply_mem_fixedCharacterSpace_conj π ι χ hι z hv
  have hK : conjSubgroup z K = K := by
    ext x
    rw [mem_conjSubgroup, mul_assoc, Subgroup.mem_center_iff.mp hz x, ← mul_assoc,
      inv_mul_cancel, one_mul]
  rwa [hK] at h

/-- The action of `A` preserves Renard's `(r V)^{K_M}_χ`. -/
theorem apply_mem_fixedGeneralizedCharacterSpace (hι : ∀ t : A, ι t ∈ Subgroup.center M)
    (t : A) {K : Subgroup M} {v : V} (hv : v ∈ fixedGeneralizedCharacterSpace π ι χ K) :
    π (ι t) v ∈ fixedGeneralizedCharacterSpace π ι χ K := by
  have hle : fixedGeneralizedCharacterSpace π ι χ K ≤
      (fixedGeneralizedCharacterSpace π ι χ K).comap (π (ι t)) :=
    iSup_le fun d _ hw => fixedCharacterSpace_le_fixedGeneralizedCharacterSpace π ι χ K d
      (apply_mem_fixedCharacterSpace_of_mem_center π ι χ hι (hι t) hw)
  exact hle hv

variable {π}

/-- Intertwiners preserve each `K`-fixed character space. -/
theorem map_mem_fixedCharacterSpace {σ : Representation R M W} (f : π.IntertwiningMap σ)
    {K : Subgroup M} {d : ℕ} {v : V} (hv : v ∈ fixedCharacterSpace π ι χ K d) :
    f v ∈ fixedCharacterSpace σ ι χ K d := by
  obtain ⟨hfix, hchar⟩ := Submodule.mem_inf.mp hv
  exact Submodule.mem_inf.mpr ⟨map_mem_fixedVectors f hfix,
    map_mem_characterSpace_of_intertwining f.toLinearMap (fun t => (f.isIntertwining' (ι t)).symm) χ d hchar⟩

variable (π)

section Topological

variable [TopologicalSpace M] [IsTopologicalGroup M]

/-- Renard's `(r V)_χ`: the union of the `K`-fixed generalized character spaces over
the compact open subgroups `K` of `M`, hence over all such `K` and all powers `d`. It is
`M`-stable because `ι` has central image and conjugates of compact open subgroups are
compact open. -/
def generalizedWeightSpace (hι : ∀ t : A, ι t ∈ Subgroup.center M) : Subrepresentation π where
  toSubmodule := ⨆ K : CompactOpenSubgroup M, fixedGeneralizedCharacterSpace π ι χ K.toSubgroup
  apply_mem_toSubmodule m := by
    intro v hv
    have hle : (⨆ K : CompactOpenSubgroup M,
        fixedGeneralizedCharacterSpace π ι χ K.toSubgroup) ≤
          (⨆ K : CompactOpenSubgroup M,
            fixedGeneralizedCharacterSpace π ι χ K.toSubgroup).comap (π m) := by
      refine iSup_le fun K => iSup_le fun d => ?_
      intro w hw
      exact Submodule.mem_iSup_of_mem (K.conj m)
        (fixedCharacterSpace_le_fixedGeneralizedCharacterSpace π ι χ _ d
          (apply_mem_fixedCharacterSpace_conj π ι χ hι m hw))
    exact hle hv

variable (hι : ∀ t : A, ι t ∈ Subgroup.center M)

theorem fixedGeneralizedCharacterSpace_le_generalizedWeightSpace (K : CompactOpenSubgroup M) :
    fixedGeneralizedCharacterSpace π ι χ K.toSubgroup ≤
      (generalizedWeightSpace π ι χ hι).toSubmodule :=
  le_iSup (fun K : CompactOpenSubgroup M => fixedGeneralizedCharacterSpace π ι χ K.toSubgroup) K

theorem fixedCharacterSpace_le_generalizedWeightSpace (K : CompactOpenSubgroup M) (d : ℕ) :
    fixedCharacterSpace π ι χ K.toSubgroup d ≤ (generalizedWeightSpace π ι χ hι).toSubmodule :=
  (fixedCharacterSpace_le_fixedGeneralizedCharacterSpace π ι χ _ d).trans
    (fixedGeneralizedCharacterSpace_le_generalizedWeightSpace π ι χ hι K)

/-- The union defining `(r V)_χ` is directed: two compact open subgroups contain their
compact open intersection. -/
theorem directed_fixedGeneralizedCharacterSpace :
    Directed (· ≤ ·)
      (fun K : CompactOpenSubgroup M => fixedGeneralizedCharacterSpace π ι χ K.toSubgroup) :=
  fun K L => ⟨K.inf L,
    fixedGeneralizedCharacterSpace_antitone π ι χ (K.inf_le_left L),
    fixedGeneralizedCharacterSpace_antitone π ι χ (K.inf_le_right L)⟩

end Topological

section Intertwining

variable [TopologicalSpace M] [IsTopologicalGroup M]
  (hι : ∀ t : A, ι t ∈ Subgroup.center M)

variable {π} {σ : Representation R M W} {τ : Representation R M X}

/-- Intertwiners preserve the generalized weight subrepresentations. -/
theorem map_mem_generalizedWeightSpace (f : π.IntertwiningMap σ) {v : V}
    (hv : v ∈ generalizedWeightSpace π ι χ hι) : f v ∈ generalizedWeightSpace σ ι χ hι := by
  have hle : (⨆ K : CompactOpenSubgroup M,
      fixedGeneralizedCharacterSpace π ι χ K.toSubgroup) ≤
        (generalizedWeightSpace σ ι χ hι).toSubmodule.comap f.toLinearMap := by
    refine iSup_le fun K => iSup_le fun d => ?_
    intro w hw
    exact fixedCharacterSpace_le_generalizedWeightSpace σ ι χ hι K d
      (map_mem_fixedCharacterSpace ι χ f hw)
  exact hle hv

/-- The restriction of an intertwiner to the generalized weight subrepresentations. -/
def generalizedWeightMap (f : π.IntertwiningMap σ) :
    (generalizedWeightSpace π ι χ hι).toRepresentation.IntertwiningMap
      (generalizedWeightSpace σ ι χ hι).toRepresentation where
  toFun v := ⟨f v, map_mem_generalizedWeightSpace ι χ hι f v.property⟩
  map_add' v w := Subtype.ext (map_add f (v : V) (w : V))
  map_smul' c v := Subtype.ext (map_smul f c (v : V))
  isIntertwining' m := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change f (π m (v : V)) = σ m (f (v : V))
    exact Representation.IntertwiningMap.isIntertwining π σ f m (v : V)

@[simp]
theorem generalizedWeightMap_apply (f : π.IntertwiningMap σ)
    (v : generalizedWeightSpace π ι χ hι) :
    (generalizedWeightMap ι χ hι f v : W) = f (v : V) :=
  rfl

/-- Restriction preserves identities. -/
theorem generalizedWeightMap_id :
    generalizedWeightMap ι χ hι (Representation.IntertwiningMap.id π) =
      Representation.IntertwiningMap.id (generalizedWeightSpace π ι χ hι).toRepresentation :=
  Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)

/-- Restriction preserves composition. -/
theorem generalizedWeightMap_comp (g : σ.IntertwiningMap τ) (f : π.IntertwiningMap σ) :
    generalizedWeightMap ι χ hι (g.comp f) =
      (generalizedWeightMap ι χ hι g).comp (generalizedWeightMap ι χ hι f) :=
  Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)

end Intertwining

section Exponent

variable [TopologicalSpace A] [TopologicalSpace M] [IsTopologicalGroup M]

/-- A generalized weight of the central action: Renard's smooth-character convention,
written as an open kernel (as in `IsJacquetExponent`, `IsCentralExponent` and
`Induction.SmoothCharacter`), together with nontriviality of `(r V)_χ`. -/
def IsGeneralizedWeight (hι : ∀ t : A, ι t ∈ Subgroup.center M) : Prop :=
  IsOpen (χ.ker : Set A) ∧ generalizedWeightSpace π ι χ hι ≠ ⊥

end Exponent

section LocallyProfinite

variable [TopologicalSpace M] [NonarchimedeanGroup M] [WeaklyLocallyCompactSpace M]
  (hι : ∀ t : A, ι t ∈ Subgroup.center M)

/-- Membership in `(r V)_χ`: some compact open `K` fixes the vector, and one power `d`
kills `π(ι t) - χ(t)` for every `t`. -/
theorem mem_generalizedWeightSpace (v : V) :
    v ∈ generalizedWeightSpace π ι χ hι ↔
      ∃ K : CompactOpenSubgroup M, v ∈ fixedVectors π K.toSubgroup ∧
        ∃ d : ℕ, ∀ t : A, ((π (ι t) - (χ t : R) • 1) ^ d) v = 0 := by
  have := nonempty_compactOpenSubgroup M
  change v ∈ (⨆ K : CompactOpenSubgroup M,
    fixedGeneralizedCharacterSpace π ι χ K.toSubgroup) ↔ _
  rw [Submodule.mem_iSup_of_directed _ (directed_fixedGeneralizedCharacterSpace π ι χ)]
  simp only [mem_fixedGeneralizedCharacterSpace]

variable {π} in
/-- For a smooth representation the compact open condition is automatic: every smooth
vector is fixed by a compact open subgroup. -/
theorem mem_generalizedWeightSpace_of_isSmooth (hπ : IsSmooth π) (v : V) :
    v ∈ generalizedWeightSpace π ι χ hι ↔
      ∃ d : ℕ, ∀ t : A, ((π (ι t) - (χ t : R) • 1) ^ d) v = 0 := by
  rw [mem_generalizedWeightSpace]
  constructor
  · rintro ⟨-, -, hd⟩
    exact hd
  · intro hd
    obtain ⟨K, hK, -, hv⟩ :=
      exists_compactOpen_fixing_finite π hπ (fun _ : Unit => v) Set.univ Filter.univ_mem
    exact ⟨⟨K, hK⟩, hv (), hd⟩

variable {π} in
/-- For a smooth representation, `(r V)_χ` is the union of the generic uniform character
spaces of the restricted action. -/
theorem generalizedWeightSpace_toSubmodule_of_isSmooth (hπ : IsSmooth π) :
    (generalizedWeightSpace π ι χ hι).toSubmodule = ⨆ d : ℕ, characterSpace (π.comp ι) χ d := by
  ext v
  change v ∈ generalizedWeightSpace π ι χ hι ↔ _
  rw [mem_generalizedWeightSpace_of_isSmooth ι χ hι hπ,
    Submodule.mem_iSup_of_directed _ (characterSpace_mono (π.comp ι) χ).directed_le]
  simp only [mem_characterSpace]
  rfl

variable {π} in
/-- Nontriviality of `(r V)_χ` is the generic generalized-eigencharacter predicate of the
restricted action. -/
theorem generalizedWeightSpace_ne_bot_iff (hπ : IsSmooth π) :
    generalizedWeightSpace π ι χ hι ≠ ⊥ ↔ IsGeneralizedEigencharacter (π.comp ι) χ := by
  have hbot : ∀ S : Subrepresentation π, S = ⊥ ↔ S.toSubmodule = ⊥ :=
    fun S => ⟨fun h => h ▸ rfl, fun h => Subrepresentation.toSubmodule_injective h⟩
  rw [Ne, hbot, ← Ne, Submodule.ne_bot_iff, isGeneralizedEigencharacter_iff]
  constructor
  · rintro ⟨v, hv, hv0⟩
    obtain ⟨d, hd⟩ := (mem_generalizedWeightSpace_of_isSmooth ι χ hι hπ v).mp hv
    exact ⟨d, v, hv0, hd⟩
  · rintro ⟨d, v, hv0, hd⟩
    exact ⟨v, (mem_generalizedWeightSpace_of_isSmooth ι χ hι hπ v).mpr ⟨d, hd⟩, hv0⟩

variable {π} in
/-- Comparison with the published full-center subrepresentation: a generalized central
character `χZ` restricting to `χ` along `ι` has its generalized space inside `(r V)_χ`. -/
theorem generalizedCentralCharacterSpace_le_generalizedWeightSpace (hπ : IsSmooth π)
    (χZ : Subgroup.center M →* Rˣ) (hχ : ∀ t : A, χZ ⟨ι t, hι t⟩ = χ t) :
    generalizedCentralCharacterSpace π χZ ≤ generalizedWeightSpace π ι χ hι := by
  intro v hv
  obtain ⟨n, hn⟩ := (mem_generalizedCentralCharacterSpace π χZ v).mp hv
  refine (mem_generalizedWeightSpace_of_isSmooth ι χ hι hπ v).mpr ⟨n, fun t => ?_⟩
  have h := hn ⟨ι t, hι t⟩
  rwa [hχ] at h

variable {π} in
theorem isGeneralizedWeight_iff_isOpen_ker_and [TopologicalSpace A] (hπ : IsSmooth π) :
    IsGeneralizedWeight π ι χ hι ↔
      IsOpen (χ.ker : Set A) ∧ IsGeneralizedEigencharacter (π.comp ι) χ :=
  and_congr Iff.rfl (generalizedWeightSpace_ne_bot_iff ι χ hι hπ)

end LocallyProfinite

end Fixed

section OpenKernel

variable {k : Type uR} [Field k] {A : Type uA} [Group A] {M : Type uM} [Group M]
  [TopologicalSpace M] [IsTopologicalGroup M] {V : Type uV} [AddCommGroup V] [Module k V]

/-- A generalized eigencharacter of a smooth action restricted along `ι` has open kernel
for the topology induced by `ι`. -/
theorem isOpen_induced_ker_of_isGeneralizedEigencharacter_comp (π : Representation k M V)
    (hπ : IsSmooth π) (ι : A →* M) (χ : A →* kˣ)
    (h : IsGeneralizedEigencharacter (π.comp ι) χ) :
    IsOpen[TopologicalSpace.induced ι ‹_›] (χ.ker : Set A) := by
  let _ : TopologicalSpace A := TopologicalSpace.induced ι ‹_›
  have _ : IsTopologicalGroup A := isTopologicalGroup_induced ι
  exact isOpen_ker_of_isGeneralizedEigencharacter (π.comp ι) χ
    (isSmooth_comp ι continuous_induced_dom hπ) h

/-- A generalized eigencharacter of a smooth action restricted along a continuous `ι` has
open kernel. No topological-group structure on `A` is needed. -/
theorem isOpen_ker_of_isGeneralizedEigencharacter_comp [TopologicalSpace A]
    (π : Representation k M V) (hπ : IsSmooth π) (ι : A →* M) (hιc : Continuous ι)
    (χ : A →* kˣ) (h : IsGeneralizedEigencharacter (π.comp ι) χ) :
    IsOpen (χ.ker : Set A) :=
  (isOpen_implies_isOpen_iff.mpr (continuous_iff_le_induced.mp hιc)) _
    (isOpen_induced_ker_of_isGeneralizedEigencharacter_comp π hπ ι χ h)

end OpenKernel

section OpenKernelLocallyProfinite

variable {k : Type uR} [Field k] {A : Type uA} [Group A] [TopologicalSpace A]
  {M : Type uM} [Group M] [TopologicalSpace M] [NonarchimedeanGroup M]
  [WeaklyLocallyCompactSpace M] {V : Type uV} [AddCommGroup V] [Module k V]

/-- For a smooth action over a field and a continuous central `ι`, the open-kernel
condition is automatic: generalized weights are exactly the generic generalized
eigencharacters of the restricted action. -/
theorem isGeneralizedWeight_iff (π : Representation k M V) (hπ : IsSmooth π) (ι : A →* M)
    (hιc : Continuous ι) (hι : ∀ t : A, ι t ∈ Subgroup.center M) (χ : A →* kˣ) :
    IsGeneralizedWeight π ι χ hι ↔ IsGeneralizedEigencharacter (π.comp ι) χ := by
  rw [isGeneralizedWeight_iff_isOpen_ker_and ι χ hι hπ]
  exact ⟨And.right, fun h => ⟨isOpen_ker_of_isGeneralizedEigencharacter_comp π hπ ι hιc χ h, h⟩⟩

end OpenKernelLocallyProfinite

end Langlands
