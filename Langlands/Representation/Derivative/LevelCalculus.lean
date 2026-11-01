import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Derivative.ShortExactFunctorLaws
import Langlands.Representation.Derivative.MirabolicDerivativeDetectionProof
import Langlands.Representation.Category.Abelian

/-!
# Level calculus for mirabolic derivatives

Elementary consequences of the published definitions of `level` and
`IsHomogeneous`, of the exactness statement for the minus functors (taken as an
explicit hypothesis where it is used), and of the published detection theorem.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

namespace LevelCalculus

/-! ## Maps of smooth representations -/

section Maps

variable {G : Type*} [Group G] [TopologicalSpace G]

theorem nontrivial_of_injective {A B : SmoothRep.{0, _, uV} ℂ G} (f : A ⟶ B)
    (hf : Function.Injective (SmoothRep.hom f)) [Nontrivial A] : Nontrivial B :=
  hf.nontrivial

theorem subsingleton_of_injective {A B : SmoothRep.{0, _, uV} ℂ G} (f : A ⟶ B)
    (hf : Function.Injective (SmoothRep.hom f)) [Subsingleton B] : Subsingleton A :=
  hf.subsingleton

theorem hom_inv_apply {A B : SmoothRep.{0, _, uV} ℂ G} (e : A ≅ B) (x : A) :
    SmoothRep.hom e.inv (SmoothRep.hom e.hom x) = x := by
  change SmoothRep.hom (e.hom ≫ e.inv) x = x
  rw [e.hom_inv_id]
  rfl

theorem inv_hom_apply {A B : SmoothRep.{0, _, uV} ℂ G} (e : A ≅ B) (y : B) :
    SmoothRep.hom e.hom (SmoothRep.hom e.inv y) = y := by
  change SmoothRep.hom (e.inv ≫ e.hom) y = y
  rw [e.inv_hom_id]
  rfl

theorem iso_hom_injective {A B : SmoothRep.{0, _, uV} ℂ G} (e : A ≅ B) :
    Function.Injective (SmoothRep.hom e.hom) :=
  Function.LeftInverse.injective (hom_inv_apply e)

theorem iso_hom_surjective {A B : SmoothRep.{0, _, uV} ℂ G} (e : A ≅ B) :
    Function.Surjective (SmoothRep.hom e.hom) :=
  Function.RightInverse.surjective (inv_hom_apply e)

theorem nontrivial_iff_of_iso {A B : SmoothRep.{0, _, uV} ℂ G} (e : A ≅ B) :
    Nontrivial A ↔ Nontrivial B :=
  ⟨fun _ => nontrivial_of_injective e.hom (iso_hom_injective e),
    fun _ => nontrivial_of_injective e.inv (iso_hom_injective e.symm)⟩

theorem subsingleton_iff_of_iso {A B : SmoothRep.{0, _, uV} ℂ G} (e : A ≅ B) :
    Subsingleton A ↔ Subsingleton B := by
  rw [← not_nontrivial_iff_subsingleton, ← not_nontrivial_iff_subsingleton,
    nontrivial_iff_of_iso e]

/-- A bijective intertwiner is an isomorphism. -/
theorem isIso_of_bijective {A B : SmoothRep.{0, _, uV} ℂ G} (f : A ⟶ B)
    (hi : Function.Injective (SmoothRep.hom f)) (hs : Function.Surjective (SmoothRep.hom f)) :
    IsIso f := by
  have : Mono f := (SmoothRep.mono_iff_injective f).mpr hi
  have : Epi f := (SmoothRep.epi_iff_surjective f).mpr hs
  exact isIso_of_mono_of_epi f

/-- The corestriction of an intertwiner to an invariant subspace containing its
values. -/
def codRestrict {A B : SmoothRep.{0, _, uV} ℂ G} (f : A ⟶ B)
    (U : Subrepresentation B.representation) (hU : ∀ x, SmoothRep.hom f x ∈ U.toSubmodule) :
    A ⟶ SmoothRep.subrepresentation B U :=
  SmoothRep.ofHom
    { toLinearMap := LinearMap.codRestrict U.toSubmodule (SmoothRep.hom f).toLinearMap hU
      isIntertwining' := fun g => by
        ext x
        apply Subtype.ext
        exact Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom f) g x }

theorem codRestrict_apply {A B : SmoothRep.{0, _, uV} ℂ G} (f : A ⟶ B)
    (U : Subrepresentation B.representation) (hU : ∀ x, SmoothRep.hom f x ∈ U.toSubmodule)
    (x : A) : SmoothRep.hom (SmoothRep.subtype B U) (SmoothRep.hom (codRestrict f U hU) x) =
      SmoothRep.hom f x :=
  rfl

theorem codRestrict_injective {A B : SmoothRep.{0, _, uV} ℂ G} (f : A ⟶ B)
    (U : Subrepresentation B.representation) (hU : ∀ x, SmoothRep.hom f x ∈ U.toSubmodule)
    (hf : Function.Injective (SmoothRep.hom f)) :
    Function.Injective (SmoothRep.hom (codRestrict f U hU)) := fun _ _ h =>
  hf (congrArg Subtype.val h)

/-- An injective intertwiner identifies its source with its range. -/
def isoRange {A B : SmoothRep.{0, _, uV} ℂ G} (f : A ⟶ B)
    (hf : Function.Injective (SmoothRep.hom f)) :
    A ≅ SmoothRep.subrepresentation B (SmoothRep.hom f).range :=
  haveI := isIso_of_bijective (codRestrict f (SmoothRep.hom f).range fun x => ⟨x, rfl⟩)
    (codRestrict_injective f _ _ hf) (by
      rintro ⟨_, x, rfl⟩
      exact ⟨x, rfl⟩)
  asIso (codRestrict f (SmoothRep.hom f).range fun x => ⟨x, rfl⟩)

theorem subrepresentation_nontrivial {A : SmoothRep.{0, _, uV} ℂ G}
    (U : Subrepresentation A.representation) (hU : U ≠ ⊥) :
    Nontrivial (SmoothRep.subrepresentation A U) := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply hU
  apply Subrepresentation.toSubmodule_injective
  change U.toSubmodule = ⊥
  rw [eq_bot_iff]
  intro x hx
  exact congrArg Subtype.val (@Subsingleton.elim U.toSubmodule h ⟨x, hx⟩ 0)

theorem range_ne_bot {A B : SmoothRep.{0, _, uV} ℂ G} (f : A ⟶ B)
    (hf : Function.Injective (SmoothRep.hom f)) [Nontrivial A] :
    (SmoothRep.hom f).range ≠ ⊥ := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : A)
  apply hx
  apply hf
  have : SmoothRep.hom f x ∈ ((SmoothRep.hom f).range).toSubmodule := ⟨x, rfl⟩
  rw [h] at this
  rw [map_zero]
  exact this

/-- The full subrepresentation is the ambient representation. -/
def topIso (A : SmoothRep.{0, _, uV} ℂ G) : SmoothRep.subrepresentation A ⊤ ≅ A :=
  haveI := isIso_of_bijective (SmoothRep.subtype A ⊤) (SmoothRep.subtype_injective A ⊤)
    (fun x => ⟨⟨x, Submodule.mem_top⟩, rfl⟩)
  asIso (SmoothRep.subtype A ⊤)

theorem top_ne_bot {A : SmoothRep.{0, _, uV} ℂ G} [Nontrivial A] :
    (⊤ : Subrepresentation A.representation) ≠ ⊥ := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : A)
  have : x ∈ (⊤ : Subrepresentation A.representation).toSubmodule := Submodule.mem_top
  rw [h] at this
  exact hx this

/-- The preimage of an invariant subspace under an intertwiner. -/
def comap {A B : SmoothRep.{0, _, uV} ℂ G} (f : A ⟶ B) (U : Subrepresentation B.representation) :
    Subrepresentation A.representation where
  toSubmodule := U.toSubmodule.comap (SmoothRep.hom f).toLinearMap
  apply_mem_toSubmodule g v hv := by
    change SmoothRep.hom f (A.representation g v) ∈ U.toSubmodule
    rw [Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom f) g v]
    exact U.apply_mem_toSubmodule g hv

theorem mem_comap {A B : SmoothRep.{0, _, uV} ℂ G} (f : A ⟶ B)
    (U : Subrepresentation B.representation) (x : A) :
    x ∈ (comap f U).toSubmodule ↔ SmoothRep.hom f x ∈ U.toSubmodule :=
  Iff.rfl

/-- The restriction of an intertwiner to the preimage of an invariant subspace. -/
def comapMap {A B : SmoothRep.{0, _, uV} ℂ G} (f : A ⟶ B) (U : Subrepresentation B.representation) :
    SmoothRep.subrepresentation A (comap f U) ⟶ SmoothRep.subrepresentation B U :=
  codRestrict (SmoothRep.subtype A (comap f U) ≫ f) U fun x => x.2

theorem comapMap_injective {A B : SmoothRep.{0, _, uV} ℂ G} (f : A ⟶ B)
    (U : Subrepresentation B.representation) (hf : Function.Injective (SmoothRep.hom f)) :
    Function.Injective (SmoothRep.hom (comapMap f U)) :=
  codRestrict_injective _ _ _ (hf.comp (SmoothRep.subtype_injective A _))

/-- Short exactness of a pair of actual intertwiners. -/
structure IsShortExact {A B C : SmoothRep.{0, _, uV} ℂ G} (i : A ⟶ B) (q : B ⟶ C) : Prop where
  injective : Function.Injective (SmoothRep.hom i)
  surjective : Function.Surjective (SmoothRep.hom q)
  exact : LinearMap.range (SmoothRep.hom i).toLinearMap = LinearMap.ker (SmoothRep.hom q).toLinearMap

theorem subsingleton_of_isShortExact {A B C : SmoothRep.{0, _, uV} ℂ G} {i : A ⟶ B} {q : B ⟶ C}
    (h : IsShortExact i q) [Subsingleton A] [Subsingleton C] : Subsingleton B := by
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : B, z = 0 := by
    intro z
    have : z ∈ LinearMap.ker (SmoothRep.hom q).toLinearMap :=
      Subsingleton.elim (SmoothRep.hom q z) 0
    rw [← h.exact] at this
    obtain ⟨a, rfl⟩ := this
    change SmoothRep.hom i a = 0
    rw [Subsingleton.elim a 0, map_zero]
  rw [hx x, hx y]

theorem isShortExact_mkQ {A B : SmoothRep.{0, _, uV} ℂ G} (i : A ⟶ B)
    (hi : Function.Injective (SmoothRep.hom i)) :
    IsShortExact i (SmoothRep.mkQ B (SmoothRep.hom i).range) where
  injective := hi
  surjective := SmoothRep.mkQ_surjective B _
  exact := (Submodule.ker_mkQ _).symm

theorem isShortExact_kernelι {B C : SmoothRep.{0, _, uV} ℂ G} (q : B ⟶ C)
    (hq : Function.Surjective (SmoothRep.hom q)) :
    IsShortExact (SmoothRep.kernelι q) q where
  injective := SmoothRep.subtype_injective B _
  surjective := hq
  exact := Submodule.range_subtype _

end Maps

/-! ## Exact functors -/

section Exact

variable {G : Type*} [Group G] [TopologicalSpace G] {H : Type*} [Group H] [TopologicalSpace H]
  {K : Type*} [Group K] [TopologicalSpace K]

open Mirabolic

theorem isShortExact_map {J : SmoothRep.{0, _, uV} ℂ G ⥤ SmoothRep.{0, _, uV} ℂ H}
    (hJ : MapsShortExactIntertwiners J) {A B C : SmoothRep.{0, _, uV} ℂ G} {i : A ⟶ B}
    {q : B ⟶ C} (h : IsShortExact i q) : IsShortExact (J.map i) (J.map q) :=
  let h' := hJ A B C i q h.injective h.surjective h.exact
  ⟨h'.1, h'.2.2, h'.2.1⟩

theorem map_injective_of_exact
    {J : SmoothRep.{0, _, uV} ℂ G ⥤ SmoothRep.{0, _, uV} ℂ H}
    (hJ : MapsShortExactIntertwiners J) {A B : SmoothRep.{0, _, uV} ℂ G} (i : A ⟶ B)
    (hi : Function.Injective (SmoothRep.hom i)) : Function.Injective (SmoothRep.hom (J.map i)) :=
  (isShortExact_map hJ (isShortExact_mkQ i hi)).injective


end Exact

/-! ## Exactness of the derivative functors -/

section DerivativeExact

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

open Mirabolic

theorem mapsShortExact_mirabolicRankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    MapsShortExactIntertwiners (mirabolicRankCast.{uF, uV} T h) := by
  let _ := T.topology
  subst h
  exact mapsShortExact_id

theorem mapsShortExact_phiMinusIterate (hE : MinusExactnessStatement.{uF, uV} F T) (n : ℕ) :
    ∀ k : ℕ, letI := T.topology
      MapsShortExactIntertwiners (phiMinusIterate.{uF, uV} T ψ n k) := by
  let _ := T.topology
  intro k
  induction k with
  | zero => exact mapsShortExact_id
  | succ k ih => exact mapsShortExact_comp (hE.2.2.2 (n + k) ψ) ih

theorem mapsShortExact_mirabolicDerivative (hE : MinusExactnessStatement.{uF, uV} F T)
    (n k : ℕ) :
    letI := T.topology
    MapsShortExactIntertwiners (mirabolicDerivative.{uF, uV} T ψ n k) := by
  let _ := T.topology
  exact mapsShortExact_comp (mapsShortExact_phiMinusIterate T ψ hE n k) (hE.2.2.1 n)

theorem mapsShortExact_mirabolicDerivativeOfOrder (hE : MinusExactnessStatement.{uF, uV} F T)
    (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    MapsShortExactIntertwiners (mirabolicDerivativeOfOrder.{uF, uV} T ψ N k hk) := by
  let _ := T.topology
  exact mapsShortExact_comp (mapsShortExact_mirabolicRankCast T _)
    (mapsShortExact_mirabolicDerivative T ψ hE _ _)

end DerivativeExact

/-! ## Level -/

section Level

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem hasNonzeroDerivative_level {N : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      level T ψ A ≠ 0 → HasNonzeroDerivative T ψ A (level T ψ A) := by
  intro A
  classical
  change Nat.findGreatest (HasNonzeroDerivative T ψ A) (N + 1) ≠ 0 →
    HasNonzeroDerivative T ψ A (Nat.findGreatest (HasNonzeroDerivative T ψ A) (N + 1))
  exact fun h => Nat.findGreatest_of_ne_zero rfl h

theorem level_le_of_imp {N : ℕ} :
    letI := T.topology
    ∀ A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      (∀ k, HasNonzeroDerivative T ψ A k → HasNonzeroDerivative T ψ B k) →
        level T ψ A ≤ level T ψ B := by
  intro A B h
  by_cases h0 : level T ψ A = 0
  · rw [h0]
    exact Nat.zero_le _
  · exact le_level_of_hasNonzeroDerivative T ψ B (h _ (hasNonzeroDerivative_level T ψ A h0))

theorem hasNonzeroDerivative_iff_of_iso {N : ℕ} :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (_ : A ≅ B) (k : ℕ),
      HasNonzeroDerivative T ψ A k ↔ HasNonzeroDerivative T ψ B k := by
  let _ := T.topology
  intro A B e k
  exact ⟨fun ⟨hk, h⟩ =>
      ⟨hk, (nontrivial_iff_of_iso ((mirabolicDerivativeOfOrder T ψ N k hk).mapIso e)).mp h⟩,
    fun ⟨hk, h⟩ =>
      ⟨hk, (nontrivial_iff_of_iso ((mirabolicDerivativeOfOrder T ψ N k hk).mapIso e)).mpr h⟩⟩

theorem level_eq_of_iso {N : ℕ} :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (_ : A ≅ B),
      level T ψ A = level T ψ B := by
  let _ := T.topology
  intro A B e
  exact le_antisymm (level_le_of_imp T ψ A B fun k => (hasNonzeroDerivative_iff_of_iso T ψ e k).mp)
    (level_le_of_imp T ψ B A fun k => (hasNonzeroDerivative_iff_of_iso T ψ e k).mpr)

theorem level_mirabolicRankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier),
      level T ψ ((mirabolicRankCast T h).obj A) = level T ψ A := by
  subst h
  intro A
  rfl

theorem nontrivial_mirabolicRankCast_iff {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier),
      Nontrivial ((mirabolicRankCast T h).obj A) ↔ Nontrivial A := by
  subst h
  intro A
  rfl

theorem nontrivial_of_hasNonzeroDerivative {N k : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      HasNonzeroDerivative T ψ A k → Nontrivial A := by
  let _ := T.topology
  rintro A ⟨hk, h⟩
  by_contra hA
  rw [not_nontrivial_iff_subsingleton] at hA
  have := mirabolicDerivativeOfOrder_obj_subsingleton T ψ N k hk A hA
  exact not_subsingleton _ this

theorem nontrivial_of_level_ne_zero {N : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier), level T ψ A ≠ 0 → Nontrivial A :=
  fun A h => nontrivial_of_hasNonzeroDerivative T ψ A (hasNonzeroDerivative_level T ψ A h)

/-- The published detection theorem, in the form used below. -/
theorem level_pos {N : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)) [Nontrivial A], 0 < level T ψ A :=
  fun A hA => mirabolicDerivativeDetection.{uF, uV} F T ψ N A hA

theorem level_ne_zero_iff {N : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier), level T ψ A ≠ 0 ↔ Nontrivial A :=
  fun A => ⟨nontrivial_of_level_ne_zero T ψ A, fun _ => (level_pos T ψ A).ne'⟩

theorem level_eq_zero_iff_subsingleton {N : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier), level T ψ A = 0 ↔ Subsingleton A := by
  intro A
  rw [← not_nontrivial_iff_subsingleton, ← level_ne_zero_iff T ψ A, not_not]

/-! ### Injections and short exact sequences, under exactness -/

variable (hE : Mirabolic.MinusExactnessStatement.{uF, uV} F T)
include hE

theorem hasNonzeroDerivative_of_injective {N : ℕ} :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (f : A ⟶ B),
      Function.Injective (SmoothRep.hom f) →
        ∀ k, HasNonzeroDerivative T ψ A k → HasNonzeroDerivative T ψ B k := by
  let _ := T.topology
  rintro A B f hf k ⟨hk, h⟩
  refine ⟨hk, ?_⟩
  exact (map_injective_of_exact (mapsShortExact_mirabolicDerivativeOfOrder T ψ hE N k hk) f
    hf).nontrivial

theorem level_le_of_injective {N : ℕ} :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (f : A ⟶ B),
      Function.Injective (SmoothRep.hom f) → level T ψ A ≤ level T ψ B :=
  fun f hf => level_le_of_imp T ψ _ _ (hasNonzeroDerivative_of_injective T ψ hE f hf)

theorem level_le_max_of_isShortExact {N : ℕ} :
    letI := T.topology
    ∀ {A B C : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} {i : A ⟶ B} {q : B ⟶ C},
      IsShortExact i q → level T ψ B ≤ max (level T ψ A) (level T ψ C) := by
  let _ := T.topology
  intro A B C i q h
  by_cases h0 : level T ψ B = 0
  · rw [h0]
    exact Nat.zero_le _
  obtain ⟨hk, hn⟩ := hasNonzeroDerivative_level T ψ B h0
  have hJ := isShortExact_map (mapsShortExact_mirabolicDerivativeOfOrder T ψ hE N _ hk) h
  by_contra hlt
  rw [not_le, max_lt_iff] at hlt
  have hA : Subsingleton ((mirabolicDerivativeOfOrder T ψ N _ hk).obj A) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hA
    have := le_level_of_hasNonzeroDerivative T ψ A ⟨hk, hA⟩
    omega
  have hC : Subsingleton ((mirabolicDerivativeOfOrder T ψ N _ hk).obj C) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hC
    have := le_level_of_hasNonzeroDerivative T ψ C ⟨hk, hC⟩
    omega
  exact not_subsingleton _ (subsingleton_of_isShortExact hJ)

end Level

/-! ## One `Φ⁻` step shifts derivative orders by one -/

section Shift

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem nontrivial_mirabolicDerivative_cast_congr {N n n' j j' : ℕ} (hn : n = n') (hj : j = j')
    (h : N = n + j) (h' : N = n' + j') :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      Nontrivial ((mirabolicDerivative T ψ n j).obj ((mirabolicRankCast T h).obj A)) ↔
        Nontrivial ((mirabolicDerivative T ψ n' j').obj ((mirabolicRankCast T h').obj A)) := by
  subst hn hj
  intro A
  rfl

/-- The order-`(j+1)` derivative, read through any decomposition `N = n + j`. -/
theorem hasNonzeroDerivative_succ_iff_cast {N n j : ℕ} (h : N = n + j) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      HasNonzeroDerivative T ψ A (j + 1) ↔
        Nontrivial ((mirabolicDerivative T ψ n j).obj ((mirabolicRankCast T h).obj A)) := by
  intro A
  constructor
  · rintro ⟨hk, hA⟩
    exact (nontrivial_mirabolicDerivative_cast_congr T ψ (by omega) (by omega) _ h A).mp hA
  · intro hA
    exact ⟨⟨by omega, by omega⟩,
      (nontrivial_mirabolicDerivative_cast_congr T ψ (by omega) (by omega) h _ A).mp hA⟩

theorem mirabolicDerivative_succ_cast_obj {M n j : ℕ} (h : M + 1 = n + (j + 1))
    (h' : M = n + j) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier),
      (mirabolicDerivative T ψ n (j + 1)).obj ((mirabolicRankCast T h).obj A) =
        (mirabolicDerivative T ψ n j).obj
          ((mirabolicRankCast T h').obj ((Mirabolic.phiMinus T ψ M).obj A)) := by
  subst h'
  intro A
  rfl

/-- One `Φ⁻` step lowers every positive derivative order by one. -/
theorem hasNonzeroDerivative_succ_iff {M : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier)) {k : ℕ}, 0 < k →
      (HasNonzeroDerivative T ψ A (k + 1) ↔
        HasNonzeroDerivative T ψ ((Mirabolic.phiMinus T ψ M).obj A) k) := by
  intro A k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  by_cases hj : j ≤ M
  · obtain ⟨n, hn⟩ : ∃ n, M = n + j := ⟨M - j, by omega⟩
    have h : M + 1 = n + (j + 1) := by omega
    rw [hasNonzeroDerivative_succ_iff_cast T ψ h, mirabolicDerivative_succ_cast_obj T ψ h hn,
      ← hasNonzeroDerivative_succ_iff_cast T ψ hn]
  · constructor
    · rintro ⟨hk, -⟩
      omega
    · rintro ⟨hk, -⟩
      omega

theorem level_le_level_phiMinus_succ {M : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier),
      level T ψ A ≤ level T ψ ((Mirabolic.phiMinus T ψ M).obj A) + 1 := by
  intro A
  by_cases h0 : level T ψ A ≤ 1
  · omega
  have hA := hasNonzeroDerivative_level T ψ A (by omega)
  obtain ⟨k, hk⟩ : ∃ k, level T ψ A = k + 1 := ⟨level T ψ A - 1, by omega⟩
  rw [hk] at hA ⊢
  have := le_level_of_hasNonzeroDerivative T ψ _
    ((hasNonzeroDerivative_succ_iff T ψ A (by omega)).mp hA)
  omega

/-- If `Φ⁻ A` has a positive level, `A` has exactly one more. -/
theorem level_eq_level_phiMinus_succ {M : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier),
      0 < level T ψ ((Mirabolic.phiMinus T ψ M).obj A) →
        level T ψ A = level T ψ ((Mirabolic.phiMinus T ψ M).obj A) + 1 := by
  intro A hpos
  apply le_antisymm (level_le_level_phiMinus_succ T ψ A)
  apply le_level_of_hasNonzeroDerivative T ψ A
  exact (hasNonzeroDerivative_succ_iff T ψ A hpos).mpr
    (hasNonzeroDerivative_level T ψ _ hpos.ne')

theorem level_le_one_of_subsingleton_phiMinus {M : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier),
      Subsingleton ((Mirabolic.phiMinus T ψ M).obj A) → level T ψ A ≤ 1 := by
  intro A hA
  have := level_le_level_phiMinus_succ T ψ A
  rw [level_eq_zero_of_subsingleton T ψ _ hA] at this
  exact this

/-- With detection, `Φ⁻ A ≠ 0` exactly when `A` has level at least two. -/
theorem nontrivial_phiMinus_iff {M : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (M + 1) F.Carrier),
      Nontrivial ((Mirabolic.phiMinus T ψ M).obj A) ↔ 1 < level T ψ A := by
  intro A
  constructor
  · intro hA
    rw [level_eq_level_phiMinus_succ T ψ A (level_pos T ψ _)]
    have := level_pos T ψ ((Mirabolic.phiMinus T ψ M).obj A)
    omega
  · intro hA
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have := level_le_one_of_subsingleton_phiMinus T ψ A hn
    omega

end Shift

/-! ## Homogeneity through injective intertwiners -/

section Homogeneous

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem level_eq_of_isHomogeneous {N : ℕ} :
    letI := T.topology
    ∀ {W X : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)}, IsHomogeneous T ψ X →
      ∀ (f : W ⟶ X), Function.Injective (SmoothRep.hom f) → Nontrivial W →
        level T ψ W = level T ψ X := by
  let _ := T.topology
  intro W X hX f hf hW
  rw [level_eq_of_iso T ψ (isoRange f hf)]
  exact hX _ (range_ne_bot f hf)

theorem isHomogeneous_of_forall_injective {N : ℕ} :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)) (c : ℕ),
      (∀ (W : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)) (f : W ⟶ X),
        Function.Injective (SmoothRep.hom f) → Nontrivial W → level T ψ W = c) →
      IsHomogeneous T ψ X := by
  let _ := T.topology
  intro X c h
  by_cases hX : Nontrivial X
  · have hc : level T ψ X = c := h X (𝟙 X) (fun _ _ hxy => hxy) hX
    intro U hU
    rw [hc]
    exact h _ (SmoothRep.subtype X U) (SmoothRep.subtype_injective X U)
      (subrepresentation_nontrivial U hU)
  · rw [not_nontrivial_iff_subsingleton] at hX
    exact isHomogeneous_of_subsingleton T ψ X hX

theorem isHomogeneous_of_iso {N : ℕ} :
    letI := T.topology
    ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)} (_ : X ≅ Y),
      IsHomogeneous T ψ X → IsHomogeneous T ψ Y := by
  let _ := T.topology
  intro X Y e hX
  apply isHomogeneous_of_forall_injective T ψ Y (level T ψ X)
  intro W f hf hW
  exact level_eq_of_isHomogeneous T ψ hX (f ≫ e.inv)
    ((iso_hom_injective e.symm).comp hf) hW

end Homogeneous

end LevelCalculus

end Langlands.Derivative
