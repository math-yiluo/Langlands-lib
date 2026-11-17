import Langlands.Representation.Smooth.JointIsotypicComponent
import Langlands.Automorphic.OperatorSubquotientLocalComponentStatement
import Langlands.Automorphic.CuspidalContragredientLocalCompatibilityProof
import Langlands.Automorphic.OperatorSubquotientArchimedean
import Langlands.Global.FiniteAdelicGL.CompactOpenRefinement
import Langlands.Global.FiniteAdelicGL.PadicComparison

/-!
# Local components of automorphic representations at the finite places

The finite-place conjunct of `LocalComponentExistenceStatement` (Getz–Hahn, Theorem 6.3.7;
Flath, Theorem 3): an irreducible jointly admissible operator subquotient `Q` of `GL_(r+1)`
over a number field `F` is, at every finite place `v`, isotypic for an irreducible
admissible smooth representation of `GL_(r+1)(F_v)`.

The proof applies `Langlands.JointIsotypic` to the restriction `σ` of `Q` to `GL_n(F_v)`
and to the set `C` of the operators of `Q` coming from the local centralizer at `v`
(the operators of the concrete algebra commuting with every local translation at `v`).

* `commutesWith_localCentralizerOperators`, `isJointlyIrreducible_localCentralizerOperators`:
  `C` commutes with `σ`, and `σ` and `C` together act irreducibly, because every generator
  of the operator algebra is a local translation times an element of `C`.
* `awayFixed`: for an open subgroup `L₀` of the finite adelic group, the vectors fixed by
  the elements of `L₀` with identity `v`-component; it is stable under `σ` and the compact
  action at infinity.
* `equivariantInto_le_jointMultiplicitySpace`: maps from a representation `τ` of the
  standard compact subgroup at infinity into the vectors of `awayFixed` fixed by an open
  `L ≤ GL_n(F_v)` lie in the joint multiplicity space of an explicit open subgroup of the
  finite adelic group, which is finite-dimensional by joint admissibility.
* `exists_isotypic_subrepresentation`: an irreducible admissible subrepresentation `U` of
  `σ` such that `σ` is `U`-isotypic.
* `localComponentExistence_finitePlace`: the finite-place conjunct, with `U` placed in the
  correspondence category through the equality of the completion and canonical p-adic
  topologies on `GL_n(F_v)`.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)
open Langlands.JointIsotypic Langlands.TwoFactorExistence FiniteVectors
open scoped TensorProduct

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup
  subquotientRealizationGroup

section Subgroups

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

/-- The elements of an open subgroup `L₀` of the finite adelic group with identity
`v`-component. -/
def awaySubgroup (v : FinitePlace F) (L₀ : OpenSubgroup (FiniteAdelicGL F n)) :
    Subgroup (FiniteAdelicGL F n) :=
  L₀.toSubgroup ⊓ (localProjection F n v).toMonoidHom.ker

theorem mem_awaySubgroup {v : FinitePlace F} {L₀ : OpenSubgroup (FiniteAdelicGL F n)}
    {d : FiniteAdelicGL F n} :
    d ∈ awaySubgroup v L₀ ↔ d ∈ L₀ ∧ localProjection F n v d = 1 :=
  Subgroup.mem_inf.trans (and_congr Iff.rfl MonoidHom.mem_ker)

/-- The open subgroup `proj_v⁻¹(L) ∩ L₀ ∩ (inc_v ∘ proj_v)⁻¹(L₀)` of the finite adelic
group, for open subgroups `L₀` of the finite adelic group and `L` of `GL_n(F_v)`. -/
def comparisonSubgroup (v : FinitePlace F) (L₀ : OpenSubgroup (FiniteAdelicGL F n))
    (L : OpenSubgroup (FiniteLocalGL F n v)) : OpenSubgroup (FiniteAdelicGL F n) :=
  (L.comap (localProjection F n v).toMonoidHom (localProjection F n v).continuous ⊓ L₀) ⊓
    L₀.comap ((localInclusion F n v).toMonoidHom.comp (localProjection F n v).toMonoidHom)
      ((localInclusion F n v).continuous.comp (localProjection F n v).continuous)

/-- Admissibility for the completion topology on `GL_n(F_v)` gives admissibility for the
canonical p-adic matrix topology; the two topologies are equal (`localGL_topology_eq`). -/
theorem isAdmissible_canonicalTopology {v : FinitePlace F} {W : Type*} [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ (FiniteLocalGL F n v) W} (h : IsAdmissible ρ) :
    @IsAdmissible ℂ (FiniteLocalGL F n v) W _ _ _ _
      ((padicField v).canonicalGeneralLinearTopology n) ρ := by
  rw [← localGL_topology_eq F v n]
  exact h

end Subgroups

namespace OperatorSubquotient

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorSubquotient F n)

/-- The operators of `S` given by the elements of the operator algebra lying in the local
centralizer at `v`. -/
def localCentralizerOperators (v : FinitePlace F) : Set (Module.End ℂ S.Space) :=
  {T | ∃ a : automorphicOperatorAlgebra F n, a.val ∈ localCentralizer n v ∧
    T = S.representation a}

theorem commutesWith_localCentralizerOperators (v : FinitePlace F) :
    CommutesWith (S.localRepresentation v) (S.localCentralizerOperators v) := by
  rintro _ ⟨a, ha, rfl⟩ g x
  have hcomm : a * finiteOperator F n (localInclusion F n v g) =
      finiteOperator F n (localInclusion F n v g) * a :=
    Subtype.ext ((mem_localCentralizer.mp ha) g).symm
  have h₁ := LinearMap.congr_fun
    (map_mul S.representation a (finiteOperator F n (localInclusion F n v g))) x
  have h₂ := LinearMap.congr_fun
    (map_mul S.representation (finiteOperator F n (localInclusion F n v g)) a) x
  calc S.representation a (S.localRepresentation v g x)
      = S.representation (a * finiteOperator F n (localInclusion F n v g)) x := h₁.symm
    _ = S.representation (finiteOperator F n (localInclusion F n v g) * a) x :=
        congrArg (fun b => S.representation b x) hcomm
    _ = S.localRepresentation v g (S.representation a x) := h₂

/-- A generator of the operator algebra preserves a subspace stable under the local
translations at `v` and the operators from the local centralizer: a finite translation is a
local translation times a finite translation with identity `v`-component. -/
theorem generator_mem_of_localStable (v : FinitePlace F) (P : Submodule ℂ S.Space)
    (hσ : ∀ (g : FiniteLocalGL F n v), ∀ x ∈ P, S.localRepresentation v g x ∈ P)
    (hC : ∀ c ∈ S.localCentralizerOperators v, ∀ x ∈ P, c x ∈ P)
    {c : FiniteSmoothEnd F n} (hc : c ∈ automorphicOperatorGenerators F n)
    (hc' : c ∈ automorphicOperatorAlgebra F n) :
    ∀ x ∈ P, S.representation ⟨c, hc'⟩ x ∈ P := by
  intro x hx
  rcases hc with (⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩
  · show S.representation (finiteOperator F n d) x ∈ P
    have hs := exists_localSplit F n v d
    obtain ⟨g, d', hd', hd⟩ := hs
    have hmem : S.representation (finiteOperator F n d') ∈ S.localCentralizerOperators v :=
      ⟨finiteOperator F n d', finite_mem_localCentralizer hd', rfl⟩
    have h₁ : S.representation (finiteOperator F n d) x =
        S.representation (finiteOperator F n (localInclusion F n v g * d')) x :=
      congrArg (fun e => S.representation (finiteOperator F n e) x) hd
    have h₂ : S.representation (finiteOperator F n (localInclusion F n v g * d')) x =
        S.localRepresentation v g (S.representation (finiteOperator F n d') x) :=
      (congrArg (fun b => S.representation b x)
        (map_mul (finiteOperator F n) (localInclusion F n v g) d')).trans
        (LinearMap.congr_fun (map_mul S.representation _ _) x)
    have h₃ := hσ g _ (hC _ hmem x hx)
    rw [h₁, h₂]
    exact h₃
  · have hmem : S.representation (compactOperator F n k) ∈ S.localCentralizerOperators v :=
      ⟨compactOperator F n k, compact_mem_localCentralizer v k, rfl⟩
    exact hC _ hmem x hx
  · have hmem : S.representation (differentialOperator F n u) ∈ S.localCentralizerOperators v :=
      ⟨differentialOperator F n u, enveloping_mem_localCentralizer v u, rfl⟩
    exact hC _ hmem x hx

/-- A subspace stable under the local translations at `v` and under the operators from the
local centralizer is stable under the whole operator algebra. -/
theorem representation_mem_of_localStable (v : FinitePlace F) (P : Submodule ℂ S.Space)
    (hσ : ∀ (g : FiniteLocalGL F n v), ∀ x ∈ P, S.localRepresentation v g x ∈ P)
    (hC : ∀ c ∈ S.localCentralizerOperators v, ∀ x ∈ P, c x ∈ P)
    {c : FiniteSmoothEnd F n} (hc : c ∈ Algebra.adjoin ℂ (automorphicOperatorGenerators F n)) :
    ∀ x ∈ P, S.representation ⟨c, hc⟩ x ∈ P := by
  induction hc using Algebra.adjoin_induction with
  | mem c hc => exact S.generator_mem_of_localStable v P hσ hC hc _
  | algebraMap a =>
      intro x hx
      have h : S.representation (algebraMap ℂ (automorphicOperatorAlgebra F n) a) x = a • x :=
        (LinearMap.congr_fun (S.operatorAction.commutes a) x).trans
          (Module.algebraMap_end_apply ℂ ℂ S.Space a x)
      have h' := P.smul_mem a hx
      rw [← h] at h'
      exact h'
  | add c₁ c₂ hc₁ hc₂ ih₁ ih₂ =>
      intro x hx
      have h : S.representation (⟨c₁, hc₁⟩ + ⟨c₂, hc₂⟩ : automorphicOperatorAlgebra F n) x =
          S.representation ⟨c₁, hc₁⟩ x + S.representation ⟨c₂, hc₂⟩ x :=
        LinearMap.congr_fun (S.operatorAction.map_add _ _) x
      have h' := P.add_mem (ih₁ x hx) (ih₂ x hx)
      rw [← h] at h'
      exact h'
  | mul c₁ c₂ hc₁ hc₂ ih₁ ih₂ =>
      intro x hx
      have h : S.representation (⟨c₁, hc₁⟩ * ⟨c₂, hc₂⟩ : automorphicOperatorAlgebra F n) x =
          S.representation ⟨c₁, hc₁⟩ (S.representation ⟨c₂, hc₂⟩ x) :=
        LinearMap.congr_fun (map_mul S.representation _ _) x
      exact (congrArg (fun y => y ∈ P) h).mpr (ih₁ _ (ih₂ x hx))

/-- For an irreducible operator subquotient, the local translations at `v` and the operators
from the local centralizer act irreducibly together. -/
theorem isJointlyIrreducible_localCentralizerOperators (hS : S.IsIrreducible)
    (v : FinitePlace F) :
    IsJointlyIrreducible (S.localRepresentation v) (S.localCentralizerOperators v) := by
  intro P hσ hC
  let R : Subrepresentation S.representation :=
    { toSubmodule := P
      apply_mem_toSubmodule := fun b x hx =>
        S.representation_mem_of_localStable v P hσ hC b.property x hx }
  rcases hS.eq_bot_or_eq_top R with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

/-- The vectors fixed by the elements of `L₀` with identity `v`-component. -/
def awayFixed (v : FinitePlace F) (L₀ : OpenSubgroup (FiniteAdelicGL F n)) :
    Submodule ℂ S.Space :=
  fixedVectors S.finiteRepresentation (awaySubgroup v L₀)

theorem localRepresentation_mem_awayFixed (v : FinitePlace F)
    (L₀ : OpenSubgroup (FiniteAdelicGL F n)) (g : FiniteLocalGL F n v) {x : S.Space}
    (hx : x ∈ S.awayFixed v L₀) : S.localRepresentation v g x ∈ S.awayFixed v L₀ := by
  refine TwoFactorExistence.mem_fixedVectors_iff.mpr fun d hd => ?_
  have hc := (localInclusion_commute_of_localProjection_eq_one F n v
    (mem_awaySubgroup.mp hd).2 g).eq
  calc S.finiteRepresentation d (S.localRepresentation v g x)
      = S.finiteRepresentation (d * localInclusion F n v g) x :=
        (LinearMap.congr_fun (map_mul S.finiteRepresentation d (localInclusion F n v g)) x).symm
    _ = S.finiteRepresentation (localInclusion F n v g * d) x :=
        congrArg (fun e => S.finiteRepresentation e x) hc.symm
    _ = S.localRepresentation v g (S.finiteRepresentation d x) :=
        LinearMap.congr_fun (map_mul S.finiteRepresentation (localInclusion F n v g) d) x
    _ = S.localRepresentation v g x :=
        congrArg (S.localRepresentation v g) (TwoFactorExistence.mem_fixedVectors_iff.mp hx d hd)

theorem compactRepresentation_mem_awayFixed (v : FinitePlace F)
    (L₀ : OpenSubgroup (FiniteAdelicGL F n)) (k : standardInfiniteCompact F n) {x : S.Space}
    (hx : x ∈ S.awayFixed v L₀) : S.compactRepresentation k x ∈ S.awayFixed v L₀ :=
  TwoFactorExistence.mem_fixedVectors_iff.mpr fun d hd =>
    (S.finiteRepresentation_compactRepresentation d k x).trans
      (congrArg (S.compactRepresentation k) (TwoFactorExistence.mem_fixedVectors_iff.mp hx d hd))

/-- `awayFixed` as a subrepresentation of the local translations at `v`. -/
def awayFixedLocal (v : FinitePlace F) (L₀ : OpenSubgroup (FiniteAdelicGL F n)) :
    Subrepresentation (S.localRepresentation v) where
  toSubmodule := S.awayFixed v L₀
  apply_mem_toSubmodule g _ hx := S.localRepresentation_mem_awayFixed v L₀ g hx

/-- `awayFixed` as a subrepresentation of the compact action at infinity. -/
def awayFixedCompact (v : FinitePlace F) (L₀ : OpenSubgroup (FiniteAdelicGL F n)) :
    Subrepresentation S.compactRepresentation where
  toSubmodule := S.awayFixed v L₀
  apply_mem_toSubmodule k _ hx := S.compactRepresentation_mem_awayFixed v L₀ k hx

/-- A vector of `awayFixed v L₀` fixed by `L ≤ GL_n(F_v)` is fixed by
`comparisonSubgroup v L₀ L`: such an element `d` is `inc_v(proj_v d)` times an element of
`L₀` with identity `v`-component. -/
theorem finiteRepresentation_eq_of_mem_comparisonSubgroup (v : FinitePlace F)
    (L₀ : OpenSubgroup (FiniteAdelicGL F n)) (L : OpenSubgroup (FiniteLocalGL F n v))
    {x : S.Space}
    (hx : x ∈ S.awayFixed v L₀ ⊓ fixedVectors (S.localRepresentation v) L.toSubgroup)
    {d : FiniteAdelicGL F n} (hd : d ∈ (comparisonSubgroup v L₀ L).toSubgroup) :
    S.finiteRepresentation d x = x := by
  have hx₁ : x ∈ S.awayFixed v L₀ := (Submodule.mem_inf.mp hx).1
  have hx₂ : x ∈ fixedVectors (S.localRepresentation v) L.toSubgroup :=
    (Submodule.mem_inf.mp hx).2
  have hd₁ := OpenSubgroup.mem_inf.mp hd
  have hd₂ := OpenSubgroup.mem_inf.mp hd₁.1
  have hdL := hd₂.1
  have hd₀ : d ∈ L₀ := hd₂.2
  have hdi := hd₁.2
  have hdL' : localProjection F n v d ∈ L := hdL
  have hdi' : localInclusion F n v (localProjection F n v d) ∈ L₀ := hdi
  have ha : (localInclusion F n v (localProjection F n v d))⁻¹ * d ∈ awaySubgroup v L₀ :=
    mem_awaySubgroup.mpr ⟨mul_mem (inv_mem hdi') hd₀, localProjection_awayPart F n v d⟩
  calc S.finiteRepresentation d x
      = S.finiteRepresentation (localInclusion F n v (localProjection F n v d) *
          ((localInclusion F n v (localProjection F n v d))⁻¹ * d)) x :=
        congrArg (fun e => S.finiteRepresentation e x) (mul_inv_cancel_left _ _).symm
    _ = S.localRepresentation v (localProjection F n v d)
          (S.finiteRepresentation
            ((localInclusion F n v (localProjection F n v d))⁻¹ * d) x) :=
        LinearMap.congr_fun (map_mul S.finiteRepresentation _ _) x
    _ = S.localRepresentation v (localProjection F n v d) x :=
        congrArg (S.localRepresentation v (localProjection F n v d))
          (TwoFactorExistence.mem_fixedVectors_iff.mp hx₁ _ ha)
    _ = x := TwoFactorExistence.mem_fixedVectors_iff.mp hx₂ _ hdL'

/-- Equivariant maps from `τ` into the vectors of `awayFixed v L₀` fixed by `L` lie in the
joint multiplicity space of `comparisonSubgroup v L₀ L`. -/
theorem equivariantInto_le_jointMultiplicitySpace (v : FinitePlace F)
    (L₀ : OpenSubgroup (FiniteAdelicGL F n)) (L : OpenSubgroup (FiniteLocalGL F n v)) {m : ℕ}
    (τ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    equivariantInto S.compactRepresentation τ
        ((S.awayFixedLocal v L₀).toSubmodule ⊓
          fixedVectors (S.localRepresentation v) L.toSubgroup) ≤
      jointMultiplicitySpace S.finiteRepresentation S.compactRepresentation
        (comparisonSubgroup v L₀ L).toSubgroup τ :=
  fun _ hφ => ⟨fun w => TwoFactorExistence.mem_fixedVectors_iff.mpr fun _ hd =>
    S.finiteRepresentation_eq_of_mem_comparisonSubgroup v L₀ L (hφ.1 w) hd, hφ.2⟩

/-- **Isotypic restriction to a finite place.** An irreducible jointly admissible operator
subquotient has an irreducible admissible subrepresentation `U` of its restriction to
`GL_n(F_v)` such that the restriction is spanned by the images of the intertwining maps
from `U`. -/
theorem exists_isotypic_subrepresentation (hS : S.IsIrreducible) (hA : S.IsJointlyAdmissible)
    (v : FinitePlace F) :
    ∃ U : Subrepresentation (S.localRepresentation v), U.toRepresentation.IsIrreducible ∧
      IsAdmissible U.toRepresentation ∧
      ⨆ f : U.toRepresentation.IntertwiningMap (S.localRepresentation v),
        LinearMap.range f.toLinearMap = ⊤ := by
  have := hS
  have hne : ∃ x₀ : S.Space, x₀ ≠ 0 := by
    by_contra! h
    apply (top_ne_bot : (⊤ : Subrepresentation S.representation) ≠ ⊥)
    apply Subrepresentation.toSubmodule_injective
    exact (Submodule.eq_bot_iff _).mpr fun x _ => h x
  obtain ⟨x₀, hx₀⟩ := hne
  have hsm := S.finiteRepresentation_isSmooth x₀
  obtain ⟨L₀, hL₀⟩ := hsm
  have hx₀P : x₀ ∈ S.awayFixed v L₀ := TwoFactorExistence.mem_fixedVectors_iff.mpr fun d hd =>
    TwoFactorExistence.mem_fixedVectors_iff.mp hL₀ d (mem_awaySubgroup.mp hd).1
  let E := orbitSubrepresentation S.compactRepresentation x₀
  have hE : Module.Finite ℂ E.toSubmodule := S.compactRepresentation_isFiniteVector x₀
  have hEfree : Module.Free ℂ E.toSubmodule := Module.Free.of_divisionRing ℂ E.toSubmodule
  let e := (Module.finBasis ℂ E.toSubmodule).equivFun
  let τ : Representation ℂ (standardInfiniteCompact F n)
      (Fin (Module.finrank ℂ E.toSubmodule) → ℂ) :=
    (MonoidHomClass.toMonoidHom (e.conjAlgEquiv ℂ)).comp E.toRepresentation
  let φ₀ : (Fin (Module.finrank ℂ E.toSubmodule) → ℂ) →ₗ[ℂ] S.Space :=
    E.toSubmodule.subtype ∘ₗ e.symm.toLinearMap
  have key : ∀ z : E.toSubmodule, φ₀ (e z) = z := fun z =>
    congrArg Subtype.val (e.symm_apply_apply z)
  have hφ₀ : φ₀ ∈ equivariantInto S.compactRepresentation τ (S.awayFixedLocal v L₀).toSubmodule := by
    refine ⟨fun w => orbitSpan_le _ x₀ (S.awayFixedCompact v L₀) hx₀P (e.symm w).2,
      fun k w => ?_⟩
    calc φ₀ (τ k w) = φ₀ (e (E.toRepresentation k (e.symm w))) := rfl
      _ = ((E.toRepresentation k (e.symm w) : E.toSubmodule) : S.Space) := key _
      _ = S.compactRepresentation k (φ₀ w) := rfl
  have hw₀ : φ₀ (e ⟨x₀, self_mem_orbitSpan _ x₀⟩) ≠ 0 := fun h =>
    hx₀ ((key ⟨x₀, self_mem_orbitSpan _ x₀⟩).symm.trans h)
  refine exists_irreducible_admissible_isotypic_of_typeSpan
    (S.commutesWith_localCentralizerOperators v)
    (S.isJointlyIrreducible_localCentralizerOperators hS v) (S.localRepresentation_isSmooth v)
    ?_ ?_ (S.awayFixedLocal v L₀) ?_ hφ₀ hw₀
  · intro W
    have hW := compactOpen_cofinal F n v W
    obtain ⟨K, hK, hKW⟩ := hW
    exact ⟨K, hKW, hK⟩
  · intro k g x
    exact (S.finiteRepresentation_compactRepresentation (localInclusion F n v g) k x).symm
  · intro L _
    have := hA (comparisonSubgroup v L₀ L) _ τ
    exact Submodule.finiteDimensional_of_le (S.equivariantInto_le_jointMultiplicitySpace v L₀ L τ)

end OperatorSubquotient

section Canonical

variable {F : Type u} [Field F] [NumberField F]

/-- The canonical p-adic matrix topology on `GL_n(F_v)`, the one of the correspondence
category `AutomorphicObject (padicField v)`. -/
local instance finitePlaceCanonicalTopology (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (FiniteLocalGL F n v) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- **Local components at the finite places** (the finite-place conjunct of
`LocalComponentExistenceStatement`): an irreducible jointly admissible operator subquotient
of `GL_(r+1)` is, at every finite place `v`, isotypic for an irreducible admissible smooth
representation of `GL_(r+1)(F_v)`. -/
theorem localComponentExistence_finitePlace (r : ℕ) (Q : IrreducibleOperatorSubquotient F r)
    (hQ : Q.subquotient.IsJointlyAdmissible) (v : FinitePlace F) :
    ∃ A : AutomorphicObject.{u, u} (padicField v) r.succPNat,
      Q.subquotient.IsFinitePlaceIsotypic v A.obj.representation := by
  have hU := Q.subquotient.exists_isotypic_subrepresentation Q.irreducible hQ v
  obtain ⟨U, hUirr, hUadm, hUiso⟩ := hU
  have hadm : IsAdmissible U.toRepresentation := isAdmissible_canonicalTopology hUadm
  exact ⟨⟨SmoothRep.of U.toRepresentation hadm.1, hUirr, hadm⟩, hUiso⟩

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Reduction of `LocalComponentExistenceStatement` to the infinite places.** The
finite-place conjunct holds by `localComponentExistence_finitePlace`; the statement follows
from its real-place and complex-place conjuncts. -/
theorem localComponentExistenceStatement_of_infinitePlaces
    (h : ∀ (F : Type u) [Field F] [NumberField F] (r : ℕ)
      (Q : IrreducibleOperatorSubquotient F r), Q.subquotient.IsJointlyAdmissible →
      (∀ v : {v : NumberField.InfinitePlace F // v.IsReal},
        ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
          (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
          Archimedean.IsRealGKModule (r + 1) ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
            Archimedean.IsAdmissibleGKModule ρ ∧ Q.subquotient.IsRealPlaceIsotypic v ρ π) ∧
      ∀ v : {v : NumberField.InfinitePlace F // v.IsComplex},
        ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
          (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
          Archimedean.IsComplexGKModule (r + 1) ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
            Archimedean.IsAdmissibleGKModule ρ ∧ Q.subquotient.IsComplexPlaceIsotypic v ρ π) :
    LocalComponentExistenceStatement.{u} := by
  intro F _ _ r Q hQ
  have hinf := h F r Q hQ
  exact ⟨fun v => localComponentExistence_finitePlace r Q hQ v, hinf.1, hinf.2⟩

end Canonical

end Langlands.Automorphic
