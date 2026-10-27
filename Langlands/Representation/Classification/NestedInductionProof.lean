import Langlands.Representation.Classification.NestedInductionStatement
import Langlands.Representation.Parabolic.ComposedFlattenedInductionProof
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Twist.SmoothProof
import Langlands.Group.GL.CompactOpen

/-!
# Proof of normalized induction in stages inside a product Levi
-/

noncomputable section

namespace Langlands

universe uF uV uM uW uK

namespace NestedInductionProof

open GeneralLinear Geometric

section Groups

variable (K : Type uK) [CommRing K] {n : ℕ}

/-- The composite parabolic of a refinement is the parabolic of its flattening. -/
theorem composedParabolic_flatten (X : BlockShape n) (Y : BlockRefinement X) :
    Parabolic.composedParabolic K X Y = (X.flatten Y).parabolic K :=
  (X.flatten Y).composedParabolic_eq_of_coordinates X Y (X.flattenBlockEquiv Y)
    (fun a => (X.flatten_size_flattenBlockEquiv Y a).symm) K
    (fun i k x => X.index_index_eq_flatten Y ⟨i, k⟩ x)

/-- A product-Levi element lies in the refined parabolic exactly when its block
diagonal matrix lies in the flattened parabolic. -/
theorem mem_refinedParabolic_iff (X : BlockShape n) (Y : BlockRefinement X)
    (g : X.Levi K) :
    g ∈ refinedParabolic K X Y ↔ X.leviEmbedding K g ∈ (X.flatten Y).parabolic K := by
  rw [← composedParabolic_flatten K X Y]
  change _ ↔ _ ∈ Parabolic.leviPreimage K X (refinedParabolic K X Y)
  rw [Parabolic.mem_leviPreimage_iff]
  constructor
  · intro hg
    refine ⟨(X.leviInParabolic K g).property, ?_⟩
    change X.leviProjection K (X.leviInParabolic K g) ∈ _
    rw [X.leviProjection_section]
    exact hg
  · rintro ⟨_, hg⟩
    have h' : X.leviProjection K (X.leviInParabolic K g) ∈ refinedParabolic K X Y := hg
    rw [X.leviProjection_section] at h'
    exact h'

/-- Flattened Levi projection, transported to the refined Levi, is the refined
projection of the coarse Levi projection. -/
theorem flattenedLeviEquiv_leviProjection (X : BlockShape n) (Y : BlockRefinement X)
    (y : GeneralLinear n K) (hy : y ∈ (X.flatten Y).parabolic K)
    (hyX : y ∈ X.parabolic K)
    (hyY : X.leviProjection K ⟨y, hyX⟩ ∈ refinedParabolic K X Y) :
    flattenedLeviEquiv K X Y ((X.flatten Y).leviProjection K ⟨y, hy⟩) =
      refinedLeviProjection K X Y ⟨X.leviProjection K ⟨y, hyX⟩, hyY⟩ := by
  have h := (X.flatten Y).composedLeviProjection_parabolicRefinementEquiv X Y
    (X.flattenBlockEquiv Y) (fun a => (X.flatten_size_flattenBlockEquiv Y a).symm) K
    (fun i k x => X.index_index_eq_flatten Y ⟨i, k⟩ x) ⟨y, hy⟩
  rw [BlockShape.leviRefinementEquiv_flatten] at h
  exact h.symm

/-- The flattened Levi projection of a block diagonal refined-parabolic element. -/
theorem flatten_leviProjection_embedding (X : BlockShape n) (Y : BlockRefinement X)
    (q : refinedParabolic K X Y)
    (hq : X.leviEmbedding K q.val ∈ (X.flatten Y).parabolic K) :
    (X.flatten Y).leviProjection K ⟨X.leviEmbedding K q.val, hq⟩ =
      (flattenedLeviEquiv K X Y).symm (refinedLeviProjection K X Y q) := by
  have hq' : X.leviProjection K (X.leviInParabolic K q.val) ∈ refinedParabolic K X Y := by
    rw [X.leviProjection_section]
    exact q.property
  rw [MulEquiv.eq_symm_apply, flattenedLeviEquiv_leviProjection K X Y _ hq
    (X.leviInParabolic K q.val).property hq']
  congr 1
  apply Subtype.ext
  exact X.leviProjection_section K q.val

/-- Transport of a flattened Levi element along an equality of shapes. -/
def leviCast {X Y : BlockShape n} (h : X = Y) : X.Levi K ≃* Y.Levi K := by
  subst h
  exact MulEquiv.refl _

theorem leviProjection_cast {X Y : BlockShape n} (h : X = Y) (y : GeneralLinear n K)
    (hX : y ∈ X.parabolic K) (hY : y ∈ Y.parabolic K) :
    Y.leviProjection K ⟨y, hY⟩ = leviCast K h (X.leviProjection K ⟨y, hX⟩) := by
  subst h
  rfl

theorem leviEmbedding_cast {X Y : BlockShape n} (h : X = Y) (m : X.Levi K) :
    Y.leviEmbedding K (leviCast K h m) = X.leviEmbedding K m := by
  subst h
  rfl

variable (B : BlockShape n) (Q : BlockRefinement B) (R : BlockRefinement (B.flatten Q))

/-- The direct refined parabolic is the subgroup of the middle refined parabolic
whose middle Levi part lies in the fine refined parabolic. -/
theorem mem_composeRefinement_iff (g : B.Levi K) :
    g ∈ refinedParabolic K B (B.composeRefinement Q R) ↔
      ∃ hg : g ∈ refinedParabolic K B Q,
        (flattenedLeviEquiv K B Q).symm (refinedLeviProjection K B Q ⟨g, hg⟩) ∈
          refinedParabolic K (B.flatten Q) R := by
  rw [mem_refinedParabolic_iff K B (B.composeRefinement Q R),
    ← B.flatten_composeRefinement Q R, ← composedParabolic_flatten K (B.flatten Q) R]
  change _ ∈ Parabolic.leviPreimage K (B.flatten Q) (refinedParabolic K (B.flatten Q) R) ↔ _
  rw [Parabolic.mem_leviPreimage_iff]
  constructor
  · rintro ⟨hD, hR⟩
    have hg := (mem_refinedParabolic_iff K B Q g).mpr hD
    refine ⟨hg, ?_⟩
    rw [← flatten_leviProjection_embedding K B Q ⟨g, hg⟩ hD]
    exact hR
  · rintro ⟨hg, hR⟩
    have hD := (mem_refinedParabolic_iff K B Q g).mp hg
    refine ⟨hD, ?_⟩
    rw [flatten_leviProjection_embedding K B Q ⟨g, hg⟩ hD]
    exact hR

/-- The direct Levi projection is the fine projection of the middle projection,
after the actual shape transport. -/
theorem composeRefinement_leviProjection
    (g : refinedParabolic K B (B.composeRefinement Q R))
    (hg : g.val ∈ refinedParabolic K B Q)
    (hR : (flattenedLeviEquiv K B Q).symm (refinedLeviProjection K B Q ⟨g.val, hg⟩) ∈
      refinedParabolic K (B.flatten Q) R) :
    (flattenedLeviEquiv K B (B.composeRefinement Q R)).symm
        (refinedLeviProjection K B (B.composeRefinement Q R) g) =
      leviCast K (B.flatten_composeRefinement Q R)
        ((flattenedLeviEquiv K (B.flatten Q) R).symm
          (refinedLeviProjection K (B.flatten Q) R ⟨_, hR⟩)) := by
  have hS := (mem_refinedParabolic_iff K B (B.composeRefinement Q R) g.val).mp g.property
  have hFR : B.leviEmbedding K g.val ∈ ((B.flatten Q).flatten R).parabolic K := by
    rw [B.flatten_composeRefinement Q R]
    exact hS
  have hD := (mem_refinedParabolic_iff K B Q g.val).mp hg
  have hDR : (B.flatten Q).leviProjection K ⟨B.leviEmbedding K g.val, hD⟩ ∈
      refinedParabolic K (B.flatten Q) R := by
    rw [flatten_leviProjection_embedding K B Q ⟨g.val, hg⟩ hD]
    exact hR
  rw [← flatten_leviProjection_embedding K B (B.composeRefinement Q R) g hS,
    leviProjection_cast K (B.flatten_composeRefinement Q R) _ hFR hS]
  congr 1
  rw [MulEquiv.eq_symm_apply, flattenedLeviEquiv_leviProjection K (B.flatten Q) R _ hFR hD hDR]
  congr 1
  apply Subtype.ext
  exact flatten_leviProjection_embedding K B Q ⟨g.val, hg⟩ hD

end Groups

section Modulus

open scoped NNReal

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- The flattened full modulus is the outer modulus times the inner product modulus. -/
theorem leviModulus_flatten (X : BlockShape n) (Y : BlockRefinement X)
    (m : refinedLevi F.Carrier X Y) :
    T.leviModulus X m.val * T.refinedLeviModulus X Y m =
      T.leviModulus (X.flatten Y) ((flattenedLeviEquiv F.Carrier X Y).symm m) := by
  have h := DFunLike.congr_fun (T.composedLeviModulus_flattened X Y)
    ((flattenedLeviEquiv F.Carrier X Y).symm m)
  rw [← h]
  simp [PadicField.TopologicalData.composedLeviModulus]

theorem leviModulus_cast {X Y : BlockShape n} (h : X = Y) (m : X.Levi F.Carrier) :
    T.leviModulus Y (leviCast F.Carrier h m) = T.leviModulus X m := by
  subst h
  rfl

variable (B : BlockShape n) (Q : BlockRefinement B) (R : BlockRefinement (B.flatten Q))

/-- The direct inner modulus is the product of the middle and fine inner moduli. -/
theorem refinedLeviModulus_compose
    (g : refinedParabolic F.Carrier B (B.composeRefinement Q R))
    (hg : g.val ∈ refinedParabolic F.Carrier B Q)
    (hR : (flattenedLeviEquiv F.Carrier B Q).symm
      (refinedLeviProjection F.Carrier B Q ⟨g.val, hg⟩) ∈
        refinedParabolic F.Carrier (B.flatten Q) R) :
    T.refinedLeviModulus B (B.composeRefinement Q R)
        (refinedLeviProjection F.Carrier B (B.composeRefinement Q R) g) =
      T.refinedLeviModulus B Q (refinedLeviProjection F.Carrier B Q ⟨g.val, hg⟩) *
        T.refinedLeviModulus (B.flatten Q) R
          (refinedLeviProjection F.Carrier (B.flatten Q) R ⟨_, hR⟩) := by
  have hS := leviModulus_flatten T B (B.composeRefinement Q R)
    (refinedLeviProjection F.Carrier B (B.composeRefinement Q R) g)
  have hQ := leviModulus_flatten T B Q (refinedLeviProjection F.Carrier B Q ⟨g.val, hg⟩)
  have hD := leviModulus_flatten T (B.flatten Q) R
    (refinedLeviProjection F.Carrier (B.flatten Q) R ⟨_, hR⟩)
  have oS := T.refinedOuterModulus_projection B (B.composeRefinement Q R) g
  have oQ := T.refinedOuterModulus_projection B Q ⟨g.val, hg⟩
  have oD := T.refinedOuterModulus_projection (B.flatten Q) R ⟨_, hR⟩
  simp only [PadicField.TopologicalData.refinedOuterModulus_apply] at oS oQ oD
  rw [oS, composeRefinement_leviProjection F.Carrier B Q R g hg hR, leviModulus_cast,
    ← hD, oD, ← hQ, oQ, mul_assoc] at hS
  exact mul_left_cancel hS

/-- The positive half moduli satisfy the same product formula. -/
theorem refinedLeviHalfModulus_compose
    (g : refinedParabolic F.Carrier B (B.composeRefinement Q R))
    (hg : g.val ∈ refinedParabolic F.Carrier B Q)
    (hR : (flattenedLeviEquiv F.Carrier B Q).symm
      (refinedLeviProjection F.Carrier B Q ⟨g.val, hg⟩) ∈
        refinedParabolic F.Carrier (B.flatten Q) R) :
    T.refinedLeviHalfModulus B (B.composeRefinement Q R)
        (refinedLeviProjection F.Carrier B (B.composeRefinement Q R) g) =
      T.refinedLeviHalfModulus B Q (refinedLeviProjection F.Carrier B Q ⟨g.val, hg⟩) *
        T.refinedLeviHalfModulus (B.flatten Q) R
          (refinedLeviProjection F.Carrier (B.flatten Q) R ⟨_, hR⟩) := by
  simp only [PadicField.TopologicalData.refinedLeviHalfModulus, MonoidHom.comp_apply,
    Jacquet.complexCharacter, Jacquet.positiveHalfCharacter,
    refinedLeviModulus_compose T B Q R g hg hR, map_mul]

end Modulus

section Cast

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Transport of a Levi representation along a shape equality is evaluation
through the corresponding Levi transport. -/
theorem cast_apply (K : Type uK) [CommRing K] {X Y : BlockShape n} (h : X = Y)
    (ω : Representation ℂ (X.Levi K) V) (x : X.Levi K) :
    (h ▸ ω : Representation ℂ (Y.Levi K) V) (leviCast K h x) = ω x := by
  subst h
  rfl

end Cast

section Comparison

set_option maxHeartbeats 1600000

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n) (Q : BlockRefinement B) (R : BlockRefinement (B.flatten Q))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ω : Representation ℂ (((B.flatten Q).flatten R).Levi F.Carrier) V)
  (ωB : Representation ℂ ((B.flatten (B.composeRefinement Q R)).Levi F.Carrier) V)

/-- Fine normalized induction from the fine refined subgroup to the middle Levi. -/
private abbrev midRep :=
  T.normalizedRefinedInduced (B.flatten Q) R
    (ω.comp (flattenedLeviEquiv F.Carrier (B.flatten Q) R).symm.toMonoidHom)

private abbrev Mid :=
  letI := T.topology
  letI := T.leviTopologicalGroup (B.flatten Q)
  Induction.SmoothFunctions (refinedParabolic F.Carrier (B.flatten Q) R)
    (twist (T.refinedParabolicHalfModulus (B.flatten Q) R)
      ((ω.comp (flattenedLeviEquiv F.Carrier (B.flatten Q) R).symm.toMonoidHom).comp
        (refinedLeviProjection F.Carrier (B.flatten Q) R)))

private abbrev Iter :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  Induction.SmoothFunctions (refinedParabolic F.Carrier B Q)
    (twist (T.refinedParabolicHalfModulus B Q)
      (((midRep T B Q R ω).comp (flattenedLeviEquiv F.Carrier B Q).symm.toMonoidHom).comp
        (refinedLeviProjection F.Carrier B Q)))

private abbrev Direct :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  Induction.SmoothFunctions (refinedParabolic F.Carrier B (B.composeRefinement Q R))
    (twist (T.refinedParabolicHalfModulus B (B.composeRefinement Q R))
      ((ωB.comp (flattenedLeviEquiv F.Carrier B (B.composeRefinement Q R)).symm.toMonoidHom).comp
        (refinedLeviProjection F.Carrier B (B.composeRefinement Q R))))

private theorem mid_cov (φ : Mid T B Q R ω) (r : refinedParabolic F.Carrier (B.flatten Q) R)
    (m : (B.flatten Q).Levi F.Carrier) :
    φ.val.val (r.val * m) =
      (T.refinedLeviHalfModulus (B.flatten Q) R
        (refinedLeviProjection F.Carrier (B.flatten Q) R r) : ℂ) •
        ω ((flattenedLeviEquiv F.Carrier (B.flatten Q) R).symm
          (refinedLeviProjection F.Carrier (B.flatten Q) R r)) (φ.val.val m) :=
  φ.val.property r m

private theorem iter_cov (f : Iter T B Q R ω) (q : refinedParabolic F.Carrier B Q)
    (g : B.Levi F.Carrier) (m : (B.flatten Q).Levi F.Carrier) :
    (f.val.val (q.val * g)).val.val m =
      (T.refinedLeviHalfModulus B Q (refinedLeviProjection F.Carrier B Q q) : ℂ) •
        (f.val.val g).val.val
          (m * (flattenedLeviEquiv F.Carrier B Q).symm (refinedLeviProjection F.Carrier B Q q)) :=
  congrArg (fun φ : Mid T B Q R ω => φ.val.val m) (f.val.property q g)

private theorem direct_cov (f : Direct T B Q R ωB)
    (s : refinedParabolic F.Carrier B (B.composeRefinement Q R)) (g : B.Levi F.Carrier) :
    f.val.val (s.val * g) =
      (T.refinedLeviHalfModulus B (B.composeRefinement Q R)
        (refinedLeviProjection F.Carrier B (B.composeRefinement Q R) s) : ℂ) •
        ωB ((flattenedLeviEquiv F.Carrier B (B.composeRefinement Q R)).symm
          (refinedLeviProjection F.Carrier B (B.composeRefinement Q R) s)) (f.val.val g) :=
  f.val.property s g

/-- The middle Levi image of a fine refined-parabolic element lies in the direct
refined parabolic, with the fine Levi part and the product half modulus. -/
private theorem section_direct (r : refinedParabolic F.Carrier (B.flatten Q) R) :
    ∃ hs : (flattenedLeviEquiv F.Carrier B Q r.val).val ∈
        refinedParabolic F.Carrier B (B.composeRefinement Q R),
      (flattenedLeviEquiv F.Carrier B (B.composeRefinement Q R)).symm
          (refinedLeviProjection F.Carrier B (B.composeRefinement Q R) ⟨_, hs⟩) =
        leviCast F.Carrier (B.flatten_composeRefinement Q R)
          ((flattenedLeviEquiv F.Carrier (B.flatten Q) R).symm
            (refinedLeviProjection F.Carrier (B.flatten Q) R r)) ∧
      T.refinedLeviHalfModulus B (B.composeRefinement Q R)
          (refinedLeviProjection F.Carrier B (B.composeRefinement Q R) ⟨_, hs⟩) =
        T.refinedLeviHalfModulus B Q (flattenedLeviEquiv F.Carrier B Q r.val) *
          T.refinedLeviHalfModulus (B.flatten Q) R
            (refinedLeviProjection F.Carrier (B.flatten Q) R r) := by
  have hg : (flattenedLeviEquiv F.Carrier B Q r.val).val ∈ refinedParabolic F.Carrier B Q :=
    (refinedLeviSection F.Carrier B Q (flattenedLeviEquiv F.Carrier B Q r.val)).property
  have hp : refinedLeviProjection F.Carrier B Q ⟨_, hg⟩ = flattenedLeviEquiv F.Carrier B Q r.val :=
    refinedLeviProjection_section F.Carrier B Q _
  have hR : (flattenedLeviEquiv F.Carrier B Q).symm
      (refinedLeviProjection F.Carrier B Q ⟨_, hg⟩) ∈ refinedParabolic F.Carrier (B.flatten Q) R := by
    rw [hp, MulEquiv.symm_apply_apply]
    exact r.property
  have hrr : (⟨_, hR⟩ : refinedParabolic F.Carrier (B.flatten Q) R) = r :=
    Subtype.ext (by simp only [hp, MulEquiv.symm_apply_apply])
  have hs := (mem_composeRefinement_iff F.Carrier B Q R _).mpr ⟨hg, hR⟩
  refine ⟨hs, ?_, ?_⟩
  · have h := composeRefinement_leviProjection F.Carrier B Q R ⟨_, hs⟩ hg hR
    rw [hrr] at h
    exact h
  · have h := refinedLeviHalfModulus_compose T B Q R ⟨_, hs⟩ hg hR
    rw [hrr, hp] at h
    exact h

/-- Direct induction ignores the part of a middle refined-parabolic element
with trivial middle Levi projection. -/
private theorem direct_projQ (f : Direct T B Q R ωB) (y : refinedParabolic F.Carrier B Q)
    (g : B.Levi F.Carrier) :
    f.val.val (y.val * g) = f.val.val ((refinedLeviProjection F.Carrier B Q y).val * g) := by
  let x := refinedLeviProjection F.Carrier B Q y
  let u : refinedParabolic F.Carrier B Q := y * (refinedLeviSection F.Carrier B Q x)⁻¹
  have hu : refinedLeviProjection F.Carrier B Q u = 1 := by
    simp only [u, x, map_mul, map_inv, refinedLeviProjection_section, mul_inv_cancel]
  have hR : (flattenedLeviEquiv F.Carrier B Q).symm
      (refinedLeviProjection F.Carrier B Q ⟨u.val, u.property⟩) ∈
        refinedParabolic F.Carrier (B.flatten Q) R := by
    change (flattenedLeviEquiv F.Carrier B Q).symm (refinedLeviProjection F.Carrier B Q u) ∈ _
    rw [hu, map_one]
    exact one_mem _
  have hs := (mem_composeRefinement_iff F.Carrier B Q R u.val).mpr ⟨u.property, hR⟩
  have hproj : refinedLeviProjection F.Carrier B (B.composeRefinement Q R) ⟨u.val, hs⟩ = 1 := by
    have h1 := composeRefinement_leviProjection F.Carrier B Q R ⟨u.val, hs⟩ u.property hR
    have hr1 : (⟨_, hR⟩ : refinedParabolic F.Carrier (B.flatten Q) R) = 1 := by
      apply Subtype.ext
      change (flattenedLeviEquiv F.Carrier B Q).symm (refinedLeviProjection F.Carrier B Q u) = 1
      rw [hu, map_one]
    rw [hr1, map_one, map_one, map_one] at h1
    exact (MulEquiv.map_eq_one_iff _).mp h1
  have h := direct_cov T B Q R ωB f ⟨u.val, hs⟩ (x.val * g)
  rw [hproj, map_one, map_one, Units.val_one, one_smul, map_one, Module.End.one_apply] at h
  have hu' : u.val * (x.val * g) = y.val * g := by
    simp only [u, Subgroup.coe_mul, Subgroup.coe_inv, refinedLeviSection_val, mul_assoc,
      inv_mul_cancel_left]
  rw [hu'] at h
  exact h

private theorem iter_cov_one (f : Iter T B Q R ω) (q : B.Levi F.Carrier)
    (hq : q ∈ refinedParabolic F.Carrier B Q) (g : B.Levi F.Carrier) :
    (f.val.val (q * g)).val.val 1 =
      (T.refinedLeviHalfModulus B Q (refinedLeviProjection F.Carrier B Q ⟨q, hq⟩) : ℂ) •
        (f.val.val g).val.val
          ((flattenedLeviEquiv F.Carrier B Q).symm (refinedLeviProjection F.Carrier B Q ⟨q, hq⟩)) := by
  have h := iter_cov T B Q R ω f ⟨q, hq⟩ g 1
  rw [one_mul] at h
  exact h

private theorem mid_cov_one (φ : Mid T B Q R ω) (r : (B.flatten Q).Levi F.Carrier)
    (hr : r ∈ refinedParabolic F.Carrier (B.flatten Q) R) :
    φ.val.val r =
      (T.refinedLeviHalfModulus (B.flatten Q) R
        (refinedLeviProjection F.Carrier (B.flatten Q) R ⟨r, hr⟩) : ℂ) •
        ω ((flattenedLeviEquiv F.Carrier (B.flatten Q) R).symm
          (refinedLeviProjection F.Carrier (B.flatten Q) R ⟨r, hr⟩)) (φ.val.val 1) := by
  have h := mid_cov T B Q R ω φ ⟨r, hr⟩ 1
  rw [mul_one] at h
  exact h

variable (hω : ∀ x, ωB (leviCast F.Carrier (B.flatten_composeRefinement Q R) x) = ω x)

include hω in
/-- Scalar bookkeeping for `forward_cov`, stated with a free vector so that rewriting
happens in a small goal. -/
private theorem forward_scalar (s : refinedParabolic F.Carrier B (B.composeRefinement Q R))
    (hg : s.val ∈ refinedParabolic F.Carrier B Q)
    (hR : (flattenedLeviEquiv F.Carrier B Q).symm
      (refinedLeviProjection F.Carrier B Q ⟨s.val, hg⟩) ∈
        refinedParabolic F.Carrier (B.flatten Q) R) (v : V) :
    (T.refinedLeviHalfModulus B Q (refinedLeviProjection F.Carrier B Q ⟨s.val, hg⟩) : ℂ) •
      ((T.refinedLeviHalfModulus (B.flatten Q) R
        (refinedLeviProjection F.Carrier (B.flatten Q) R ⟨_, hR⟩) : ℂ) •
        ω ((flattenedLeviEquiv F.Carrier (B.flatten Q) R).symm
          (refinedLeviProjection F.Carrier (B.flatten Q) R ⟨_, hR⟩)) v) =
      (T.refinedLeviHalfModulus B (B.composeRefinement Q R)
        (refinedLeviProjection F.Carrier B (B.composeRefinement Q R) s) : ℂ) •
        ωB ((flattenedLeviEquiv F.Carrier B (B.composeRefinement Q R)).symm
          (refinedLeviProjection F.Carrier B (B.composeRefinement Q R) s)) v := by
  rw [composeRefinement_leviProjection F.Carrier B Q R s hg hR, hω,
    refinedLeviHalfModulus_compose T B Q R s hg hR, Units.val_mul, mul_smul]

include hω in
private theorem forward_cov (f : Iter T B Q R ω)
    (s : refinedParabolic F.Carrier B (B.composeRefinement Q R)) (g : B.Levi F.Carrier) :
    (f.val.val (s.val * g)).val.val 1 =
      (T.refinedLeviHalfModulus B (B.composeRefinement Q R)
        (refinedLeviProjection F.Carrier B (B.composeRefinement Q R) s) : ℂ) •
        ωB ((flattenedLeviEquiv F.Carrier B (B.composeRefinement Q R)).symm
          (refinedLeviProjection F.Carrier B (B.composeRefinement Q R) s))
          ((f.val.val g).val.val 1) := by
  obtain ⟨hg, hR⟩ := (mem_composeRefinement_iff F.Carrier B Q R s.val).mp s.property
  have e2 : (f.val.val g).val.val
      ((flattenedLeviEquiv F.Carrier B Q).symm (refinedLeviProjection F.Carrier B Q ⟨s.val, hg⟩)) =
      (T.refinedLeviHalfModulus (B.flatten Q) R
        (refinedLeviProjection F.Carrier (B.flatten Q) R ⟨_, hR⟩) : ℂ) •
        ω ((flattenedLeviEquiv F.Carrier (B.flatten Q) R).symm
          (refinedLeviProjection F.Carrier (B.flatten Q) R ⟨_, hR⟩)) ((f.val.val g).val.val 1) :=
    mid_cov_one T B Q R ω (f.val.val g) _ hR
  exact (iter_cov_one T B Q R ω f s.val hg g).trans
    ((congrArg ((T.refinedLeviHalfModulus B Q
      (refinedLeviProjection F.Carrier B Q ⟨s.val, hg⟩) : ℂ) • ·) e2).trans
      (forward_scalar T B Q R ω ωB hω s hg hR _))

include hω in
private def forward (f : Iter T B Q R ω) : Direct T B Q R ωB := by
  letI := T.topology
  letI := T.leviTopologicalGroup B
  letI := T.leviTopologicalGroup (B.flatten Q)
  let K := Classical.choose f.property
  have hK := Classical.choose_spec f.property
  refine Induction.smoothFunctionOf _ _ (fun g => (f.val.val g).val.val 1) ?_ K ?_
  · intro s g
    exact forward_cov T B Q R ω ωB hω f s g
  · intro k g
    exact congrArg (fun h : Induction.EquivariantFunctions _ _ => (h.val g).val.val 1) (hK k)

private def inverseValue (f : Direct T B Q R ωB) (g : B.Levi F.Carrier)
    (m : (B.flatten Q).Levi F.Carrier) : V :=
  (T.refinedLeviHalfModulus B Q (flattenedLeviEquiv F.Carrier B Q m) : ℂ)⁻¹ •
    f.val.val ((flattenedLeviEquiv F.Carrier B Q m).val * g)

include hω in
private theorem inverseValue_cov (f : Direct T B Q R ωB) (g : B.Levi F.Carrier)
    (r : refinedParabolic F.Carrier (B.flatten Q) R) (m : (B.flatten Q).Levi F.Carrier) :
    inverseValue T B Q R ωB f g (r.val * m) =
      (T.refinedLeviHalfModulus (B.flatten Q) R
        (refinedLeviProjection F.Carrier (B.flatten Q) R r) : ℂ) •
        ω ((flattenedLeviEquiv F.Carrier (B.flatten Q) R).symm
          (refinedLeviProjection F.Carrier (B.flatten Q) R r))
          (inverseValue T B Q R ωB f g m) := by
  obtain ⟨hs, hp, hδ⟩ := section_direct T B Q R r
  have h := direct_cov T B Q R ωB f ⟨_, hs⟩
    ((flattenedLeviEquiv F.Carrier B Q m).val * g)
  rw [hp, hω, hδ, Units.val_mul] at h
  dsimp only at h
  unfold inverseValue
  rw [map_mul (flattenedLeviEquiv F.Carrier B Q), Subgroup.coe_mul,
    mul_assoc (flattenedLeviEquiv F.Carrier B Q r.val).val, h, map_mul, Units.val_mul,
    map_smul, smul_smul, smul_smul]
  congr 1
  have h1 := Units.ne_zero (T.refinedLeviHalfModulus B Q (flattenedLeviEquiv F.Carrier B Q r.val))
  have h2 := Units.ne_zero (T.refinedLeviHalfModulus B Q (flattenedLeviEquiv F.Carrier B Q m))
  field_simp

/-- A direct stabilizer pulls back through conjugation and the refined Levi
section; intersecting the half-modulus kernel also fixes the inverse scalar. -/
private theorem inverseValue_smooth (f : Direct T B Q R ωB) (g : B.Levi F.Carrier) :
    letI := T.topology
    ∃ K : OpenSubgroup ((B.flatten Q).Levi F.Carrier), ∀ (k : K) (m : (B.flatten Q).Levi F.Carrier),
      inverseValue T B Q R ωB f g (m * k.val) = inverseValue T B Q R ωB f g m := by
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.leviTopologicalGroup B
  obtain ⟨K, hK⟩ := f.property
  let e := flattenedLeviEquivContinuous F.Carrier B Q
  let c : (B.flatten Q).Levi F.Carrier →* B.Levi F.Carrier := {
    toFun := fun m => g⁻¹ * (flattenedLeviEquiv F.Carrier B Q m).val * g
    map_one' := by simp
    map_mul' := by intro a b; simp [map_mul, mul_assoc] }
  have hc : Continuous c :=
    (continuous_const.mul (continuous_subtype_val.comp e.continuous)).mul_const g
  let H : OpenSubgroup (refinedLevi F.Carrier B Q) :=
    ⟨(T.refinedLeviHalfModulus B Q).ker, T.isOpen_ker_refinedLeviHalfModulus B Q⟩
  refine ⟨K.comap c hc ⊓ H.comap e.toMulEquiv.toMonoidHom e.continuous, ?_⟩
  intro k m
  have hk : c k.val ∈ K := k.property.1
  have hχ : T.refinedLeviHalfModulus B Q (flattenedLeviEquiv F.Carrier B Q k.val) = 1 :=
    k.property.2
  have hf := congrArg (fun h : Induction.EquivariantFunctions _ _ =>
    h.val ((flattenedLeviEquiv F.Carrier B Q m).val * g)) (hK ⟨c k.val, hk⟩)
  change f.val.val (((flattenedLeviEquiv F.Carrier B Q m).val * g) *
    (g⁻¹ * (flattenedLeviEquiv F.Carrier B Q k.val).val * g)) = _ at hf
  simp only [mul_assoc, mul_inv_cancel_left] at hf
  simp only [inverseValue, map_mul, hχ, mul_one, Subgroup.coe_mul]
  rw [mul_assoc, hf]

include hω in
private def inverseInner (f : Direct T B Q R ωB) (g : B.Levi F.Carrier) : Mid T B Q R ω := by
  letI := T.topology
  letI := T.leviTopologicalGroup (B.flatten Q)
  let K := Classical.choose (inverseValue_smooth T B Q R ωB f g)
  exact Induction.smoothFunctionOf _ _ (inverseValue T B Q R ωB f g)
    (inverseValue_cov T B Q R ω ωB hω f g) K
    (Classical.choose_spec (inverseValue_smooth T B Q R ωB f g))

/-- Outer covariance of the inverse values, through the middle Levi part. -/
private theorem inverseValue_outer (f : Direct T B Q R ωB)
    (q : refinedParabolic F.Carrier B Q) (g : B.Levi F.Carrier)
    (m : (B.flatten Q).Levi F.Carrier) :
    inverseValue T B Q R ωB f (q.val * g) m =
      (T.refinedLeviHalfModulus B Q (refinedLeviProjection F.Carrier B Q q) : ℂ) •
        inverseValue T B Q R ωB f g
          (m * (flattenedLeviEquiv F.Carrier B Q).symm (refinedLeviProjection F.Carrier B Q q)) := by
  let y : refinedParabolic F.Carrier B Q :=
    refinedLeviSection F.Carrier B Q (flattenedLeviEquiv F.Carrier B Q m) * q
  have h := direct_projQ T B Q R ωB f y g
  have hp : refinedLeviProjection F.Carrier B Q y =
      flattenedLeviEquiv F.Carrier B Q
        (m * (flattenedLeviEquiv F.Carrier B Q).symm (refinedLeviProjection F.Carrier B Q q)) := by
    simp only [y, map_mul, refinedLeviProjection_section, MulEquiv.apply_symm_apply]
  rw [hp] at h
  change f.val.val (((flattenedLeviEquiv F.Carrier B Q m).val * q.val) * g) = _ at h
  rw [mul_assoc] at h
  unfold inverseValue
  rw [h, map_mul (flattenedLeviEquiv F.Carrier B Q), MulEquiv.apply_symm_apply,
    map_mul (T.refinedLeviHalfModulus B Q), Units.val_mul, smul_smul]
  congr 1
  have h1 := Units.ne_zero (T.refinedLeviHalfModulus B Q (flattenedLeviEquiv F.Carrier B Q m))
  have h2 := Units.ne_zero (T.refinedLeviHalfModulus B Q (refinedLeviProjection F.Carrier B Q q))
  field_simp

include hω in
private def inverse (f : Direct T B Q R ωB) : Iter T B Q R ω := by
  letI := T.topology
  letI := T.leviTopologicalGroup B
  letI := T.leviTopologicalGroup (B.flatten Q)
  let K := Classical.choose f.property
  have hK := Classical.choose_spec f.property
  refine Induction.smoothFunctionOf _ _ (inverseInner T B Q R ω ωB hω f) ?_ K ?_
  · intro q g
    apply Subtype.ext
    apply Subtype.ext
    funext m
    exact inverseValue_outer T B Q R ωB f q g m
  · intro k g
    apply Subtype.ext
    apply Subtype.ext
    funext m
    change inverseValue T B Q R ωB f (g * k.val) m = inverseValue T B Q R ωB f g m
    have hf := congrArg (fun h : Induction.EquivariantFunctions _ _ =>
      h.val ((flattenedLeviEquiv F.Carrier B Q m).val * g)) (hK k)
    change f.val.val (((flattenedLeviEquiv F.Carrier B Q m).val * g) * k.val) = _ at hf
    unfold inverseValue
    rw [← mul_assoc, hf]

/-- Scalar bookkeeping for `iter_section`, with a free middle function. -/
private theorem section_scalar (φ : (B.flatten Q).Levi F.Carrier → V)
    (m : (B.flatten Q).Levi F.Carrier)
    (hq : (flattenedLeviEquiv F.Carrier B Q m).val ∈ refinedParabolic F.Carrier B Q) :
    (T.refinedLeviHalfModulus B Q (refinedLeviProjection F.Carrier B Q ⟨_, hq⟩) : ℂ) •
      φ ((flattenedLeviEquiv F.Carrier B Q).symm (refinedLeviProjection F.Carrier B Q ⟨_, hq⟩)) =
      (T.refinedLeviHalfModulus B Q (flattenedLeviEquiv F.Carrier B Q m) : ℂ) • φ m := by
  have hp : refinedLeviProjection F.Carrier B Q ⟨_, hq⟩ = flattenedLeviEquiv F.Carrier B Q m :=
    refinedLeviProjection_section F.Carrier B Q _
  rw [hp, MulEquiv.symm_apply_apply]

private theorem iter_section (f : Iter T B Q R ω) (m : (B.flatten Q).Levi F.Carrier)
    (g : B.Levi F.Carrier) :
    (f.val.val ((flattenedLeviEquiv F.Carrier B Q m).val * g)).val.val 1 =
      (T.refinedLeviHalfModulus B Q (flattenedLeviEquiv F.Carrier B Q m) : ℂ) •
        (f.val.val g).val.val m := by
  have hq : (flattenedLeviEquiv F.Carrier B Q m).val ∈ refinedParabolic F.Carrier B Q :=
    (refinedLeviSection F.Carrier B Q (flattenedLeviEquiv F.Carrier B Q m)).property
  exact (iter_cov_one T B Q R ω f _ hq g).trans
    (section_scalar T B Q (V := V) (f.val.val g).val.val m hq)

include hω in
private theorem forward_inverse (f : Direct T B Q R ωB) :
    forward T B Q R ω ωB hω (inverse T B Q R ω ωB hω f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change (T.refinedLeviHalfModulus B Q (flattenedLeviEquiv F.Carrier B Q 1) : ℂ)⁻¹ •
    f.val.val ((flattenedLeviEquiv F.Carrier B Q 1).val * g) = f.val.val g
  simp only [map_one, Units.val_one, inv_one, one_mul, one_smul, OneMemClass.coe_one]

include hω in
private theorem inverse_forward (f : Iter T B Q R ω) :
    inverse T B Q R ω ωB hω (forward T B Q R ω ωB hω f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply Subtype.ext
  apply Subtype.ext
  funext m
  exact (inv_smul_eq_iff₀ (Units.ne_zero _)).mpr (iter_section T B Q R ω f m g)

include hω in
/-- The constructed comparison of the iterated and direct smooth parts. -/
private def comparisonEquiv :
    letI := T.topology
    (RelativeRegularComparison.middleInduced T B Q
        (RelativeRegularComparison.middleInduced T (B.flatten Q) R (Rep.of ω))).ρ.Equiv
      (RelativeRegularComparison.middleInduced T B (B.composeRefinement Q R) (Rep.of ωB)).ρ := by
  letI := T.topology
  letI := T.leviTopologicalGroup B
  exact {
    toLinearEquiv := {
      toFun := forward T B Q R ω ωB hω
      invFun := inverse T B Q R ω ωB hω
      left_inv := inverse_forward T B Q R ω ωB hω
      right_inv := forward_inverse T B Q R ω ωB hω
      map_add' := by
        intro f h
        apply Subtype.ext
        apply Subtype.ext
        funext g
        rfl
      map_smul' := by
        intro c f
        apply Subtype.ext
        apply Subtype.ext
        funext g
        rfl }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      apply Subtype.ext
      funext x
      rfl }

end Comparison

/-- The comparison clause: evaluation at the middle identity is an equivalence
from the iterated induction to the direct induction. -/
theorem comparison : NestedInduction.Comparison.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n B Q D R V _ _ ω S h ωB A C
  refine ⟨comparisonEquiv T B Q R ω ωB (cast_apply F.Carrier h ω), ?_, ?_⟩
  · intro f g
    rfl
  · intro f g m
    rfl

section Quotient

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n)

/-- A refined parabolic is closed in the product Levi. -/
theorem isClosed_refinedParabolic (Q : BlockRefinement B) :
    letI := T.topology
    IsClosed (refinedParabolic F.Carrier B Q : Set (B.Levi F.Carrier)) := by
  let := T.topology
  let := T.fieldT2
  rw [refinedParabolic, Subgroup.coe_pi]
  exact isClosed_set_pi fun i _ => (Q i).isClosed_parabolic F.Carrier

/-- Normalized refined induction carries surjections of smooth representations
to surjections. -/
theorem normalizedRefinedInducedMap_surjective (Q : BlockRefinement B)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (refinedLevi F.Carrier B Q) V}
    {τ : Representation ℂ (refinedLevi F.Carrier B Q) W} (f : σ.IntertwiningMap τ)
    (hσ : letI := T.topology; IsSmooth σ) (hτ : letI := T.topology; IsSmooth τ)
    (hf : Function.Surjective f) :
    Function.Surjective (T.normalizedRefinedInducedMap B Q f) := by
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.fieldT2
  let := T.leviTopologicalGroup B
  let := T.leviT2Space B
  refine Induction.smoothInductionSurjectivity.{uF, uV, uW} (B.Levi F.Carrier) ?_
    (refinedParabolic F.Carrier B Q) (isClosed_refinedParabolic T B Q) V W _ _ ?_ ?_
    (refinedInducingMap B Q (T.refinedLeviHalfModulus B Q) f) hf
  · intro K
    let L := T.leviCompactOpen B K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L.1, L.2.1, L.2.2⟩
  · exact (isSmooth_twist_iff _ _ (T.isOpen_ker_refinedParabolicHalfModulus B Q)).2
      (isSmooth_comp _ (refinedLeviProjectionContinuous F.Carrier B Q).continuous hσ)
  · exact (isSmooth_twist_iff _ _ (T.isOpen_ker_refinedParabolicHalfModulus B Q)).2
      (isSmooth_comp _ (refinedLeviProjectionContinuous F.Carrier B Q).continuous hτ)

/-- Transport of the fine twisted input along an equality of fine shapes. -/
theorem fineTwist_transport (S : BlockRefinement B) {X : BlockShape n} (h : X = B.flatten S)
    (ω : Rep.{uV} ℂ (X.Levi F.Carrier)) (v₀ : Fin X.length → ℝ)
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (q : (RelativeRegularComparison.middleInduced T B S
      (Rep.of (h ▸ T.leviRealPowerTwist X (fun k => -v₀ k + 0) ω.ρ :
        Representation ℂ ((B.flatten S).Levi F.Carrier) ω.V))).ρ.IntertwiningMap π.ρ)
    (hq : Function.Surjective q) :
    ∃ q' : (RelativeJacquetMultiplicity.innerInduced T B S
      (RelativeJacquetMultiplicity.fineTwist T B S (h ▸ ω) (h ▸ v₀) 0)).ρ.IntertwiningMap π.ρ,
      Function.Surjective q' := by
  subst h
  exact ⟨q, hq⟩

end Quotient

/-- The quotient-transport clause. -/
theorem quotientTransport : NestedInduction.QuotientTransport.{uF, uV, uM, uW} := by
  intro p _ F T
  let := T.topology
  intro n B Q D R ω v₀ σ π qFM qMC hFM hMC S h
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.leviTopologicalGroup B
  let := T.leviTopologicalGroup D
  let ω'' : Representation ℂ ((D.flatten R).Levi F.Carrier) ω.V :=
    T.leviRealPowerTwist (D.flatten R) (fun k => -v₀ k + 0) ω.ρ
  let M := RelativeRegularComparison.middleInduced T D R (Rep.of ω'')
  let q1 : M.ρ.IntertwiningMap σ.ρ := qFM
  let e := (flattenedLeviEquiv F.Carrier B Q).symm.toMonoidHom
  let q2 : Representation.IntertwiningMap (M.ρ.comp e) (σ.ρ.comp e) :=
    { toLinearMap := q1.toLinearMap
      isIntertwining' := fun x => q1.isIntertwining' (e x) }
  have hM : IsSmooth M.ρ := T.isSmooth_normalizedRefinedInduced D R _
  have hσ : IsSmooth σ.ρ := isSmooth_of_surjective q1 hFM hM
  have he : Continuous e := (flattenedLeviEquivContinuous F.Carrier B Q).symm.continuous
  have hq3 := normalizedRefinedInducedMap_surjective T B Q q2 (isSmooth_comp e he hM)
    (isSmooth_comp e he hσ) hFM
  let q3 : (RelativeRegularComparison.middleInduced T B Q M).ρ.IntertwiningMap
      (RelativeRegularComparison.middleInduced T B Q σ).ρ :=
    T.normalizedRefinedInducedMap B Q q2
  let E := comparisonEquiv T B Q R ω'' (h ▸ ω'') (cast_apply F.Carrier h ω'')
  let q4 := qMC.comp (q3.comp E.symm.toIntertwiningMap)
  -- The explicit composite keeps the transported terms syntactically equal to the goal's.
  refine fineTwist_transport T B (B.composeRefinement Q R) h ω v₀ π q4 ?_
  intro y
  obtain ⟨x, rfl⟩ := hMC y
  obtain ⟨z, rfl⟩ := hq3 x
  exact ⟨E z, congrArg (fun w => qMC (q3 w)) (E.symm_apply_apply z)⟩

end NestedInductionProof

/-- Normalized induction in stages inside a product Levi, with its quotient
transport consequence. -/
theorem normalizedNestedInduction : NormalizedNestedInductionStatement.{uF, uV, uM, uW} :=
  ⟨NestedInductionProof.comparison, NestedInductionProof.quotientTransport⟩

end Langlands
