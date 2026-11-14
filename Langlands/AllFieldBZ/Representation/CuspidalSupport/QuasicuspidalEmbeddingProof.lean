import Langlands.AllFieldBZ.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement
import Langlands.AllFieldBZ.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem IrreducibleQuasicuspidalLeviAdmissibilityTheorem MinimalNonzeroJacquetTheorem NormalizedQuasicuspidalEmbeddingTheorem ZeroRankCuspidalEmbeddingTheorem minimalNonzeroJacquet normalizedQuasicuspidalEmbedding normalizedQuasicuspidalEmbedding_of
open Langlands.GeneralLinear
universe uF uV uW uG

namespace QuasicuspidalEmbedding
open Langlands.CuspidalSupport.QuasicuspidalEmbedding hiding exists_finset_generating inducedMap inducedMap_eval_one inducingRepresentation jacquetMk_parabolic orbitMap
section Lattice
variable {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Lattice
section Jacquet
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
variable {n : ℕ} (B : BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The parabolic acts on the actual Jacquet quotient through its Levi
projection, with the positive half modulus restoring the normalization. -/
theorem jacquetMk_parabolic (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (g : B.parabolic F.Carrier) (v : V) :
    B.jacquetMk ρ (ρ g v) =
      ((T.parabolicHalfModulus B g : ℂˣ) : ℂ) •
        T.normalizedJacquet B ρ (B.leviProjection F.Carrier g) (B.jacquetMk ρ v) := by
  rw [T.normalizedJacquet_mk_eq_inv_halfModulus, T.parabolicHalfModulus_apply, Units.smul_def,
    smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let u := B.unipotentPart F.Carrier g
  have hg : (g : GeneralLinear n F.Carrier) =
      ((u : B.parabolic F.Carrier) : GeneralLinear n F.Carrier) *
        B.leviEmbedding F.Carrier (B.leviProjection F.Carrier g) := by
    change (g : GeneralLinear n F.Carrier) =
      ((g * (B.leviInParabolic F.Carrier (B.leviProjection F.Carrier g))⁻¹ *
        B.leviInParabolic F.Carrier (B.leviProjection F.Carrier g) :
          B.parabolic F.Carrier) : GeneralLinear n F.Carrier)
    rw [inv_mul_cancel_right]
  rw [hg, map_mul, Module.End.mul_apply]
  exact Jacquet.mk_apply_subgroup (ρ.comp (B.parabolic F.Carrier).subtype)
    (B.unipotentRadical F.Carrier) u _

/-- The inducing representation of the normalized parabolic induction. -/
abbrev inducingRepresentation (σ : Representation ℂ (B.Levi F.Carrier) W) :
    Representation ℂ (B.parabolic F.Carrier) W :=
  twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))

/-- The orbit functions `g ↦ f (r_P (ρ g v))`, before restriction to smooth
vectors. -/
def orbitMap (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (B.Levi F.Carrier) W)
    (f : (T.normalizedJacquet B ρ).IntertwiningMap σ) :
    ρ.IntertwiningMap (Representation.coind (B.parabolic F.Carrier).subtype
      (inducingRepresentation T B σ)) where
  toLinearMap :=
    { toFun := fun v => ⟨fun g => f (B.jacquetMk ρ (ρ g v)), by
        intro q g
        change f (B.jacquetMk ρ (ρ ((q : GeneralLinear n F.Carrier) * g) v)) =
          ((T.parabolicHalfModulus B q : ℂˣ) : ℂ) •
            σ (B.leviProjection F.Carrier q) (f (B.jacquetMk ρ (ρ g v)))
        rw [map_mul, Module.End.mul_apply, jacquetMk_parabolic T B ρ q, map_smul,
          Representation.IntertwiningMap.isIntertwining]⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        funext g
        change f (B.jacquetMk ρ (ρ g (v + w))) =
          f (B.jacquetMk ρ (ρ g v)) + f (B.jacquetMk ρ (ρ g w))
        rw [map_add, map_add, map_add]
      map_smul' := by
        intro c v
        apply Subtype.ext
        funext g
        change f (B.jacquetMk ρ (ρ g (c • v))) = c • f (B.jacquetMk ρ (ρ g v))
        rw [map_smul, map_smul, map_smul] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    change f (B.jacquetMk ρ (ρ x (ρ g v))) = f (B.jacquetMk ρ (ρ (x * g) v))
    rw [map_mul, Module.End.mul_apply]

variable [TopologicalSpace (GeneralLinear n F.Carrier)]
  [IsTopologicalGroup (GeneralLinear n F.Carrier)]

/-- Backward Frobenius reciprocity: a Levi intertwiner out of the normalized
Jacquet module gives an intertwiner into normalized smooth induction. -/
def inducedMap {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} (hρ : IsSmooth ρ)
    (σ : Representation ℂ (B.Levi F.Carrier) W)
    (f : (T.normalizedJacquet B ρ).IntertwiningMap σ) :
    ρ.IntertwiningMap (Induction.smoothInduced (B.parabolic F.Carrier)
      (inducingRepresentation T B σ)) :=
  smoothLift hρ (orbitMap T B ρ σ f)

theorem inducedMap_eval_one {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    (hρ : IsSmooth ρ) (σ : Representation ℂ (B.Levi F.Carrier) W)
    (f : (T.normalizedJacquet B ρ).IntertwiningMap σ) (v : V) :
    Induction.eval (B.parabolic F.Carrier) (inducingRepresentation T B σ)
      (inducedMap T B hρ σ f v) 1 = f (B.jacquetMk ρ v) := by
  change f (B.jacquetMk ρ (ρ 1 v)) = f (B.jacquetMk ρ v)
  rw [map_one, Module.End.one_apply]

/-- With compact `P \ G`, the normalized Jacquet module of a representation
generated by one smooth vector is generated by finitely many vectors. -/
theorem exists_finset_generating
    [CompactSpace (Induction.LeftQuotient (B.parabolic F.Carrier))]
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} (hρ : IsSmooth ρ) (v₀ : V)
    (hgen : ∀ v : V, v ∈ Submodule.span ℂ (Set.range fun g => ρ g v₀)) :
    ∃ s : Finset (B.JacquetModule ρ),
      ∀ S : Subrepresentation (T.normalizedJacquet B ρ), (∀ x ∈ s, x ∈ S) → S = ⊤ := by
  obtain ⟨K, hK⟩ := hρ v₀
  obtain ⟨t, ht⟩ := Induction.exists_finset_doubleCoset_cover (B.parabolic F.Carrier) K
  classical
  refine ⟨t.image fun i => B.jacquetMk ρ (ρ i v₀), ?_⟩
  intro S hS
  have hmem : ∀ g : GeneralLinear n F.Carrier, B.jacquetMk ρ (ρ g v₀) ∈ S := by
    intro g
    obtain ⟨i, hi, q, hq, k, hk, rfl⟩ := ht g
    have hk' : ρ k v₀ = v₀ := hK ⟨k, hk⟩
    have hiS : B.jacquetMk ρ (ρ i v₀) ∈ S :=
      hS _ (Finset.mem_image_of_mem _ hi)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hk']
    have h := jacquetMk_parabolic T B ρ ⟨q, hq⟩ (ρ i v₀)
    change B.jacquetMk ρ (ρ q (ρ i v₀)) = _ at h
    rw [h]
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ hiS)
  have hle : Submodule.span ℂ (Set.range fun g => ρ g v₀) ≤
      S.toSubmodule.comap (B.jacquetMk ρ) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hmem g
  apply SetLike.ext
  intro x
  refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
  exact hle (hgen v)

end Jacquet
section Irreducible
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Irreducible
end QuasicuspidalEmbedding
open Langlands.CuspidalSupport.QuasicuspidalEmbedding hiding exists_finset_generating inducedMap inducedMap_eval_one inducingRepresentation jacquetMk_parabolic orbitMap
variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

/-- The positive-rank embedding, assuming nonzero quasicuspidal Jacquet descent. -/
theorem normalizedQuasicuspidalEmbedding_of
    (hMin : MinimalNonzeroJacquetTheorem.{uF, uV})
    (n : ℕ) : NormalizedQuasicuspidalEmbeddingTheorem.{uF, uV} F T n := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro _ ω hω
  have hωne : Nontrivial ω := nontrivial_of_isIrreducible ω.representation hω
  obtain ⟨B, hJne, hJq⟩ := hMin F T n ω hωne
  let J := (T.normalizedJacquetFunctor B).obj ω
  have : CompactSpace (Induction.LeftQuotient (B.parabolic F.Carrier)) :=
    Parabolic.parabolicQuotientCompact F T B
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : ω)
  obtain ⟨s, hs⟩ := Langlands.AllFieldBZ.CuspidalSupport.QuasicuspidalEmbedding.exists_finset_generating T B ω.isSmooth v₀
    (mem_span_orbit ω.representation hω hv₀)
  have : Nontrivial J := hJne
  obtain ⟨S, hS⟩ := exists_isCoatom_subrepresentation J.representation s hs
  let σ := SmoothRep.quotient J S
  let q : J.representation.IntertwiningMap σ.representation := SmoothRep.hom (SmoothRep.mkQ J S)
  have hq : Function.Surjective q := SmoothRep.mkQ_surjective J S
  have hqker : ∀ x, q x = 0 ↔ x ∈ S := fun x => Submodule.Quotient.mk_eq_zero _
  have hσ : σ.IsIrreducible := isIrreducible_of_isCoatom q hq S hS hqker
  have hσq : IsLeviQuasicuspidal B σ.representation := fun R hR =>
    coinvariants_subsingleton_of_surjective q hq _ (hJq R hR)
  let j := Langlands.AllFieldBZ.CuspidalSupport.QuasicuspidalEmbedding.inducedMap T B ω.isSmooth σ.representation q
  refine ⟨B, σ, hσ, hσq, j, ?_⟩
  have : Representation.IsIrreducible ω.representation := hω
  rcases Representation.IsIrreducible.injective_or_eq_zero j with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx⟩ : ∃ x, x ∉ S := by
      by_contra hall
      push Not at hall
      apply hS.1
      apply SetLike.ext
      intro x
      exact ⟨fun _ => Submodule.mem_top, fun _ => hall x⟩
    obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ω.representation x
    have h1 := Langlands.AllFieldBZ.CuspidalSupport.QuasicuspidalEmbedding.inducedMap_eval_one T B ω.isSmooth σ.representation q v
    change Induction.eval _ _ (j v) 1 = _ at h1
    rw [h] at h1
    have h0 : q (B.jacquetMk ω.representation v) = 0 := h1.symm.trans rfl
    exact hx ((hqker _).mp h0)

/-- The positive-rank quasicuspidal embedding into normalized induction. -/
theorem normalizedQuasicuspidalEmbedding (n : ℕ) :
    NormalizedQuasicuspidalEmbeddingTheorem.{uF, uV} F T n :=
  normalizedQuasicuspidalEmbedding_of F T minimalNonzeroJacquet n

end Langlands.AllFieldBZ.CuspidalSupport
