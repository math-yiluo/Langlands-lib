import Langlands.Representation.Jacquet.BlockCompressionProof
import Langlands.AllField.Representation.Jacquet.BlockCompressionStatement
/-! # Normalized block compression laws from finite orbit means -/

namespace Langlands.AllField.Jacquet
open Langlands.Jacquet hiding BlockCompressionStatement blockCompressedAction_mk blockCompressedAction_mul blockCompression
open Langlands.AllField.Jacquet

open scoped BigOperators

universe uG uF uV uW

section Averaging

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

private theorem average_apply_subgroup (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (k : K) (v : V) :
    Compact.averageMap ρ hρ K hK (ρ k.val v) = Compact.averageMap ρ hρ K hK v := by
  let τ := ρ.comp K.toSubgroup.subtype
  have ho : Compact.orbit τ (τ k v) = Compact.orbit τ v := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h * k, by simp⟩
    · rintro ⟨h, rfl⟩
      refine ⟨h * k⁻¹, ?_⟩
      simp [map_mul, Module.End.mul_apply]
  change Compact.orbitMean τ (τ k v) = Compact.orbitMean τ v
  unfold Compact.orbitMean
  rw [ho]

end Averaging

/-- The two normalized compression laws, with exactly the published telescope. -/
theorem blockCompression : BlockCompressionStatement.{uF, uV} := by
  intro F _ T n B
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ K hK hfac
  have hcomm (a : Fin B.length → Fˣ)
      (m : B.iwahoriLevi F K.toSubgroup) :
      B.blockScalar F a * m.val = m.val * B.blockScalar F a := by
    obtain ⟨m', hm'⟩ := m.property.2
    rw [← hm']
    exact (map_mul (B.leviEmbedding F) _ _).symm.trans
      ((congrArg (B.leviEmbedding F) (B.blockScalarLevi_commute F a m')).trans
        (map_mul (B.leviEmbedding F) _ _))
  have hlow (a : Fin B.length → Fˣ) (ha : (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T a)
      (v : fixedVectors ρ K.toSubgroup)
      (l : B.iwahoriLower F K.toSubgroup) :
      ρ l.val (ρ (B.blockScalar F a) v.val) =
        ρ (B.blockScalar F a) v.val := by
    have hl := (hfac.2 a ha).2 l.val l.property
    calc
      _ = ρ (B.blockScalar F a)
          (ρ ((B.blockScalar F a)⁻¹ * l.val * B.blockScalar F a) v.val) := by
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        congr 1
        group
      _ = _ := congrArg (ρ (B.blockScalar F a)) (v.property ⟨_, hl.1⟩)
  have hmid (a : Fin B.length → Fˣ)
      (v : fixedVectors ρ K.toSubgroup)
      (m : B.iwahoriLevi F K.toSubgroup) :
      ρ m.val (ρ (B.blockScalar F a) v.val) =
        ρ (B.blockScalar F a) v.val := by
    calc
      _ = ρ (B.blockScalar F a) (ρ m.val v.val) := by
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        rw [hcomm a m]
      _ = _ := congrArg (ρ (B.blockScalar F a)) (v.property ⟨_, m.property.1⟩)
  have horbit (a : Fin B.length → Fˣ) (ha : (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T a)
      (v : fixedVectors ρ K.toSubgroup) (k : K) :
      ∃ u : B.iwahoriUpper F K.toSubgroup,
        ρ k.val (ρ (B.blockScalar F a) v.val) =
          ρ u.val (ρ (B.blockScalar F a) v.val) := by
    obtain ⟨⟨l, m, u⟩, hprod⟩ := hfac.1.2 k⁻¹
    have heq : k.val = u.val⁻¹ * m.val⁻¹ * l.val⁻¹ := by
      have hi := congrArg (fun x : K => x.val⁻¹) hprod
      simpa only [GeneralLinear.BlockShape.iwahoriProduct_val,
        InvMemClass.coe_inv, inv_inv, mul_inv_rev, mul_assoc] using hi.symm
    refine ⟨u⁻¹, ?_⟩
    rw [heq]
    simp only [map_mul, Module.End.mul_apply, InvMemClass.coe_inv]
    have hl := hlow a ha v l⁻¹
    have hm := hmid a v m⁻¹
    simp only [InvMemClass.coe_inv] at hl hm
    rw [hl, hm]
  constructor
  · intro a b ha hb
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change Compact.averageMap ρ hρ K hK (ρ (B.blockScalar F (a * b)) v.val) =
      Compact.averageMap ρ hρ K hK (ρ (B.blockScalar F a)
        (Compact.averageMap ρ hρ K hK (ρ (B.blockScalar F b) v.val)))
    rw [B.blockScalar_mul, map_mul, Module.End.mul_apply]
    symm
    apply map_averageMap_of_forall_eq ρ hρ K hK
      ((Compact.averageMap ρ hρ K hK).comp (ρ (B.blockScalar F a)))
      (ρ (B.blockScalar F b) v.val)
    intro k
    change Compact.averageMap ρ hρ K hK
      (ρ (B.blockScalar F a) (ρ k.val (ρ (B.blockScalar F b) v.val))) = _
    obtain ⟨u, hu⟩ := horbit b hb v k
    rw [hu]
    have huK := (hfac.2 a ha).1 u.val u.property
    calc
      _ = Compact.averageMap ρ hρ K hK
          (ρ (B.blockScalar F a * u.val * (B.blockScalar F a)⁻¹)
            (ρ (B.blockScalar F a) (ρ (B.blockScalar F b) v.val))) := by
        congr 1
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        congr 1
        group
      _ = _ := average_apply_subgroup ρ hρ K hK ⟨_, huK.1⟩ _
  · intro a ha v
    rw [action_mk]
    change mk ρ (B.unipotentSubgroup F)
        (Compact.averageMap ρ hρ K hK (ρ (B.blockScalar F a) v.val)) =
      mk ρ (B.unipotentSubgroup F) (ρ (B.blockScalar F a) v.val)
    apply map_averageMap_of_forall_eq
    intro k
    obtain ⟨u, hu⟩ := horbit a ha v k
    rw [hu]
    exact mk_apply_subgroup ρ (B.unipotentSubgroup F) ⟨_, u.property.2⟩ _

/-- Multiplicativity of the actual normalized compressed actions in the weak chamber. -/
theorem blockCompressedAction_mul (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F))
      (hK : IsCompact (K : Set (GeneralLinear n F))),
      (Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization B) T K →
      ∀ a b : Fin B.length → Fˣ,
        (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T a → (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T b →
          compressedAction ρ hρ K hK (B.blockScalar F (a * b)) =
            compressedAction ρ hρ K hK (B.blockScalar F a) *
              compressedAction ρ hρ K hK (B.blockScalar F b) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ K hK hfac
  exact (blockCompression F T n B V ρ hρ K hK hfac).1

/-- Compression intertwines the actual quotient with the unnormalized Levi action. -/
theorem blockCompressedAction_mk (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F))
      (hK : IsCompact (K : Set (GeneralLinear n F))),
      (Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization B) T K →
      ∀ a : Fin B.length → Fˣ, (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T a →
        ∀ v : fixedVectors ρ K.toSubgroup,
          mk ρ (B.unipotentSubgroup F)
              (compressedAction ρ hρ K hK (B.blockScalar F a) v : V) =
            action ρ (B.unipotentSubgroup F) (B.leviSubgroup F)
              (B.leviSubgroup_le_normalizer_unipotentSubgroup F)
              (B.blockScalarInLevi F a)
              (mk ρ (B.unipotentSubgroup F) (v : V)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ K hK hfac
  exact (blockCompression F T n B V ρ hρ K hK hfac).2

end Langlands.AllField.Jacquet
