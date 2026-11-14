import Langlands.AllFieldBZ.Representation.Jacquet.BlockCompressionStatement
import Langlands.Representation.Jacquet.BlockCompressionProof

/-!
# All-field port of `Langlands.Representation.Jacquet.BlockCompressionProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Jacquet.BlockCompressionProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Jacquet
open Langlands.Jacquet hiding BlockCompressionStatement blockCompressedAction_mk blockCompressedAction_mul blockCompression
open scoped BigOperators
universe uG uF uV uW

section Averaging
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

private theorem _root_.Langlands.Jacquet.average_apply_subgroup (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
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
  intro F T n B
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ K hK hfac
  have hcomm (a : Fin B.length → F.Carrierˣ)
      (m : B.iwahoriLevi F.Carrier K.toSubgroup) :
      B.blockScalar F.Carrier a * m.val = m.val * B.blockScalar F.Carrier a := by
    obtain ⟨m', hm'⟩ := m.property.2
    rw [← hm']
    exact (map_mul (B.leviEmbedding F.Carrier) _ _).symm.trans
      ((congrArg (B.leviEmbedding F.Carrier) (B.blockScalarLevi_commute F.Carrier a m')).trans
        (map_mul (B.leviEmbedding F.Carrier) _ _))
  have hlow (a : Fin B.length → F.Carrierˣ) (ha : B.IsWeaklyContracting_allFieldBZ T a)
      (v : fixedVectors ρ K.toSubgroup)
      (l : B.iwahoriLower F.Carrier K.toSubgroup) :
      ρ l.val (ρ (B.blockScalar F.Carrier a) v.val) =
        ρ (B.blockScalar F.Carrier a) v.val := by
    have hl := (hfac.2 a ha).2 l.val l.property
    calc
      _ = ρ (B.blockScalar F.Carrier a)
          (ρ ((B.blockScalar F.Carrier a)⁻¹ * l.val * B.blockScalar F.Carrier a) v.val) := by
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        congr 1
        group
      _ = _ := congrArg (ρ (B.blockScalar F.Carrier a)) (v.property ⟨_, hl.1⟩)
  have hmid (a : Fin B.length → F.Carrierˣ)
      (v : fixedVectors ρ K.toSubgroup)
      (m : B.iwahoriLevi F.Carrier K.toSubgroup) :
      ρ m.val (ρ (B.blockScalar F.Carrier a) v.val) =
        ρ (B.blockScalar F.Carrier a) v.val := by
    calc
      _ = ρ (B.blockScalar F.Carrier a) (ρ m.val v.val) := by
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        rw [hcomm a m]
      _ = _ := congrArg (ρ (B.blockScalar F.Carrier a)) (v.property ⟨_, m.property.1⟩)
  have horbit (a : Fin B.length → F.Carrierˣ) (ha : B.IsWeaklyContracting_allFieldBZ T a)
      (v : fixedVectors ρ K.toSubgroup) (k : K) :
      ∃ u : B.iwahoriUpper F.Carrier K.toSubgroup,
        ρ k.val (ρ (B.blockScalar F.Carrier a) v.val) =
          ρ u.val (ρ (B.blockScalar F.Carrier a) v.val) := by
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
    change Compact.averageMap ρ hρ K hK (ρ (B.blockScalar F.Carrier (a * b)) v.val) =
      Compact.averageMap ρ hρ K hK (ρ (B.blockScalar F.Carrier a)
        (Compact.averageMap ρ hρ K hK (ρ (B.blockScalar F.Carrier b) v.val)))
    rw [B.blockScalar_mul, map_mul, Module.End.mul_apply]
    symm
    apply map_averageMap_of_forall_eq ρ hρ K hK
      ((Compact.averageMap ρ hρ K hK).comp (ρ (B.blockScalar F.Carrier a)))
      (ρ (B.blockScalar F.Carrier b) v.val)
    intro k
    change Compact.averageMap ρ hρ K hK
      (ρ (B.blockScalar F.Carrier a) (ρ k.val (ρ (B.blockScalar F.Carrier b) v.val))) = _
    obtain ⟨u, hu⟩ := horbit b hb v k
    rw [hu]
    have huK := (hfac.2 a ha).1 u.val u.property
    calc
      _ = Compact.averageMap ρ hρ K hK
          (ρ (B.blockScalar F.Carrier a * u.val * (B.blockScalar F.Carrier a)⁻¹)
            (ρ (B.blockScalar F.Carrier a) (ρ (B.blockScalar F.Carrier b) v.val))) := by
        congr 1
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        congr 1
        group
      _ = _ := average_apply_subgroup ρ hρ K hK ⟨_, huK.1⟩ _
  · intro a ha v
    rw [action_mk]
    change mk ρ (B.unipotentSubgroup F.Carrier)
        (Compact.averageMap ρ hρ K hK (ρ (B.blockScalar F.Carrier a) v.val)) =
      mk ρ (B.unipotentSubgroup F.Carrier) (ρ (B.blockScalar F.Carrier a) v.val)
    apply map_averageMap_of_forall_eq
    intro k
    obtain ⟨u, hu⟩ := horbit a ha v k
    rw [hu]
    exact mk_apply_subgroup ρ (B.unipotentSubgroup F.Carrier) ⟨_, u.property.2⟩ _

/-- Multiplicativity of the actual normalized compressed actions in the weak chamber. -/
theorem blockCompressedAction_mul (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization_allFieldBZ T K →
      ∀ a b : Fin B.length → F.Carrierˣ,
        B.IsWeaklyContracting_allFieldBZ T a → B.IsWeaklyContracting_allFieldBZ T b →
          compressedAction ρ hρ K hK (B.blockScalar F.Carrier (a * b)) =
            compressedAction ρ hρ K hK (B.blockScalar F.Carrier a) *
              compressedAction ρ hρ K hK (B.blockScalar F.Carrier b) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ K hK hfac
  exact (blockCompression F T n B V ρ hρ K hK hfac).1

/-- Compression intertwines the actual quotient with the unnormalized Levi action. -/
theorem blockCompressedAction_mk (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization_allFieldBZ T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsWeaklyContracting_allFieldBZ T a →
        ∀ v : fixedVectors ρ K.toSubgroup,
          mk ρ (B.unipotentSubgroup F.Carrier)
              (compressedAction ρ hρ K hK (B.blockScalar F.Carrier a) v : V) =
            action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
              (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
              (B.blockScalarInLevi F.Carrier a)
              (mk ρ (B.unipotentSubgroup F.Carrier) (v : V)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ K hK hfac
  exact (blockCompression F T n B V ρ hρ K hK hfac).2

end Langlands.AllFieldBZ.Jacquet
