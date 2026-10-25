import Langlands.Representation.Jacquet.RefinedOppositeCompressionStatement
import Langlands.Representation.Jacquet.BlockCompressionProof

namespace Langlands.Jacquet

open GeneralLinear Geometric

universe uG uF uV

private theorem average_right_translate
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (k : K) (v : V) :
    Compact.averageMap ρ hρ K hK (ρ k.val v) =
      Compact.averageMap ρ hρ K hK v := by
  let τ := ρ.comp K.toSubgroup.subtype
  have ho : Compact.orbit τ (τ k v) = Compact.orbit τ v := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h * k, by simp⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h * k⁻¹, by simp [map_mul, Module.End.mul_apply]⟩
  change Compact.orbitMean τ (τ k v) = Compact.orbitMean τ v
  unfold Compact.orbitMean
  rw [ho]

/-- The two actual normalized compression identities for the product opposite radical. -/
theorem refinedOppositeCompression : RefinedOppositeCompressionStatement.{uF,uV} := by
  classical
  intro p _ F T n B S
  let := T.topology
  let := T.leviTopologicalGroup B
  intro V _ _ ρ hρ K hK hfac
  let KP := CuspidalSupport.leviPiOpenSubgroup T B K
  let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK
  let g := fun (a : ∀ i, Fin (S i).length → F.Carrierˣ) =>
    (fun i => ((S i).blockScalar F.Carrier (a i))⁻¹ : B.Levi F.Carrier)
  have hmem (x : B.Levi F.Carrier) : x ∈ KP ↔ ∀ i, x i ∈ K i :=
    CuspidalSupport.mem_leviPiOpenSubgroup T B K x
  have hcomm (a : ∀ i, Fin (S i).length → F.Carrierˣ)
      (m : B.Levi F.Carrier) (hm : ∀ i, m i ∈ (S i).leviSubgroup F.Carrier) :
      g a * m = m * g a := by
    funext i
    change ((S i).blockScalar F.Carrier (a i))⁻¹ * m i =
      m i * ((S i).blockScalar F.Carrier (a i))⁻¹
    apply Commute.inv_left
    obtain ⟨mi, hmi⟩ := hm i
    rw [← hmi]
    change (S i).leviEmbedding F.Carrier ((S i).blockScalarLevi F.Carrier (a i)) *
        (S i).leviEmbedding F.Carrier mi =
      (S i).leviEmbedding F.Carrier mi *
        (S i).leviEmbedding F.Carrier ((S i).blockScalarLevi F.Carrier (a i))
    rw [← map_mul, ← map_mul, (S i).blockScalarLevi_commute]
  have horbit (a : ∀ i, Fin (S i).length → F.Carrierˣ)
      (ha : ∀ i, (S i).IsWeaklyContracting T (a i))
      (v : fixedVectors ρ KP.toSubgroup) (k : KP) :
      ∃ l : KP, l.val ∈ refinedOppositeUnipotent F.Carrier B S ∧
        ρ k.val (ρ (g a) v.val) = ρ l.val (ρ (g a) v.val) := by
    have hk := (hmem k.val).mp k.property
    choose z hz using fun i => (hfac i).1.2 ⟨k.val i, hk i⟩
    let l : B.Levi F.Carrier := fun i => (z i).1.val
    let m : B.Levi F.Carrier := fun i => (z i).2.1.val
    let u : B.Levi F.Carrier := fun i => (z i).2.2.val
    have hlK : l ∈ KP := (hmem l).mpr fun i => (z i).1.property.1
    have hmK : m ∈ KP := (hmem m).mpr fun i => (z i).2.1.property.1
    have hlN : l ∈ refinedOppositeUnipotent F.Carrier B S :=
      (mem_refinedOppositeUnipotent F.Carrier B S l).mpr
        fun i => (z i).1.property.2
    have hprod : k.val = l * m * u := by
      funext i
      exact (congrArg Subtype.val (hz i)).symm
    have huK : (g a)⁻¹ * u * g a ∈ KP := by
      apply (hmem _).mpr
      intro i
      change (((S i).blockScalar F.Carrier (a i))⁻¹)⁻¹ *
        (z i).2.2.val * ((S i).blockScalar F.Carrier (a i))⁻¹ ∈ K i
      rw [inv_inv]
      exact ((hfac i).2 (a i) (ha i)).1 _ (z i).2.2.property |>.1
    have hu : ρ u (ρ (g a) v.val) = ρ (g a) v.val := by
      calc
        _ = ρ (g a) (ρ ((g a)⁻¹ * u * g a) v.val) := by
          simp only [← Module.End.mul_apply, ← map_mul ρ]
          congr 1
          group
        _ = _ := congrArg (ρ (g a)) (v.property ⟨_, huK⟩)
    have hm : ρ m (ρ (g a) v.val) = ρ (g a) v.val := by
      calc
        _ = ρ (g a) (ρ m v.val) := by
          simp only [← Module.End.mul_apply, ← map_mul ρ]
          rw [hcomm a m (fun i => (z i).2.1.property.2)]
        _ = _ := congrArg (ρ (g a)) (v.property ⟨m, hmK⟩)
    refine ⟨⟨l, hlK⟩, hlN, ?_⟩
    rw [hprod, map_mul, map_mul]
    simp only [Module.End.mul_apply]
    rw [hu, hm]
  have hmul (a b : ∀ i, Fin (S i).length → F.Carrierˣ) :
      g (a * b) = g a * g b := by
    funext i
    change ((S i).blockScalar F.Carrier (a i * b i))⁻¹ =
      ((S i).blockScalar F.Carrier (a i))⁻¹ *
        ((S i).blockScalar F.Carrier (b i))⁻¹
    rw [← map_inv, ← map_inv, ← map_inv, ← map_mul, mul_inv]
  constructor
  · intro a b ha hb
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change Compact.averageMap ρ hρ KP hKP (ρ (g (a * b)) v.val) =
      Compact.averageMap ρ hρ KP hKP
        (ρ (g a) (Compact.averageMap ρ hρ KP hKP (ρ (g b) v.val)))
    rw [hmul, map_mul, Module.End.mul_apply]
    symm
    apply map_averageMap_of_forall_eq ρ hρ KP hKP
      ((Compact.averageMap ρ hρ KP hKP).comp (ρ (g a)))
      (ρ (g b) v.val)
    intro k
    change Compact.averageMap ρ hρ KP hKP
      (ρ (g a) (ρ k.val (ρ (g b) v.val))) = _
    obtain ⟨l, hlN, hl⟩ := horbit b hb v k
    rw [hl]
    have hlK : g a * l.val * (g a)⁻¹ ∈ KP := by
      apply (hmem _).mpr
      intro i
      change ((S i).blockScalar F.Carrier (a i))⁻¹ * l.val i *
        (((S i).blockScalar F.Carrier (a i))⁻¹)⁻¹ ∈ K i
      rw [inv_inv]
      exact ((hfac i).2 (a i) (ha i)).2 _ ⟨(hmem l.val).mp l.property i,
        (mem_refinedOppositeUnipotent F.Carrier B S l.val).mp hlN i⟩ |>.1
    calc
      _ = Compact.averageMap ρ hρ KP hKP
          (ρ (g a * l.val * (g a)⁻¹) (ρ (g a) (ρ (g b) v.val))) := by
        congr 1
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        congr 1
        group
      _ = _ := average_right_translate ρ hρ KP hKP ⟨_, hlK⟩ _
  · intro a ha v
    change mk ρ (refinedOppositeUnipotent F.Carrier B S)
        (Compact.averageMap ρ hρ KP hKP (ρ (g a) v.val)) =
      mk ρ (refinedOppositeUnipotent F.Carrier B S) (ρ (g a) v.val)
    apply map_averageMap_of_forall_eq
    intro k
    obtain ⟨l, hlN, hl⟩ := horbit a ha v k
    rw [hl]
    exact mk_apply_subgroup ρ (refinedOppositeUnipotent F.Carrier B S) ⟨l.val, hlN⟩ _

end Langlands.Jacquet
