import Langlands.Global.AdelicIwasawaStatement
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.InfinitePlaceLeviIwasawaBaseChange

/-! # Maximal compact subgroups of `G(𝔸_F)` and their infinite and finite factors

A maximal compact subgroup of a product of topological groups is the product of its two
projections, and each projection is maximal compact. Through the published product
decomposition `G(𝔸_F) ≃ G(𝔸_{F,∞}) × G(𝔸_{F,f})`, a maximal compact `K ≤ G(𝔸_F)` is therefore
`K_∞ × K_f`, with `K_∞ = K.comap ofInfinite` maximal compact in `G(𝔸_{F,∞})`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.CompactIwasawa

variable {A B : Type*} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]

/-- The product of two compact subgroups is compact. -/
theorem isCompact_subgroupProd {H : Subgroup A} {L : Subgroup B} (hH : IsCompact (H : Set A))
    (hL : IsCompact (L : Set B)) : IsCompact ((H.prod L : Subgroup (A × B)) : Set (A × B)) := by
  rw [Subgroup.coe_prod]
  exact hH.prod hL

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- Every subgroup of a product lies in the product of its two projections. -/
theorem le_prod_map_fst_map_snd (K : Subgroup (A × B)) :
    K ≤ (K.map (MonoidHom.fst A B)).prod (K.map (MonoidHom.snd A B)) :=
  fun x hx => Subgroup.mem_prod.mpr ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩

/-- The first projection of a compact subgroup is compact. -/
theorem isCompact_map_fst {K : Subgroup (A × B)} (hK : IsCompact (K : Set (A × B))) :
    IsCompact ((K.map (MonoidHom.fst A B) : Subgroup A) : Set A) := by
  rw [Subgroup.coe_map]
  exact hK.image continuous_fst

/-- The second projection of a compact subgroup is compact. -/
theorem isCompact_map_snd {K : Subgroup (A × B)} (hK : IsCompact (K : Set (A × B))) :
    IsCompact ((K.map (MonoidHom.snd A B) : Subgroup B) : Set B) := by
  rw [Subgroup.coe_map]
  exact hK.image continuous_snd

/-- A maximal compact subgroup of a product is the product of its two projections. -/
theorem IsMaximalCompact.eq_prod_map {K : Subgroup (A × B)} (hK : IsMaximalCompact K) :
    K = (K.map (MonoidHom.fst A B)).prod (K.map (MonoidHom.snd A B)) :=
  (hK.2 _ (isCompact_subgroupProd (isCompact_map_fst hK.1) (isCompact_map_snd hK.1))
    (le_prod_map_fst_map_snd K)).symm

/-- For a maximal compact `K ≤ A × B`, the points `(a, 1)` of `K` are exactly the first
projection of `K`. -/
theorem IsMaximalCompact.comap_inl_eq_map_fst {K : Subgroup (A × B)} (hK : IsMaximalCompact K) :
    K.comap (MonoidHom.inl A B) = K.map (MonoidHom.fst A B) := by
  ext a
  refine ⟨fun ha => ⟨(a, 1), ha, rfl⟩, fun ha => ?_⟩
  change (a, (1 : B)) ∈ K
  rw [hK.eq_prod_map]
  exact Subgroup.mem_prod.mpr ⟨ha, Subgroup.one_mem _⟩

/-- For a maximal compact `K ≤ A × B`, the points `(1, b)` of `K` are exactly the second
projection of `K`. -/
theorem IsMaximalCompact.comap_inr_eq_map_snd {K : Subgroup (A × B)} (hK : IsMaximalCompact K) :
    K.comap (MonoidHom.inr A B) = K.map (MonoidHom.snd A B) := by
  ext b
  refine ⟨fun hb => ⟨(1, b), hb, rfl⟩, fun hb => ?_⟩
  change ((1 : A), b) ∈ K
  rw [hK.eq_prod_map]
  exact Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hb⟩

/-- The first factor of a maximal compact subgroup of a product is maximal compact. -/
theorem IsMaximalCompact.comap_inl {K : Subgroup (A × B)} (hK : IsMaximalCompact K) :
    IsMaximalCompact (K.comap (MonoidHom.inl A B)) := by
  rw [hK.comap_inl_eq_map_fst]
  refine ⟨isCompact_map_fst hK.1, fun L hL hle => le_antisymm (fun a ha => ?_) hle⟩
  have hprod : L.prod (K.map (MonoidHom.snd A B)) = K :=
    hK.2 _ (isCompact_subgroupProd hL (isCompact_map_snd hK.1))
      ((le_prod_map_fst_map_snd K).trans (Subgroup.prod_mono hle le_rfl))
  have hmem : (a, (1 : B)) ∈ K := hprod ▸ Subgroup.mem_prod.mpr ⟨ha, Subgroup.one_mem _⟩
  exact ⟨(a, 1), hmem, rfl⟩

/-- The second factor of a maximal compact subgroup of a product is maximal compact. -/
theorem IsMaximalCompact.comap_inr {K : Subgroup (A × B)} (hK : IsMaximalCompact K) :
    IsMaximalCompact (K.comap (MonoidHom.inr A B)) := by
  rw [hK.comap_inr_eq_map_snd]
  refine ⟨isCompact_map_snd hK.1, fun L hL hle => le_antisymm (fun b hb => ?_) hle⟩
  have hprod : (K.map (MonoidHom.fst A B)).prod L = K :=
    hK.2 _ (isCompact_subgroupProd (isCompact_map_fst hK.1) hL)
      ((le_prod_map_fst_map_snd K).trans (Subgroup.prod_mono le_rfl hle))
  have hmem : ((1 : A), b) ∈ K := hprod ▸ Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hb⟩
  exact ⟨(1, b), hmem, rfl⟩

/-- The product of two maximal compact subgroups is maximal compact. -/
theorem IsMaximalCompact.prod {H : Subgroup A} {L : Subgroup B} (hH : IsMaximalCompact H)
    (hL : IsMaximalCompact L) : IsMaximalCompact (H.prod L) := by
  refine ⟨isCompact_subgroupProd hH.1 hL.1, fun M hM hle => le_antisymm ?_ hle⟩
  have h1 : M.map (MonoidHom.fst A B) = H :=
    hH.2 _ (isCompact_map_fst hM)
      (fun a ha => ⟨(a, 1), hle (Subgroup.mem_prod.mpr ⟨ha, Subgroup.one_mem _⟩), rfl⟩)
  have h2 : M.map (MonoidHom.snd A B) = L :=
    hL.2 _ (isCompact_map_snd hM)
      (fun b hb => ⟨(1, b), hle (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hb⟩), rfl⟩)
  calc M ≤ (M.map (MonoidHom.fst A B)).prod (M.map (MonoidHom.snd A B)) :=
        le_prod_map_fst_map_snd M
    _ = H.prod L := by rw [h1, h2]

/-- A product subgroup is maximal compact exactly when both factors are. -/
theorem isMaximalCompact_prod_iff {H : Subgroup A} {L : Subgroup B} :
    IsMaximalCompact (H.prod L) ↔ IsMaximalCompact H ∧ IsMaximalCompact L := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => h.1.prod h.2⟩
  · have hH : (H.prod L).comap (MonoidHom.inl A B) = H := by
      ext a
      simp [Subgroup.mem_prod]
    exact hH ▸ h.comap_inl
  · have hL : (H.prod L).comap (MonoidHom.inr A B) = L := by
      ext b
      simp [Subgroup.mem_prod]
    exact hL ▸ h.comap_inr

/-- Maximality is invariant under pulling back along a topological group isomorphism. -/
theorem isMaximalCompact_comap_equiv {X Y : Type*} [Group X] [Group Y] [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ* Y) {K : Subgroup Y} :
    IsMaximalCompact (K.comap e.toMonoidHom) ↔ IsMaximalCompact K := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := h.map e
    rwa [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective] at h'
  · rw [Subgroup.comap_equiv_eq_map_symm']
    exact h.map e.symm

end Langlands.CompactIwasawa

namespace Langlands.Global.AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The adelic maximality predicate is the generic one on the actual point group. -/
theorem isMaximalCompactSubgroup_iff (K : Subgroup (AdelicGroupPoints F G)) :
    IsMaximalCompactSubgroup F G K ↔ CompactIwasawa.IsMaximalCompact K := Iff.rfl

variable [IsAffine G.X.left]

/-- The points of `G(𝔸_F)` whose infinite part lies in `Kinf` and whose finite part lies
in `Kfin`. -/
def factorSubgroup (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (Kfin : Subgroup (FiniteAdelicGroupPoints F G)) : Subgroup (AdelicGroupPoints F G) :=
  (Kinf.prod Kfin).comap (split F G).toMonoidHom

variable {F G}

@[simp] theorem mem_factorSubgroup {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    {Kfin : Subgroup (FiniteAdelicGroupPoints F G)} {g : AdelicGroupPoints F G} :
    g ∈ factorSubgroup F G Kinf Kfin ↔ infinite F G g ∈ Kinf ∧ finite F G g ∈ Kfin :=
  Subgroup.mem_prod

/-- The infinite factor of `Kinf × Kfin` is `Kinf`. -/
theorem comap_ofInfinite_factorSubgroup (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (Kfin : Subgroup (FiniteAdelicGroupPoints F G)) :
    (factorSubgroup F G Kinf Kfin).comap (ofInfinite F G).toMonoidHom = Kinf := by
  ext a
  simp [Subgroup.mem_comap]

/-- The finite factor of `Kinf × Kfin` is `Kfin`. -/
theorem comap_ofFinite_factorSubgroup (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (Kfin : Subgroup (FiniteAdelicGroupPoints F G)) :
    (factorSubgroup F G Kinf Kfin).comap (ofFinite F G).toMonoidHom = Kfin := by
  ext b
  simp [Subgroup.mem_comap]

/-- `Kinf × Kfin` is maximal compact exactly when both factors are. -/
theorem isMaximalCompactSubgroup_factorSubgroup_iff
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    {Kfin : Subgroup (FiniteAdelicGroupPoints F G)} :
    IsMaximalCompactSubgroup F G (factorSubgroup F G Kinf Kfin) ↔
      CompactIwasawa.IsMaximalCompact Kinf ∧ CompactIwasawa.IsMaximalCompact Kfin :=
  (CompactIwasawa.isMaximalCompact_comap_equiv (split F G)).trans
    CompactIwasawa.isMaximalCompact_prod_iff

/-- The infinite factor of `K`, read through the product decomposition. -/
theorem comap_ofInfinite_eq (K : Subgroup (AdelicGroupPoints F G)) :
    K.comap (ofInfinite F G).toMonoidHom =
      (K.map (split F G).toMonoidHom).comap (MonoidHom.inl _ _) := by
  ext a
  rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_map_equiv]
  rfl

/-- The finite factor of `K`, read through the product decomposition. -/
theorem comap_ofFinite_eq (K : Subgroup (AdelicGroupPoints F G)) :
    K.comap (ofFinite F G).toMonoidHom =
      (K.map (split F G).toMonoidHom).comap (MonoidHom.inr _ _) := by
  ext b
  rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_map_equiv]
  rfl

namespace IsMaximalCompactSubgroup

variable {K : Subgroup (AdelicGroupPoints F G)}

/-- The infinite factor `K_∞ = {x ∈ G(𝔸_{F,∞}) : (x, 1) ∈ K}` of a maximal compact subgroup of
`G(𝔸_F)` is maximal compact in `G(𝔸_{F,∞})`. -/
theorem isMaximalCompact_comap_ofInfinite (hK : IsMaximalCompactSubgroup F G K) :
    CompactIwasawa.IsMaximalCompact (K.comap (ofInfinite F G).toMonoidHom) := by
  rw [comap_ofInfinite_eq]
  exact (CompactIwasawa.IsMaximalCompact.map hK (split F G)).comap_inl

/-- The finite factor `K_f = {y ∈ G(𝔸_{F,f}) : (1, y) ∈ K}` of a maximal compact subgroup of
`G(𝔸_F)` is maximal compact in `G(𝔸_{F,f})`. -/
theorem isMaximalCompact_comap_ofFinite (hK : IsMaximalCompactSubgroup F G K) :
    CompactIwasawa.IsMaximalCompact (K.comap (ofFinite F G).toMonoidHom) := by
  rw [comap_ofFinite_eq]
  exact (CompactIwasawa.IsMaximalCompact.map hK (split F G)).comap_inr

/-- A maximal compact subgroup of `G(𝔸_F)` is the product `K_∞ × K_f` of its two factors. -/
theorem eq_factorSubgroup (hK : IsMaximalCompactSubgroup F G K) :
    K = factorSubgroup F G (K.comap (ofInfinite F G).toMonoidHom)
      (K.comap (ofFinite F G).toMonoidHom) := by
  have hK' := CompactIwasawa.IsMaximalCompact.map hK (split F G)
  rw [comap_ofInfinite_eq, comap_ofFinite_eq, hK'.comap_inl_eq_map_fst,
    hK'.comap_inr_eq_map_snd, factorSubgroup, ← hK'.eq_prod_map]
  exact (Subgroup.comap_map_eq_self_of_injective (split F G).injective K).symm

/-- Membership in a maximal compact subgroup is decided factor by factor. -/
theorem mem_iff (hK : IsMaximalCompactSubgroup F G K) (g : AdelicGroupPoints F G) :
    g ∈ K ↔ ofInfinite F G (infinite F G g) ∈ K ∧ ofFinite F G (finite F G g) ∈ K := by
  conv_lhs => rw [hK.eq_factorSubgroup]
  exact mem_factorSubgroup

end IsMaximalCompactSubgroup

/-- A subgroup of `G(𝔸_F)` is maximal compact exactly when it is `K_∞ × K_f` for maximal compact
subgroups `K_∞ ≤ G(𝔸_{F,∞})` and `K_f ≤ G(𝔸_{F,f})`. -/
theorem isMaximalCompactSubgroup_iff_exists_factorSubgroup (K : Subgroup (AdelicGroupPoints F G)) :
    IsMaximalCompactSubgroup F G K ↔
      ∃ (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
        (Kfin : Subgroup (FiniteAdelicGroupPoints F G)),
        CompactIwasawa.IsMaximalCompact Kinf ∧ CompactIwasawa.IsMaximalCompact Kfin ∧
          K = factorSubgroup F G Kinf Kfin := by
  refine ⟨fun hK => ⟨_, _, hK.isMaximalCompact_comap_ofInfinite,
    hK.isMaximalCompact_comap_ofFinite, hK.eq_factorSubgroup⟩, ?_⟩
  rintro ⟨Kinf, Kfin, hinf, hfin, rfl⟩
  exact isMaximalCompactSubgroup_factorSubgroup_iff.mpr ⟨hinf, hfin⟩

namespace IsParabolicIwasawaCompact

variable {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
  {K : Subgroup (AdelicGroupPoints F G)}

/-- The infinite factor of a parabolic Iwasawa compact subgroup is maximal compact in
`G(𝔸_{F,∞})`. -/
theorem isMaximalCompact_comap_ofInfinite (hK : IsParabolicIwasawaCompact F G P p K) :
    CompactIwasawa.IsMaximalCompact (K.comap (ofInfinite F G).toMonoidHom) :=
  IsMaximalCompactSubgroup.isMaximalCompact_comap_ofInfinite hK.1

/-- The finite factor of a parabolic Iwasawa compact subgroup is maximal compact in
`G(𝔸_{F,f})`. -/
theorem isMaximalCompact_comap_ofFinite (hK : IsParabolicIwasawaCompact F G P p K) :
    CompactIwasawa.IsMaximalCompact (K.comap (ofFinite F G).toMonoidHom) :=
  IsMaximalCompactSubgroup.isMaximalCompact_comap_ofFinite hK.1

end IsParabolicIwasawaCompact

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- A parabolic Iwasawa compact subgroup for a subgroup `f : P₀ → P` is one for `P`. For
instance one `K` with `P₀(𝔸_F) K = G(𝔸_F)` for a minimal parabolic serves every parabolic
containing `P₀`. -/
theorem IsParabolicIwasawaCompact.of_comp {P₀ P : GroupScheme (Spec (CommRingCat.of F))}
    (f : P₀ ⟶ P) (p : P ⟶ G) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsParabolicIwasawaCompact F G P₀ (f ≫ p) K) : IsParabolicIwasawaCompact F G P p K := by
  refine ⟨hK.1, Set.eq_univ_of_univ_subset ?_⟩
  rw [← hK.2]
  apply Set.mul_subset_mul_right
  rintro _ ⟨x, rfl⟩
  refine ⟨map F P₀ P f x, ?_⟩
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]

end Langlands.Global.AdelicGroupPoints
