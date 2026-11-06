import Langlands.Shimura.LevelHecke

/-! # Translation and composition laws of double-coset operators -/

noncomputable section

universe t v w

set_option autoImplicit false

namespace Langlands.Shimura.LevelHecke

open CategoryTheory CategoryTheory.Limits Opposite CompactOpenLevel

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ## Numbers of cosets -/

section Card

variable (K L : CompactOpenLevel G) (g : G)

theorem heckeLevel_subgroup_eq :
    (heckeLevel K L g).subgroup = K.subgroup ⊓ (conjLevel g L).subgroup := by
  ext x
  rw [mem_heckeLevel, Subgroup.mem_inf, mem_conjLevel]

/-- The number of cosets `K / (K ∩ g L g⁻¹)` is the index of `g L g⁻¹ ∩ K` in `K`. -/
theorem card_heckeCosets :
    Nat.card (HeckeCosets K L g) = (conjLevel g L).subgroup.relIndex K.subgroup := by
  change (heckeLevel K L g).subgroup.relIndex K.subgroup = _
  rw [heckeLevel_subgroup_eq, Subgroup.inf_relIndex_left]

/-- The number of cosets `K / (K ∩ L)` is the index of `L ∩ K` in `K`. -/
theorem card_heckeCosets_one :
    Nat.card (HeckeCosets K L 1) = L.subgroup.relIndex K.subgroup := by
  have h : (heckeLevel K L 1).subgroup = K.subgroup ⊓ L.subgroup := by
    ext x
    rw [mem_heckeLevel, Subgroup.mem_inf, inv_one, one_mul, mul_one]
  change (heckeLevel K L 1).subgroup.relIndex K.subgroup = _
  rw [h, Subgroup.inf_relIndex_left]

end Card

/-! ## Translation by group elements -/

section Translate

variable {R : Type t} [CommRing R] {V : Type w} [AddCommGroup V] [Module R V]
variable (ρ : Representation R G V)

/-- Translation by `h` sends vectors fixed by `L` to vectors fixed by `h L h⁻¹`. -/
def translateFixed (h : G) (L : CompactOpenLevel G) :
    fixedVectors ρ L.subgroup →ₗ[R] fixedVectors ρ (conjLevel h L).subgroup where
  toFun v := ⟨ρ h v, fun x => by
    have hx : h⁻¹ * (x : G) * h ∈ L.subgroup := mem_conjLevel.mp x.property
    have e : (x : G) * h = h * (h⁻¹ * (x : G) * h) := by group
    change ρ (x : G) (ρ h v) = ρ h v
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
    exact congrArg (ρ h) (v.property ⟨_, hx⟩)⟩
  map_add' v w := Subtype.ext (map_add (ρ h) (v : V) (w : V))
  map_smul' r v := Subtype.ext (map_smul (ρ h) r (v : V))

@[simp] theorem translateFixed_apply_coe (h : G) (L : CompactOpenLevel G)
    (v : fixedVectors ρ L.subgroup) : (translateFixed ρ h L v : V) = ρ h v := rfl

/-- `[K x (h L h⁻¹)] ∘ ρ(h) = [K (x h) L]` on vectors fixed by `L`. -/
theorem heckeOperator_comp_translateFixed (K L : CompactOpenLevel G) (x h : G) :
    (heckeOperator ρ K (conjLevel h L) x).comp (translateFixed ρ h L) =
      heckeOperator ρ K L (x * h) := by
  have hH : (heckeLevel K (conjLevel h L) x).subgroup = (heckeLevel K L (x * h)).subgroup := by
    ext y
    rw [mem_heckeLevel, mem_heckeLevel, mem_conjLevel]
    have e : h⁻¹ * (x⁻¹ * y * x) * h = (x * h)⁻¹ * y * (x * h) := by group
    rw [e]
  have hH' : (heckeLevel K (conjLevel h L) x).subgroup.subgroupOf K.subgroup =
      (heckeLevel K L (x * h)).subgroup.subgroupOf K.subgroup := by
    rw [hH]
  let e : HeckeCosets K (conjLevel h L) x ≃ HeckeCosets K L (x * h) :=
    Subgroup.quotientEquivOfEq hH'
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change ∑ q, cosetTerm ρ K (conjLevel h L) x (translateFixed ρ h L v) q =
    ∑ q, cosetTerm ρ K L (x * h) v q
  refine Fintype.sum_equiv e _ _ (fun q => ?_)
  induction q using QuotientGroup.induction_on with
  | H k =>
    change ρ ((k : G) * x) (ρ h v) = ρ ((k : G) * (x * h)) v
    rw [← Module.End.mul_apply, ← map_mul, mul_assoc]

/-- The factorization `[K g L] = [K 1 (g L g⁻¹)] ∘ ρ(g)`. -/
theorem heckeOperator_eq_comp_translateFixed (K L : CompactOpenLevel G) (g : G) :
    heckeOperator ρ K L g =
      (heckeOperator ρ K (conjLevel g L) 1).comp (translateFixed ρ g L) := by
  rw [heckeOperator_comp_translateFixed, one_mul]

/-- `ρ(h) ∘ [K g L] = [(h K h⁻¹) (h g) L]` on vectors fixed by `L`. -/
theorem translateFixed_comp_heckeOperator (K L : CompactOpenLevel G) (g h : G) :
    (translateFixed ρ h K).comp (heckeOperator ρ K L g) =
      heckeOperator ρ (conjLevel h K) L (h * g) := by
  let φ : K.subgroup ≃ (conjLevel h K).subgroup :=
    { toFun := fun k => ⟨h * k * h⁻¹, mem_conjLevel.mpr (by simp [mul_assoc])⟩
      invFun := fun k => ⟨h⁻¹ * k * h, mem_conjLevel.mp k.property⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc]) }
  let e : HeckeCosets K L g ≃ HeckeCosets (conjLevel h K) L (h * g) :=
    Quotient.congr φ (fun a b => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf, mem_heckeLevel, mem_heckeLevel]
      have e : (h * g)⁻¹ * (((φ a)⁻¹ * φ b : (conjLevel h K).subgroup) : G) * (h * g) =
          g⁻¹ * ((a⁻¹ * b : K.subgroup) : G) * g := by
        change (h * g)⁻¹ * ((h * (a : G) * h⁻¹)⁻¹ * (h * (b : G) * h⁻¹)) * (h * g) =
          g⁻¹ * ((a : G)⁻¹ * (b : G)) * g
        group
      rw [e]
      exact ⟨fun hh => ⟨((φ a)⁻¹ * φ b).property, hh.2⟩, fun hh => ⟨(a⁻¹ * b).property, hh.2⟩⟩)
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change ρ h (∑ q, cosetTerm ρ K L g v q) = ∑ q, cosetTerm ρ (conjLevel h K) L (h * g) v q
  rw [map_sum]
  refine Fintype.sum_equiv e _ _ (fun q => ?_)
  induction q using QuotientGroup.induction_on with
  | H k =>
    change ρ h (ρ ((k : G) * g) v) = ρ (h * (k : G) * h⁻¹ * (h * g)) v
    rw [← Module.End.mul_apply, ← map_mul, show h * (k : G) * h⁻¹ * (h * g) = h * ((k : G) * g)
      by group]

/-- Compatibility with conjugation:
`ρ(h) ∘ [K g L] = [(h K h⁻¹) (h g h⁻¹) (h L h⁻¹)] ∘ ρ(h)`. -/
theorem translateFixed_comp_heckeOperator_conj (K L : CompactOpenLevel G) (g h : G) :
    (translateFixed ρ h K).comp (heckeOperator ρ K L g) =
      (heckeOperator ρ (conjLevel h K) (conjLevel h L) (h * g * h⁻¹)).comp
        (translateFixed ρ h L) := by
  rw [translateFixed_comp_heckeOperator, heckeOperator_comp_translateFixed, inv_mul_cancel_right]

end Translate

/-! ## Inclusions and traces -/

section Compose

variable {R : Type t} [CommRing R] {V : Type w} [AddCommGroup V] [Module R V]
variable (ρ : Representation R G V) {K L M : CompactOpenLevel G}

/-- For `M ⊆ K ⊆ L`, the inclusions compose: `[M 1 K] ∘ [K 1 L] = [M 1 L]`. -/
theorem heckeOperator_comp_of_le_of_le (hMK : M.subgroup ≤ K.subgroup)
    (hKL : K.subgroup ≤ L.subgroup) :
    (heckeOperator ρ M K 1).comp (heckeOperator ρ K L 1) = heckeOperator ρ M L 1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [LinearMap.comp_apply, heckeOperator_one_of_le ρ hMK, heckeOperator_one_of_le ρ hKL,
    heckeOperator_one_of_le ρ (hMK.trans hKL)]

/-- For `K ⊆ L`, the trace after the inclusion, `[L 1 K] ∘ [K 1 L]`, is multiplication by the
index of `K` in `L`. -/
theorem heckeOperator_trace_comp_inclusion (hKL : K.subgroup ≤ L.subgroup) :
    (heckeOperator ρ L K 1).comp (heckeOperator ρ K L 1) =
      K.subgroup.relIndex L.subgroup • LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [LinearMap.comp_apply, heckeOperator_apply_out]
  have hq : ∀ q : HeckeCosets L K 1,
      ρ ((q.out : G) * 1) (heckeOperator ρ K L 1 v : V) = v := by
    intro q
    rw [heckeOperator_one_of_le ρ hKL, mul_one]
    exact v.property q.out
  rw [Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_heckeCosets_one]
  rfl

/-- For `M ⊆ K ⊆ L`, the traces compose: `[L 1 K] ∘ [K 1 M] = [L 1 M]`. The cosets
`L / M` are identified with pairs of cosets in `L / K` and `K / M`, using chosen
representatives of `L / K`. -/
theorem heckeOperator_comp_of_ge_of_ge (hMK : M.subgroup ≤ K.subgroup)
    (hKL : K.subgroup ≤ L.subgroup) :
    (heckeOperator ρ L K 1).comp (heckeOperator ρ K M 1) = heckeOperator ρ L M 1 := by
  have hst : (heckeLevel L M 1).subgroup.subgroupOf L.subgroup ≤
      (heckeLevel L K 1).subgroup.subgroupOf L.subgroup := fun x hx => by
    rw [Subgroup.mem_subgroupOf, mem_heckeLevel] at hx ⊢
    exact ⟨hx.1, hMK hx.2⟩
  let t := (heckeLevel L K 1).subgroup.subgroupOf L.subgroup
  let s := (heckeLevel L M 1).subgroup.subgroupOf L.subgroup
  let φ : t ≃ K.subgroup :=
    { toFun := fun x => ⟨((x : L.subgroup) : G), by
        simpa using (mem_heckeLevel.mp (Subgroup.mem_subgroupOf.mp x.property)).2⟩
      invFun := fun k => ⟨⟨k, hKL k.property⟩, Subgroup.mem_subgroupOf.mpr
        (mem_heckeLevel.mpr ⟨hKL k.property, by simp⟩)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eKM : t ⧸ s.subgroupOf t ≃ HeckeCosets K M 1 :=
    Quotient.congr φ (fun a b => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_heckeLevel, mem_heckeLevel]
      exact ⟨fun hh => ⟨((φ a)⁻¹ * φ b).property, hh.2⟩,
        fun hh => ⟨((a⁻¹ * b : t) : L.subgroup).property, hh.2⟩⟩)
  let E : HeckeCosets L M 1 ≃ HeckeCosets L K 1 × HeckeCosets K M 1 :=
    (Subgroup.quotientEquivProdOfLE hst).trans (Equiv.prodCongr (Equiv.refl _) eKM)
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [LinearMap.comp_apply, heckeOperator_apply_out ρ L K 1, heckeOperator_apply ρ K M 1,
    heckeOperator_apply ρ L M 1,
    ← Fintype.sum_equiv E.symm (fun p => cosetTerm ρ L M 1 v (E.symm p)) _ (fun _ => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  induction b using QuotientGroup.induction_on with
  | H k =>
    change ρ ((a.out : G) * 1) (ρ ((k : G) * 1) v) = ρ ((a.out : G) * (k : G) * 1) v
    rw [mul_one, mul_one, mul_one, ← Module.End.mul_apply, ← map_mul]

/-- If `g M g⁻¹ ⊆ K ⊆ L`, then `[L 1 K] ∘ [K g M] = [L g M]`. -/
theorem heckeOperator_trace_comp_of_conjLevel_le {g : G}
    (hMK : (conjLevel g M).subgroup ≤ K.subgroup) (hKL : K.subgroup ≤ L.subgroup) :
    (heckeOperator ρ L K 1).comp (heckeOperator ρ K M g) = heckeOperator ρ L M g := by
  rw [heckeOperator_eq_comp_translateFixed ρ K M g, heckeOperator_eq_comp_translateFixed ρ L M g,
    ← LinearMap.comp_assoc, heckeOperator_comp_of_ge_of_ge ρ hMK hKL]

/-- If `M ⊆ L` and `g L g⁻¹ ⊆ K`, then `[K g L] ∘ [L 1 M] = [K g M]`. -/
theorem heckeOperator_comp_trace_of_conjLevel_le {g : G} (hML : M.subgroup ≤ L.subgroup)
    (hLK : (conjLevel g L).subgroup ≤ K.subgroup) :
    (heckeOperator ρ K L g).comp (heckeOperator ρ L M 1) = heckeOperator ρ K M g := by
  have hc : (conjLevel g M).subgroup ≤ (conjLevel g L).subgroup := fun x hx =>
    mem_conjLevel.mpr (hML (mem_conjLevel.mp hx))
  rw [heckeOperator_eq_comp_translateFixed ρ K L g, LinearMap.comp_assoc,
    translateFixed_comp_heckeOperator, mul_one,
    heckeOperator_eq_comp_translateFixed ρ (conjLevel g L) M g, ← LinearMap.comp_assoc,
    heckeOperator_comp_of_ge_of_ge ρ hc hLK]
  exact (heckeOperator_eq_comp_translateFixed ρ K M g).symm

end Compose

/-! ## Natural transformations -/

section NatTrans

variable (R : Type t) [CommRing R] {K L M : CompactOpenLevel G}

/-- The inclusions compose as natural transformations of fixed-vector functors. -/
theorem heckeNatTrans_comp_of_le_of_le (hMK : M.subgroup ≤ K.subgroup)
    (hKL : K.subgroup ≤ L.subgroup) :
    heckeNatTrans.{t, v, w} R K L 1 ≫ heckeNatTrans R M K 1 = heckeNatTrans R M L 1 := by
  apply NatTrans.ext
  funext A
  apply ModuleCat.hom_ext
  exact heckeOperator_comp_of_le_of_le A.obj.ρ hMK hKL

/-- The traces compose as natural transformations of fixed-vector functors. -/
theorem heckeNatTrans_comp_of_ge_of_ge (hMK : M.subgroup ≤ K.subgroup)
    (hKL : K.subgroup ≤ L.subgroup) :
    heckeNatTrans.{t, v, w} R K M 1 ≫ heckeNatTrans R L K 1 = heckeNatTrans R L M 1 := by
  apply NatTrans.ext
  funext A
  apply ModuleCat.hom_ext
  exact heckeOperator_comp_of_ge_of_ge A.obj.ρ hMK hKL

end NatTrans

/-! ## Level classes -/

section LevelColimit

variable {R : Type t} [CommRing R]
variable [HasColimitsOfShape (Ordered G)ᵒᵖ (ModuleCat.{w} R)]
variable (F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R) (hF : LevelColimit.IsLevelTrivial F)

/-- Translating the image of a class of level `L` by `h` gives the image of its transport to
the level `h L h⁻¹`. -/
theorem translateFixed_levelClass (h : G) (L : CompactOpenLevel G) (x : F.obj (op L)) :
    translateFixed (LevelColimit.smoothRep (G := G) (R := R) F hF).obj.ρ h L
        (levelClass F hF L x) =
      levelClass F hF (conjLevel h L) ((F.map (conjArrow h L).op).hom x) :=
  Subtype.ext (LevelColimit.smoothRep_ρ_ι_apply F hF h L x)

end LevelColimit

end Langlands.Shimura.LevelHecke
