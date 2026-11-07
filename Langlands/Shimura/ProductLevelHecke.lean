import Langlands.Shimura.LevelHecke
import Langlands.Shimura.PartialLevelTower

/-! # Double-coset operators for product levels and Hecke operators away from a factor -/

noncomputable section

universe t v v' w

set_option autoImplicit false

namespace Langlands.Shimura.LevelHecke

open CategoryTheory CompactOpenLevel

/-! ## Trivial coset spaces -/

section One

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- If `K ⊆ L`, there is only one coset of `K ∩ L` in `K`. -/
theorem subsingleton_heckeCosets_one {K L : CompactOpenLevel G} (h : K.subgroup ≤ L.subgroup) :
    Subsingleton (HeckeCosets K L 1) :=
  ⟨fun q₁ q₂ => by
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
      induction q₂ using QuotientGroup.induction_on with
      | H b =>
        apply QuotientGroup.eq.mpr
        apply Subgroup.mem_subgroupOf.mpr
        apply mem_heckeLevel.mpr
        refine ⟨(a⁻¹ * b).property, ?_⟩
        simpa using h (a⁻¹ * b).property⟩

instance (K : CompactOpenLevel G) : Subsingleton (HeckeCosets K K 1) :=
  subsingleton_heckeCosets_one le_rfl

end One

variable {H : Type v} {H' : Type v'} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H']

/-! ## Cosets for product levels -/

section Cosets

variable (K L : CompactOpenLevel H) (g : H) (K' L' : CompactOpenLevel H') (g' : H')

theorem mem_heckeLevel_prod {x : H × H'} :
    x ∈ (heckeLevel (prod K K') (prod L L') (g, g')).subgroup ↔
      x.1 ∈ (heckeLevel K L g).subgroup ∧ x.2 ∈ (heckeLevel K' L' g').subgroup := by
  rw [mem_heckeLevel, mem_heckeLevel, mem_heckeLevel, mem_prod, mem_prod]
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  tauto

/-- The element `(k, k')` of the product level `K × K'`. -/
def prodMk (k : K.subgroup) (k' : K'.subgroup) : (prod K K').subgroup :=
  ⟨((k : H), (k' : H')), mem_prod.mpr ⟨k.property, k'.property⟩⟩

omit [IsTopologicalGroup H] [IsTopologicalGroup H'] in
@[simp] theorem coe_prodMk (k : K.subgroup) (k' : K'.subgroup) :
    ((prodMk K K' k k' : (prod K K').subgroup) : H × H') = ((k : H), (k' : H')) := rfl

/-- The components of an element of the product level `K × K'`. -/
def prodSplit (k : (prod K K').subgroup) : K.subgroup × K'.subgroup :=
  (⟨(k : H × H').1, (mem_prod.mp k.property).1⟩, ⟨(k : H × H').2, (mem_prod.mp k.property).2⟩)

/-- The map from the cosets of `(K × K') ∩ (g, g') (L × L') (g, g')⁻¹` in `K × K'` to pairs of
cosets of the factors. -/
def heckeCosetsProdFun (q : HeckeCosets (prod K K') (prod L L') (g, g')) :
    HeckeCosets K L g × HeckeCosets K' L' g' :=
  Quotient.liftOn' q
    (fun k => (((prodSplit K K' k).1 : HeckeCosets K L g),
      ((prodSplit K K' k).2 : HeckeCosets K' L' g')))
    fun a b hab => by
      have h := (mem_heckeLevel_prod K L g K' L' g').mp
        (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab))
      exact Prod.ext (QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr h.1))
        (QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr h.2))

theorem heckeCosetsProdFun_injective : Function.Injective (heckeCosetsProdFun K L g K' L' g') := by
  intro q₁ q₂ h
  induction q₁ using QuotientGroup.induction_on with
  | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
      have h₁ : ((prodSplit K K' a).1 : HeckeCosets K L g) = (prodSplit K K' b).1 :=
        congrArg Prod.fst h
      have h₂ : ((prodSplit K K' a).2 : HeckeCosets K' L' g') = (prodSplit K K' b).2 :=
        congrArg Prod.snd h
      apply QuotientGroup.eq.mpr
      apply Subgroup.mem_subgroupOf.mpr
      exact (mem_heckeLevel_prod K L g K' L' g').mpr
        ⟨Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h₁),
          Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h₂)⟩

theorem heckeCosetsProdFun_surjective :
    Function.Surjective (heckeCosetsProdFun K L g K' L' g') := by
  rintro ⟨q, q'⟩
  induction q using QuotientGroup.induction_on with
  | H a =>
    induction q' using QuotientGroup.induction_on with
    | H a' => exact ⟨(prodMk K K' a a' : HeckeCosets (prod K K') (prod L L') (g, g')), rfl⟩

/-- The cosets of `(K × K') ∩ (g, g') (L × L') (g, g')⁻¹` in `K × K'` are the pairs of cosets of
`K ∩ g L g⁻¹` in `K` and of `K' ∩ g' L' g'⁻¹` in `K'`. -/
def heckeCosetsProd :
    HeckeCosets (prod K K') (prod L L') (g, g') ≃ HeckeCosets K L g × HeckeCosets K' L' g' :=
  Equiv.ofBijective _
    ⟨heckeCosetsProdFun_injective K L g K' L' g', heckeCosetsProdFun_surjective K L g K' L' g'⟩

@[simp] theorem heckeCosetsProd_mk (k : (prod K K').subgroup) :
    heckeCosetsProd K L g K' L' g' (k : HeckeCosets (prod K K') (prod L L') (g, g')) =
      (((prodSplit K K' k).1 : HeckeCosets K L g), ((prodSplit K K' k).2 : HeckeCosets K' L' g')) :=
  rfl

theorem heckeCosetsProd_symm_mk (k : K.subgroup) (k' : K'.subgroup) :
    (heckeCosetsProd K L g K' L' g').symm ((k : HeckeCosets K L g), (k' : HeckeCosets K' L' g')) =
      (prodMk K K' k k' : HeckeCosets (prod K K') (prod L L') (g, g')) := by
  rw [Equiv.symm_apply_eq]
  rfl

/-- The number of cosets for a product level is the product of the numbers for the factors. -/
theorem card_heckeCosets_prod :
    Nat.card (HeckeCosets (prod K K') (prod L L') (g, g')) =
      Nat.card (HeckeCosets K L g) * Nat.card (HeckeCosets K' L' g') := by
  rw [Nat.card_congr (heckeCosetsProd K L g K' L' g'), Nat.card_prod]

end Cosets

/-! ## Operators for product levels -/

section Operator

variable {R : Type t} [CommRing R] {V : Type w} [AddCommGroup V] [Module R V]
variable (ρ : Representation R (H × H') V)

section General

variable (K L : CompactOpenLevel H) (g : H) (K' L' : CompactOpenLevel H') (g' : H')

theorem cosetTerm_prod_symm_mk (v : fixedVectors ρ (prod L L').subgroup) (k : K.subgroup)
    (k' : K'.subgroup) :
    cosetTerm ρ (prod K K') (prod L L') (g, g') v
        ((heckeCosetsProd K L g K' L' g').symm
          ((k : HeckeCosets K L g), (k' : HeckeCosets K' L' g'))) =
      ρ ((k : H) * g, (k' : H') * g') v := by
  rw [heckeCosetsProd_symm_mk, cosetTerm_mk]
  rfl

/-- The operator `[K × K' (g, g') L × L']` as a double sum over the cosets of the factors. -/
theorem heckeOperator_prod_apply (v : fixedVectors ρ (prod L L').subgroup) :
    (heckeOperator ρ (prod K K') (prod L L') (g, g') v : V) =
      ∑ q : HeckeCosets K L g, ∑ q' : HeckeCosets K' L' g',
        cosetTerm ρ (prod K K') (prod L L') (g, g') v
          ((heckeCosetsProd K L g K' L' g').symm (q, q')) :=
  ((Equiv.sum_comp (heckeCosetsProd K L g K' L' g').symm _).symm).trans
    (Fintype.sum_prod_type _)

/-- The operator `[K × K' (g, g') L × L']` in terms of chosen coset representatives of the
factors: `v ↦ ∑_{q, q'} ρ(q g, q' g') v`. -/
theorem heckeOperator_prod_apply_out (v : fixedVectors ρ (prod L L').subgroup) :
    (heckeOperator ρ (prod K K') (prod L L') (g, g') v : V) =
      ∑ q : HeckeCosets K L g, ∑ q' : HeckeCosets K' L' g',
        ρ ((q.out : H) * g, (q'.out : H') * g') v := by
  rw [heckeOperator_prod_apply]
  refine Fintype.sum_congr _ _ fun q => Fintype.sum_congr _ _ fun q' => ?_
  conv_lhs => rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
  exact cosetTerm_prod_symm_mk ρ K L g K' L' g' v _ _

/-- `[K × K' (g, g') L × L'] = [K × K' (g, 1) L × K'] ∘ [L × K' (1, g') L × L']`. -/
theorem heckeOperator_prod_eq_left_comp_right (v : fixedVectors ρ (prod L L').subgroup) :
    heckeOperator ρ (prod K K') (prod L L') (g, g') v =
      heckeOperator ρ (prod K K') (prod L K') (g, 1)
        (heckeOperator ρ (prod L K') (prod L L') (1, g') v) := by
  apply Subtype.ext
  rw [heckeOperator_prod_apply, heckeOperator_prod_apply]
  refine Fintype.sum_congr _ _ fun q => ?_
  rw [Fintype.sum_subsingleton _ ((1 : K'.subgroup) : HeckeCosets K' K' 1)]
  induction q using QuotientGroup.induction_on with
  | H a =>
    rw [cosetTerm_prod_symm_mk, heckeOperator_prod_apply,
      Fintype.sum_subsingleton _ ((1 : L.subgroup) : HeckeCosets L L 1), map_sum]
    refine Fintype.sum_congr _ _ fun q' => ?_
    induction q' using QuotientGroup.induction_on with
    | H a' =>
      rw [cosetTerm_prod_symm_mk, cosetTerm_prod_symm_mk, ← Module.End.mul_apply, ← map_mul]
      simp only [OneMemClass.coe_one, Prod.mk_mul_mk, mul_one, one_mul]

/-- `[K × K' (g, g') L × L'] = [K × K' (1, g') K × L'] ∘ [K × L' (g, 1) L × L']`. -/
theorem heckeOperator_prod_eq_right_comp_left (v : fixedVectors ρ (prod L L').subgroup) :
    heckeOperator ρ (prod K K') (prod L L') (g, g') v =
      heckeOperator ρ (prod K K') (prod K L') (1, g')
        (heckeOperator ρ (prod K L') (prod L L') (g, 1) v) := by
  apply Subtype.ext
  rw [heckeOperator_prod_apply, heckeOperator_prod_apply,
    Fintype.sum_subsingleton _ ((1 : K.subgroup) : HeckeCosets K K 1), Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun q' => ?_
  induction q' using QuotientGroup.induction_on with
  | H a' =>
    rw [cosetTerm_prod_symm_mk, heckeOperator_prod_apply, map_sum]
    refine Fintype.sum_congr _ _ fun q => ?_
    rw [Fintype.sum_subsingleton _ ((1 : L'.subgroup) : HeckeCosets L' L' 1)]
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [cosetTerm_prod_symm_mk, cosetTerm_prod_symm_mk, ← Module.End.mul_apply, ← map_mul]
      simp only [OneMemClass.coe_one, Prod.mk_mul_mk, mul_one, one_mul]

/-- Double-coset operators of the two factors commute:
`[K × K' (g, 1) L × K'] ∘ [L × K' (1, g') L × L'] = [K × K' (1, g') K × L'] ∘ [K × L' (g, 1) L × L']`. -/
theorem heckeOperator_left_comp_right_comm :
    (heckeOperator ρ (prod K K') (prod L K') (g, 1)).comp
        (heckeOperator ρ (prod L K') (prod L L') (1, g')) =
      (heckeOperator ρ (prod K K') (prod K L') (1, g')).comp
        (heckeOperator ρ (prod K L') (prod L L') (g, 1)) :=
  LinearMap.ext fun v =>
    (heckeOperator_prod_eq_left_comp_right ρ K L g K' L' g' v).symm.trans
      (heckeOperator_prod_eq_right_comp_left ρ K L g K' L' g' v)

end General

/-! ## The representation of the second factor away from a fixed first level -/

section Away

omit [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace H'] [IsTopologicalGroup H'] in
theorem map_inr_mem_fixedVectors (S : Subgroup H) (h' : H') {v : V}
    (hv : v ∈ fixedVectors ρ (S.prod ⊥)) : ρ (1, h') v ∈ fixedVectors ρ (S.prod ⊥) := by
  intro k
  have hk : ((k : H × H').2 : H') = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp k.property).2
  have e : (k : H × H') * (1, h') = (1, h') * (k : H × H') :=
    Prod.ext (by simp) (by simp [hk])
  change ρ (k : H × H') (ρ (1, h') v) = ρ (1, h') v
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
  exact congrArg (ρ (1, h')) (hv k)

/-- The representation of `H'` on the vectors fixed by `S × 1`, through `h' ↦ ρ(1, h')`. -/
def awayRep (S : Subgroup H) : Representation R H' (fixedVectors ρ (S.prod ⊥)) where
  toFun h' := (ρ (1, h')).restrict fun _ hv => map_inr_mem_fixedVectors ρ S h' hv
  map_one' := by
    ext v
    change ρ 1 (v : V) = v
    rw [map_one, Module.End.one_apply]
  map_mul' a b := by
    ext v
    change ρ (1, a * b) (v : V) = ρ (1, a) (ρ (1, b) v)
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

omit [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace H'] [IsTopologicalGroup H'] in
@[simp] theorem coe_awayRep_apply (S : Subgroup H) (h' : H')
    (v : fixedVectors ρ (S.prod ⊥)) : (awayRep ρ S h' v : V) = ρ (1, h') v := rfl

omit [IsTopologicalGroup H] [IsTopologicalGroup H'] in
variable {ρ} in
/-- Smoothness passes to the representation away from `S`: an open subgroup of `H × H'` fixing a
vector contains `1 × U'` for the open subgroup `U'` of `H'` it pulls back to. -/
theorem isSmooth_awayRep (hρ : IsSmooth ρ) (S : Subgroup H) : IsSmooth (awayRep ρ S) := by
  intro v
  obtain ⟨U, hU⟩ := hρ (v : V)
  exact ⟨U.comap (MonoidHom.inr H H') (continuous_const.prodMk continuous_id),
    fun k => Subtype.ext (hU ⟨(1, k), k.property⟩)⟩

variable {W : Type w} [AddCommGroup W] [Module R W] {σ : Representation R (H × H') W}

variable {ρ} in
/-- An intertwiner restricted to the vectors fixed by `S × 1`, as an intertwiner of the
representations of `H'`. -/
def awayMap (f : ρ.IntertwiningMap σ) (S : Subgroup H) :
    (awayRep ρ S).IntertwiningMap (awayRep σ S) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (awayRep ρ S) (awayRep σ S)
    (fixedVectorsMap f (S.prod ⊥)) fun h' v =>
      Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ f (1, h') (v : V))

omit [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace H'] [IsTopologicalGroup H'] in
variable {ρ} in
@[simp] theorem coe_awayMap_apply (f : ρ.IntertwiningMap σ) (S : Subgroup H)
    (v : fixedVectors ρ (S.prod ⊥)) : (awayMap f S v : W) = f v := rfl

variable (K₀ : CompactOpenLevel H)

/-- The `K'`-fixed vectors of the representation away from `K₀` are the `K₀ × K'`-fixed vectors. -/
def awayFixedEquiv (K' : CompactOpenLevel H') :
    fixedVectors (awayRep ρ K₀.subgroup) K'.subgroup ≃ₗ[R] fixedVectors ρ (prod K₀ K').subgroup where
  toFun w := ⟨(w : fixedVectors ρ (K₀.subgroup.prod ⊥)), fun k => by
    have hk := mem_prod.mp k.property
    have e : (k : H × H') = ((k : H × H').1, 1) * (1, (k : H × H').2) := by simp
    change ρ (k : H × H') (w : fixedVectors ρ (K₀.subgroup.prod ⊥)) = w
    rw [e, map_mul, Module.End.mul_apply]
    have h₂ : ρ (1, (k : H × H').2) (w : fixedVectors ρ (K₀.subgroup.prod ⊥)) = w :=
      congrArg Subtype.val (w.property ⟨_, hk.2⟩)
    rw [h₂]
    exact (w : fixedVectors ρ (K₀.subgroup.prod ⊥)).property
      ⟨((k : H × H').1, 1), Subgroup.mem_prod.mpr ⟨hk.1, Subgroup.mem_bot.mpr rfl⟩⟩⟩
  invFun v := ⟨⟨v, fun k => by
      have hk := Subgroup.mem_prod.mp k.property
      have h1 : ((k : H × H').2 : H') = 1 := Subgroup.mem_bot.mp hk.2
      exact v.property ⟨k, mem_prod.mpr ⟨hk.1, h1 ▸ K'.subgroup.one_mem⟩⟩⟩,
    fun k' => Subtype.ext (v.property ⟨(1, k'), mem_prod.mpr ⟨K₀.subgroup.one_mem, k'.property⟩⟩)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsTopologicalGroup H] [IsTopologicalGroup H'] in
@[simp] theorem coe_awayFixedEquiv_apply (K' : CompactOpenLevel H')
    (w : fixedVectors (awayRep ρ K₀.subgroup) K'.subgroup) :
    (awayFixedEquiv ρ K₀ K' w : V) = ((w : fixedVectors ρ (K₀.subgroup.prod ⊥)) : V) := rfl

omit [IsTopologicalGroup H] [IsTopologicalGroup H'] in
@[simp] theorem coe_awayFixedEquiv_symm_apply (K' : CompactOpenLevel H')
    (v : fixedVectors ρ (prod K₀ K').subgroup) :
    (((awayFixedEquiv ρ K₀ K').symm v : fixedVectors ρ (K₀.subgroup.prod ⊥)) : V) = v := rfl

/-- Under `awayFixedEquiv`, the double-coset operator `[K' g' L']` of the representation away
from `K₀` is the operator `[K₀ × K' (1, g') K₀ × L']` of `ρ`. -/
theorem awayFixedEquiv_heckeOperator (K' L' : CompactOpenLevel H') (g' : H')
    (w : fixedVectors (awayRep ρ K₀.subgroup) L'.subgroup) :
    awayFixedEquiv ρ K₀ K' (heckeOperator (awayRep ρ K₀.subgroup) K' L' g' w) =
      heckeOperator ρ (prod K₀ K') (prod K₀ L') (1, g') (awayFixedEquiv ρ K₀ L' w) := by
  apply Subtype.ext
  rw [coe_awayFixedEquiv_apply, heckeOperator_apply, Submodule.coe_sum, heckeOperator_prod_apply,
    Fintype.sum_subsingleton _ ((1 : K₀.subgroup) : HeckeCosets K₀ K₀ 1)]
  refine Fintype.sum_congr _ _ fun q' => ?_
  induction q' using QuotientGroup.induction_on with
  | H a' =>
    rw [cosetTerm_prod_symm_mk, cosetTerm_mk, coe_awayRep_apply, coe_awayFixedEquiv_apply]
    simp only [OneMemClass.coe_one, mul_one]

theorem awayFixedEquiv_comp_heckeOperator (K' L' : CompactOpenLevel H') (g' : H') :
    (awayFixedEquiv ρ K₀ K').toLinearMap ∘ₗ heckeOperator (awayRep ρ K₀.subgroup) K' L' g' =
      heckeOperator ρ (prod K₀ K') (prod K₀ L') (1, g') ∘ₗ (awayFixedEquiv ρ K₀ L').toLinearMap :=
  LinearMap.ext (awayFixedEquiv_heckeOperator ρ K₀ K' L' g')

end Away

end Operator

/-! ## Smooth representations -/

section Smooth

variable (R : Type t) [CommRing R] (K₀ : CompactOpenLevel H)

/-- The vectors fixed by `K₀ × 1`, as a smooth representation of `H'`. -/
def awayFunctor : SmoothRep.{t, max v v', w} R (H × H') ⥤ SmoothRep.{t, v', w} R H' where
  obj A := SmoothRep.of (awayRep A.representation K₀.subgroup)
    (isSmooth_awayRep A.isSmooth K₀.subgroup)
  map f := SmoothRep.ofHom (awayMap (SmoothRep.hom f) K₀.subgroup)
  map_id _ := rfl
  map_comp _ _ := rfl

omit [IsTopologicalGroup H] [IsTopologicalGroup H'] in
@[simp] theorem awayFunctor_obj_representation (A : SmoothRep.{t, max v v', w} R (H × H')) :
    ((awayFunctor R K₀).obj A).representation = awayRep A.representation K₀.subgroup := rfl

/-- `K'`-fixed vectors away from `K₀` are naturally the `K₀ × K'`-fixed vectors. -/
def awayFixedIso (K' : CompactOpenLevel H') :
    awayFunctor R K₀ ⋙ fixedVectorsFunctor R K'.subgroup ≅
      fixedVectorsFunctor R (prod K₀ K').subgroup :=
  NatIso.ofComponents (fun A => (awayFixedEquiv A.representation K₀ K').toModuleIso)
    fun _ => rfl

omit [IsTopologicalGroup H] [IsTopologicalGroup H'] in
@[simp] theorem awayFixedIso_hom_app (K' : CompactOpenLevel H')
    (A : SmoothRep.{t, max v v', w} R (H × H')) :
    (awayFixedIso R K₀ K').hom.app A =
      ModuleCat.ofHom (awayFixedEquiv A.representation K₀ K').toLinearMap := rfl

/-- The Hecke operators `[K' g' L']` away from `K₀` are the operators `[K₀ × K' (1, g') K₀ × L']`,
naturally in the smooth representation. -/
theorem awayFixedIso_heckeNatTrans (K' L' : CompactOpenLevel H') (g' : H') :
    Functor.whiskerLeft (awayFunctor R K₀) (heckeNatTrans R K' L' g') ≫
        (awayFixedIso R K₀ K').hom =
      (awayFixedIso R K₀ L').hom ≫ heckeNatTrans R (prod K₀ K') (prod K₀ L') (1, g') := by
  ext A : 2
  exact ModuleCat.hom_ext (awayFixedEquiv_comp_heckeOperator A.representation K₀ K' L' g')

end Smooth

/-! ## Partial colimits -/

section PartialTower

open CategoryTheory.Limits Opposite

variable {R : Type t} [CommRing R]
  [HasColimitsOfShape (Ordered H')ᵒᵖ (ModuleCat.{w} R)]
  [HasColimitsOfShape (Ordered (H × H'))ᵒᵖ (ModuleCat.{w} R)] [Nonempty (CompactOpenLevel H')]
  (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ ModuleCat.{w} R) (hF : LevelColimit.IsLevelTrivial F)
  (K₀ : CompactOpenLevel H)

/-- The comparison map from the partial colimit at `K₀` lands in the vectors fixed by `K₀ × 1`. -/
theorem reindexComparison_withLeft_apply_mem
    (x : (colimit (LevelColimit.diagram (LevelColimit.partialTower K₀ F)) : ModuleCat.{w} R)) :
    (LevelColimit.reindexComparison (withLeft K₀) F).hom x ∈
      fixedVectors (LevelColimit.smoothRep F hF).obj.ρ (K₀.subgroup.prod ⊥) := by
  intro k
  have hk := Subgroup.mem_prod.mp k.property
  have e : (k : H × H') = ((k : H × H').1, 1) := Prod.ext rfl (Subgroup.mem_bot.mp hk.2)
  change (LevelColimit.translate F (k : H × H')).hom
      ((LevelColimit.reindexComparison (withLeft K₀) F).hom x) = _
  rw [e]
  exact LevelColimit.translate_partialComparison_apply_of_mem F hF K₀ hk.1 x

/-- The comparison from the partial colimit at `K₀` to the vectors of the colimit over all levels
fixed by `K₀ × 1`, as an intertwiner of representations of `H'`. -/
def partialAwayMap :
    (LevelColimit.smoothRep (LevelColimit.partialTower K₀ F)
        (LevelColimit.isLevelTrivial_partialTower K₀ hF)).obj.ρ.IntertwiningMap
      (awayRep (LevelColimit.smoothRep F hF).obj.ρ K₀.subgroup) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((LevelColimit.reindexComparison (withLeft K₀) F).hom.codRestrict _
      (reindexComparison_withLeft_apply_mem F hF K₀))
    fun h' x => Subtype.ext (congrArg (fun f => ModuleCat.Hom.hom f x)
      (LevelColimit.translate_reindexComparison (withLeft K₀) F h'))

@[simp] theorem coe_partialAwayMap_apply
    (x : (colimit (LevelColimit.diagram (LevelColimit.partialTower K₀ F)) : ModuleCat.{w} R)) :
    (partialAwayMap F hF K₀ x : (LevelColimit.smoothRep F hF).obj.V) =
      (LevelColimit.reindexComparison (withLeft K₀) F).hom x := rfl

/-- The comparison as a morphism of smooth representations of `H'`. -/
def partialAwayHom :
    LevelColimit.smoothRep (LevelColimit.partialTower K₀ F)
        (LevelColimit.isLevelTrivial_partialTower K₀ hF) ⟶
      (awayFunctor R K₀).obj (LevelColimit.smoothRep F hF) :=
  SmoothRep.ofHom (partialAwayMap F hF K₀)

/-- A class of level `K'` of the partial tower goes to the class of level `K₀ × K'`. -/
theorem awayFixedEquiv_partialAwayMap_levelClass (K' : CompactOpenLevel H')
    (x : F.obj (op (prod K₀ K'))) :
    awayFixedEquiv (LevelColimit.smoothRep F hF).obj.ρ K₀ K'
        (fixedVectorsMap (partialAwayMap F hF K₀) K'.subgroup
          (levelClass (LevelColimit.partialTower K₀ F)
            (LevelColimit.isLevelTrivial_partialTower K₀ hF) K' x)) =
      levelClass F hF (prod K₀ K') x :=
  Subtype.ext (LevelColimit.reindexComparison_ι_apply (withLeft K₀) F K' x)

/-- The comparison intertwines the double-coset operator `[K' g' L']` of the partial colimit at
`K₀` with the operator `[K₀ × K' (1, g') K₀ × L']` of the colimit over all levels. -/
theorem awayFixedEquiv_partialAwayMap_heckeOperator (K' L' : CompactOpenLevel H') (g' : H')
    (v : fixedVectors (LevelColimit.smoothRep (LevelColimit.partialTower K₀ F)
      (LevelColimit.isLevelTrivial_partialTower K₀ hF)).obj.ρ L'.subgroup) :
    awayFixedEquiv (LevelColimit.smoothRep F hF).obj.ρ K₀ K'
        (fixedVectorsMap (partialAwayMap F hF K₀) K'.subgroup
          (heckeOperator (LevelColimit.smoothRep (LevelColimit.partialTower K₀ F)
            (LevelColimit.isLevelTrivial_partialTower K₀ hF)).obj.ρ K' L' g' v)) =
      heckeOperator (LevelColimit.smoothRep F hF).obj.ρ (prod K₀ K') (prod K₀ L') (1, g')
        (awayFixedEquiv (LevelColimit.smoothRep F hF).obj.ρ K₀ L'
          (fixedVectorsMap (partialAwayMap F hF K₀) L'.subgroup v)) := by
  rw [← awayFixedEquiv_heckeOperator]
  congr 1
  exact LinearMap.congr_fun (fixedVectorsMap_heckeOperator K' L' g' (partialAwayMap F hF K₀)) v

end PartialTower

end Langlands.Shimura.LevelHecke
