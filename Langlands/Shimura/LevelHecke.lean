import Langlands.Shimura.LevelColimit
import Langlands.Representation.Smooth.FixedVectors.Definitions

/-! # Double-coset operators on fixed vectors for compact open levels -/

noncomputable section

universe t v w u w'

set_option autoImplicit false

namespace Langlands.Shimura.LevelHecke

open CategoryTheory CategoryTheory.Limits Opposite CompactOpenLevel

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ## The cosets `K / (K ∩ g L g⁻¹)` -/

theorem mem_heckeLevel {K L : CompactOpenLevel G} {g x : G} :
    x ∈ (heckeLevel K L g).subgroup ↔ x ∈ K.subgroup ∧ g⁻¹ * x * g ∈ L.subgroup := by
  change x ∈ K.subgroup ∧ g⁻¹ * x * g⁻¹⁻¹ ∈ L.subgroup ↔ _
  rw [inv_inv]

section Cosets

variable (K L : CompactOpenLevel G) (g : G)

/-- The left cosets of the level `K ∩ g L g⁻¹` in `K`. -/
abbrev HeckeCosets : Type v :=
  K.subgroup ⧸ (heckeLevel K L g).subgroup.subgroupOf K.subgroup

/-- There are finitely many cosets, since `K` is compact and `K ∩ g L g⁻¹` is open in it. -/
instance finite_heckeCosets : Finite (HeckeCosets K L g) := by
  have : CompactSpace K.subgroup := isCompact_iff_compactSpace.mp K.isCompact
  exact Subgroup.quotient_finite_of_isOpen _
    (Subgroup.subgroupOf_isOpen K.subgroup _ (heckeLevel K L g).openSubgroup.isOpen)

instance fintype_heckeCosets : Fintype (HeckeCosets K L g) := Fintype.ofFinite _

end Cosets

/-! ## The operator on fixed vectors -/

section Operator

variable {R : Type t} [CommRing R] {V : Type w} [AddCommGroup V] [Module R V]
variable (ρ : Representation R G V) (K L : CompactOpenLevel G) (g : G)

variable {K L g} in
/-- For `v` fixed by `L` and `m ∈ K ∩ g L g⁻¹`, `ρ(k m g) v = ρ(k g) v`. -/
theorem map_mul_mem_heckeLevel (k : G) {m : G} (hm : m ∈ (heckeLevel K L g).subgroup) {v : V}
    (hv : v ∈ fixedVectors ρ L.subgroup) : ρ (k * m * g) v = ρ (k * g) v := by
  have hL : g⁻¹ * m * g ∈ L.subgroup := (mem_heckeLevel.mp hm).2
  have e : k * m * g = (k * g) * (g⁻¹ * m * g) := by group
  rw [e, map_mul, Module.End.mul_apply]
  exact congrArg (ρ (k * g)) (hv ⟨_, hL⟩)

/-- The vector `ρ(k g) v` attached to the coset of `k`, for `v` fixed by `L`; it does not
depend on the representative `k`. -/
def cosetTerm (v : fixedVectors ρ L.subgroup) (q : HeckeCosets K L g) : V :=
  Quotient.liftOn' q (fun k : K.subgroup => ρ ((k : G) * g) v) (fun a b hab => by
    have hm : ((a⁻¹ * b : K.subgroup) : G) ∈ (heckeLevel K L g).subgroup :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.leftRel_apply).mp hab)
    have e : (a : G) * ((a⁻¹ * b : K.subgroup) : G) = b := by simp
    change ρ ((a : G) * g) v = ρ ((b : G) * g) v
    rw [← map_mul_mem_heckeLevel ρ (a : G) hm v.property, e])

@[simp] theorem cosetTerm_mk (v : fixedVectors ρ L.subgroup) (k : K.subgroup) :
    cosetTerm ρ K L g v (k : HeckeCosets K L g) = ρ ((k : G) * g) v := rfl

theorem cosetTerm_eq_out (v : fixedVectors ρ L.subgroup) (q : HeckeCosets K L g) :
    cosetTerm ρ K L g v q = ρ ((q.out : G) * g) v := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

theorem cosetTerm_add (v w : fixedVectors ρ L.subgroup) (q : HeckeCosets K L g) :
    cosetTerm ρ K L g (v + w) q = cosetTerm ρ K L g v q + cosetTerm ρ K L g w q := by
  induction q using QuotientGroup.induction_on with
  | H k => exact map_add (ρ ((k : G) * g)) (v : V) (w : V)

theorem cosetTerm_smul (r : R) (v : fixedVectors ρ L.subgroup) (q : HeckeCosets K L g) :
    cosetTerm ρ K L g (r • v) q = r • cosetTerm ρ K L g v q := by
  induction q using QuotientGroup.induction_on with
  | H k => exact map_smul (ρ ((k : G) * g)) r (v : V)

/-- Translating by `k ∈ K` permutes the coset terms. -/
theorem map_cosetTerm (v : fixedVectors ρ L.subgroup) (k : K.subgroup) (q : HeckeCosets K L g) :
    ρ (k : G) (cosetTerm ρ K L g v q) = cosetTerm ρ K L g v (k • q) := by
  induction q using QuotientGroup.induction_on with
  | H a =>
    change ρ (k : G) (ρ ((a : G) * g) v) = ρ (((k * a : K.subgroup) : G) * g) v
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_mul, mul_assoc]

/-- The sum of the coset terms is fixed by `K`. -/
theorem sum_cosetTerm_mem (v : fixedVectors ρ L.subgroup) :
    ∑ q, cosetTerm ρ K L g v q ∈ fixedVectors ρ K.subgroup := by
  intro k
  change ρ (k : G) (∑ q, cosetTerm ρ K L g v q) = ∑ q, cosetTerm ρ K L g v q
  rw [map_sum]
  simp_rw [map_cosetTerm]
  exact Fintype.sum_equiv (MulAction.toPerm k) _ _ (fun _ => rfl)

/-- The double-coset operator `[K g L] : V^L → V^K`, sending `v` to
`∑_{k ∈ K / (K ∩ g L g⁻¹)} ρ(k g) v`. -/
def heckeOperator : fixedVectors ρ L.subgroup →ₗ[R] fixedVectors ρ K.subgroup where
  toFun v := ⟨∑ q, cosetTerm ρ K L g v q, sum_cosetTerm_mem ρ K L g v⟩
  map_add' v w := by
    apply Subtype.ext
    simp only [Submodule.coe_add, cosetTerm_add, Finset.sum_add_distrib]
  map_smul' r v := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, cosetTerm_smul, RingHom.id_apply, Finset.smul_sum]

theorem heckeOperator_apply (v : fixedVectors ρ L.subgroup) :
    (heckeOperator ρ K L g v : V) = ∑ q, cosetTerm ρ K L g v q := rfl

/-- The operator in terms of chosen coset representatives. -/
theorem heckeOperator_apply_out (v : fixedVectors ρ L.subgroup) :
    (heckeOperator ρ K L g v : V) = ∑ q : HeckeCosets K L g, ρ ((q.out : G) * g) v :=
  Finset.sum_congr rfl fun q _ => cosetTerm_eq_out ρ K L g v q

variable {K L} in
/-- If `K ⊆ L`, the operator `[K 1 L]` is the inclusion `V^L ⊆ V^K`. -/
theorem heckeOperator_one_of_le (h : K.subgroup ≤ L.subgroup) (v : fixedVectors ρ L.subgroup) :
    (heckeOperator ρ K L 1 v : V) = v := by
  have : Subsingleton (HeckeCosets K L 1) := ⟨fun q₁ q₂ => by
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
      induction q₂ using QuotientGroup.induction_on with
      | H b =>
        apply QuotientGroup.eq.mpr
        apply Subgroup.mem_subgroupOf.mpr
        apply mem_heckeLevel.mpr
        refine ⟨(a⁻¹ * b).property, ?_⟩
        simpa using h (a⁻¹ * b).property⟩
  rw [heckeOperator_apply, Fintype.sum_subsingleton _ ((1 : K.subgroup) : HeckeCosets K L 1),
    cosetTerm_mk]
  simp

/-- The operator `[K 1 K]` is the identity. -/
theorem heckeOperator_self : heckeOperator ρ K K 1 = LinearMap.id :=
  LinearMap.ext fun v => Subtype.ext (heckeOperator_one_of_le ρ le_rfl v)

variable {K L} in
/-- Replacing `g` by `g l` with `l ∈ L` does not change the operator. -/
theorem heckeOperator_mul_right {l : G} (hl : l ∈ L.subgroup) :
    heckeOperator ρ K L (g * l) = heckeOperator ρ K L g := by
  have hH : (heckeLevel K L (g * l)).subgroup = (heckeLevel K L g).subgroup := by
    ext x
    rw [mem_heckeLevel, mem_heckeLevel]
    have e : (g * l)⁻¹ * x * (g * l) = l⁻¹ * (g⁻¹ * x * g) * l := by group
    rw [e]
    refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
    · have h' := L.subgroup.mul_mem (L.subgroup.mul_mem hl h) (L.subgroup.inv_mem hl)
      simpa [mul_assoc] using h'
    · exact L.subgroup.mul_mem (L.subgroup.mul_mem (L.subgroup.inv_mem hl) h) hl
  have hH' : (heckeLevel K L (g * l)).subgroup.subgroupOf K.subgroup =
      (heckeLevel K L g).subgroup.subgroupOf K.subgroup := by
    rw [hH]
  let e : HeckeCosets K L (g * l) ≃ HeckeCosets K L g := Subgroup.quotientEquivOfEq hH'
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change ∑ q, cosetTerm ρ K L (g * l) v q = ∑ q, cosetTerm ρ K L g v q
  refine Fintype.sum_equiv e _ _ (fun q => ?_)
  induction q using QuotientGroup.induction_on with
  | H k =>
    change ρ ((k : G) * (g * l)) v = ρ ((k : G) * g) v
    rw [← mul_assoc, map_mul, Module.End.mul_apply]
    exact congrArg (ρ ((k : G) * g)) (v.property ⟨l, hl⟩)

variable {K L} in
/-- Replacing `g` by `k g` with `k ∈ K` does not change the operator: right multiplication by
`k` identifies the cosets of `K ∩ (k g) L (k g)⁻¹` with those of `K ∩ g L g⁻¹`. -/
theorem heckeOperator_mul_left {k : G} (hk : k ∈ K.subgroup) :
    heckeOperator ρ K L (k * g) = heckeOperator ρ K L g := by
  let e : HeckeCosets K L (k * g) ≃ HeckeCosets K L g :=
    Quotient.congr (Equiv.mulRight (⟨k, hk⟩ : K.subgroup)) (fun a b => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf, mem_heckeLevel, mem_heckeLevel]
      have e : (k * g)⁻¹ * ((a⁻¹ * b : K.subgroup) : G) * (k * g) =
          g⁻¹ * (((Equiv.mulRight (⟨k, hk⟩ : K.subgroup) a)⁻¹ *
            Equiv.mulRight (⟨k, hk⟩ : K.subgroup) b : K.subgroup) : G) * g := by
        simp only [Equiv.coe_mulRight, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact ⟨fun h => ⟨(_ : K.subgroup).property, h.2⟩, fun h => ⟨(a⁻¹ * b).property, h.2⟩⟩)
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change ∑ q, cosetTerm ρ K L (k * g) v q = ∑ q, cosetTerm ρ K L g v q
  refine Fintype.sum_equiv e _ _ (fun q => ?_)
  induction q using QuotientGroup.induction_on with
  | H a =>
    change ρ ((a : G) * (k * g)) v = ρ (((a * ⟨k, hk⟩ : K.subgroup) : G) * g) v
    rw [Subgroup.coe_mul, Subgroup.coe_mk, mul_assoc]

variable {K L} in
/-- The operator depends only on the double coset `K g L`. -/
theorem heckeOperator_mul_mul {k l : G} (hk : k ∈ K.subgroup) (hl : l ∈ L.subgroup) :
    heckeOperator ρ K L (k * g * l) = heckeOperator ρ K L g := by
  rw [heckeOperator_mul_right ρ _ hl, heckeOperator_mul_left ρ g hk]

variable {ρ} {W : Type w'} [AddCommGroup W] [Module R W] {σ : Representation R G W}

/-- The operator commutes with intertwining maps. -/
theorem fixedVectorsMap_heckeOperator (f : ρ.IntertwiningMap σ) :
    (fixedVectorsMap f K.subgroup).comp (heckeOperator ρ K L g) =
      (heckeOperator σ K L g).comp (fixedVectorsMap f L.subgroup) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change f (∑ q, cosetTerm ρ K L g v q) = ∑ q, cosetTerm σ K L g (fixedVectorsMap f L.subgroup v) q
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  induction q using QuotientGroup.induction_on with
  | H k => exact Representation.IntertwiningMap.isIntertwining _ _ f ((k : G) * g) (v : V)

end Operator

/-! ## Smooth representations -/

section Smooth

variable {R : Type t} [CommRing R] (K L : CompactOpenLevel G) (g : G)

omit [IsTopologicalGroup G] in
variable (R) in
/-- The vectors fixed by a subgroup, as a functor on smooth representations. -/
def fixedVectorsFunctor (H : Subgroup G) : SmoothRep.{t, v, w} R G ⥤ ModuleCat.{w} R where
  obj A := ModuleCat.of R (fixedVectors A.obj.ρ H)
  map f := ModuleCat.ofHom (fixedVectorsMap f.hom.hom H)
  map_id _ := rfl
  map_comp _ _ := rfl

omit [IsTopologicalGroup G] in
@[simp] theorem fixedVectorsFunctor_obj (H : Subgroup G) (A : SmoothRep.{t, v, w} R G) :
    (fixedVectorsFunctor R H).obj A = ModuleCat.of R (fixedVectors A.obj.ρ H) := rfl

variable (R) in
/-- The double-coset operators `[K g L]`, as a natural transformation from `L`-fixed vectors
to `K`-fixed vectors of smooth representations. -/
def heckeNatTrans :
    fixedVectorsFunctor.{t, v, w} R L.subgroup ⟶ fixedVectorsFunctor R K.subgroup where
  app A := ModuleCat.ofHom (heckeOperator A.obj.ρ K L g)
  naturality _ _ f :=
    ModuleCat.hom_ext (fixedVectorsMap_heckeOperator K L g f.hom.hom).symm

@[simp] theorem heckeNatTrans_app (A : SmoothRep.{t, v, w} R G) :
    (heckeNatTrans R K L g).app A = ModuleCat.ofHom (heckeOperator A.obj.ρ K L g) := rfl

theorem heckeNatTrans_self : heckeNatTrans.{t, v, w} R K K 1 = 𝟙 _ := by
  apply NatTrans.ext
  funext A
  apply ModuleCat.hom_ext
  exact heckeOperator_self A.obj.ρ K

end Smooth

/-! ## Level classes in colimits over levels -/

section LevelColimit

variable {R : Type t} [CommRing R]
variable [HasColimitsOfShape (Ordered G)ᵒᵖ (ModuleCat.{w} R)]
variable (F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R) (hF : LevelColimit.IsLevelTrivial F)
variable (K L : CompactOpenLevel G) (g : G)

/-- The image of a class of level `K` in the colimit over levels is fixed by `K`. -/
theorem ι_apply_mem_fixedVectors (K : CompactOpenLevel G) (x : F.obj (op K)) :
    (LevelColimit.ι F K).hom x ∈
      fixedVectors (LevelColimit.smoothRep (G := G) (R := R) F hF).obj.ρ K.subgroup :=
  fun k => LevelColimit.translate_ι_apply_of_mem F hF k.property x

/-- The map from level `K` to the `K`-fixed vectors of the colimit over levels. -/
def levelClass (K : CompactOpenLevel G) :
    F.obj (op K) →ₗ[R] fixedVectors (LevelColimit.smoothRep (G := G) (R := R) F hF).obj.ρ
      K.subgroup :=
  (LevelColimit.ι F K).hom.codRestrict _ (ι_apply_mem_fixedVectors F hF K)

@[simp] theorem levelClass_apply_coe (K : CompactOpenLevel G) (x : F.obj (op K)) :
    (levelClass F hF K x : (LevelColimit.smoothRep (G := G) (R := R) F hF).obj.V) =
      (LevelColimit.ι F K).hom x := rfl

/-- The double-coset operator `[K g L]` on the image of a class `x` of level `L`: the sum over
`k ∈ K / (K ∩ g L g⁻¹)` of the images at the levels `(k g) L (k g)⁻¹` of the transports of
`x` along `(k g) L (k g)⁻¹ ⟶ L`. -/
theorem heckeOperator_levelClass (x : F.obj (op L)) :
    (heckeOperator (LevelColimit.smoothRep (G := G) (R := R) F hF).obj.ρ K L g
        (levelClass F hF L x) : (LevelColimit.smoothRep (G := G) (R := R) F hF).obj.V) =
      ∑ q : HeckeCosets K L g,
        (LevelColimit.ι F (conjLevel ((q.out : G) * g) L)).hom
          ((F.map (conjArrow ((q.out : G) * g) L).op).hom x) := by
  rw [heckeOperator_apply_out]
  exact Finset.sum_congr rfl fun q _ => LevelColimit.smoothRep_ρ_ι_apply F hF _ L x

end LevelColimit

end Langlands.Shimura.LevelHecke
