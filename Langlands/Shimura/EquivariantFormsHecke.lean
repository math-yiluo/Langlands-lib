import Langlands.Shimura.EquivariantForms
import Langlands.Shimura.Levels

/-!
# Level maps and Hecke operators on equivariant functions

This file adds maps between the modules `forms ι K ρ` of
`Langlands.Shimura.EquivariantForms` for different levels `K`.

## Main definitions

* `restrict ι ρ hle`: for `K' ≤ K`, forms of level `K` are forms of level `K'`.
* `trace ι ρ hle`: for `K' ≤ K` of finite index, `(trace f) g = ∑ ρ k (f (g * k))` over
  representatives `k` of `K ⧸ K'`; `trace_restrict` shows that trace after restriction is
  multiplication by the index.
* `transport ι ρ σ g hg φ hφ`: for `g⁻¹ K g ⊆ L` and a linear map `φ` intertwining `σ` (on `L`)
  conjugated by `g` with `ρ` (on `K`), `f ↦ (x ↦ φ (f (x * g)))` from level `L` to level `K`.
* `levelPresheaf R ι ρ`: for a representation `ρ` of a topological group `G`, the forms of all
  levels `CompactOpenLevel G` as a presheaf of `R`-modules, with `levelTransport` along the
  arrows of `Langlands.Shimura.CompactOpenLevel`.
* `hecke` and `heckeOperator`: the Hecke operator of the double coset `K g L` of compact open
  levels, transport along `g` to the level `K ∩ g L g⁻¹` (`CompactOpenLevel.heckeLevel`)
  followed by the trace to `K`, with the formula `([K g L] f) x = ∑ ρ (k g) (f (x k g))`
  (`heckeOperator_apply_coe`).
-/

noncomputable section

namespace Langlands.Shimura.EquivariantForms

open CategoryTheory

universe t uR uΓ uG

variable {R : Type uR} [CommRing R] {Γ : Type uΓ} {G : Type uG} [Group Γ] [Group G]

section Restrict

variable (ι : Γ →* G) {K K' : Subgroup G} {V : Type*} [AddCommGroup V] [Module R V]
  (ρ : Representation R K V) (hle : K' ≤ K)

/-- Restriction from level `K` to a smaller level `K'`: the underlying function is unchanged
and the representation is restricted along the inclusion `K' ≤ K`. -/
def restrict : forms ι K ρ →ₗ[R] forms ι K' (ρ.comp (Subgroup.inclusion hle)) where
  toFun f := ⟨f.1, f.2.1, fun g k' => f.2.2 g (Subgroup.inclusion hle k')⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma restrict_apply_coe (f : forms ι K ρ) (g : G) : (restrict ι ρ hle f).1 g = f.1 g :=
  rfl

end Restrict

section Trace

variable (ι : Γ →* G) {K K' : Subgroup G} {V : Type*} [AddCommGroup V] [Module R V]
  (ρ : Representation R K V) (hle : K' ≤ K)

/-- For `k : K`, the linear map sending a form `f` of level `K'` to the function
`g ↦ ρ k (f (g * k))`. -/
def translateTwist (k : K) : forms ι K' (ρ.comp (Subgroup.inclusion hle)) →ₗ[R] G → V :=
  (ρ k).compLeft G ∘ₗ LinearMap.funLeft R V (· * (k : G)) ∘ₗ Submodule.subtype _

@[simp]
lemma translateTwist_apply (k : K) (f : forms ι K' (ρ.comp (Subgroup.inclusion hle))) (g : G) :
    translateTwist ι ρ hle k f g = ρ k (f.1 (g * k)) :=
  rfl

/-- `translateTwist` is constant on left cosets of `K'`: for `m ∈ K'`,
`ρ (k m) (f (g k m)) = ρ (k m) (ρ m⁻¹ (f (g k))) = ρ k (f (g k))`. -/
lemma translateTwist_mul (k : K) (m : K'.subgroupOf K) :
    translateTwist ι ρ hle (k * m) = translateTwist ι ρ hle k := by
  ext f g
  have hm : ((m : K) : G) ∈ K' := Subgroup.mem_subgroupOf.1 m.2
  have hg : g * ((k * m : K) : G) = g * k * ((⟨_, hm⟩ : K') : G) := by simp [mul_assoc]
  simp only [translateTwist_apply]
  rw [hg, f.2.2 (g * k) ⟨_, hm⟩]
  change ρ (k * m) (ρ (Subgroup.inclusion hle ⟨_, hm⟩⁻¹) _) = _
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  ext
  simp

/-- The map `translateTwist k` depends only on the coset `k K'` in `K ⧸ K'`. -/
def cosetTwist (q : K ⧸ K'.subgroupOf K) :
    forms ι K' (ρ.comp (Subgroup.inclusion hle)) →ₗ[R] G → V :=
  Quotient.liftOn' q (translateTwist ι ρ hle) fun a b h => by
    have := translateTwist_mul ι ρ hle a ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.1 h⟩
    simpa using this.symm

@[simp]
lemma cosetTwist_mk (k : K) :
    cosetTwist ι ρ hle (QuotientGroup.mk k) = translateTwist ι ρ hle k :=
  rfl

/-- Each coset term is left invariant under `ι Γ`. -/
lemma cosetTwist_left (q : K ⧸ K'.subgroupOf K) (f : forms ι K' (ρ.comp (Subgroup.inclusion hle)))
    (γ : Γ) (g : G) : cosetTwist ι ρ hle q f (ι γ * g) = cosetTwist ι ρ hle q f g := by
  induction q using QuotientGroup.induction_on with
  | H k => simp [mul_assoc, f.2.1 γ (g * k)]

/-- Right translation by `k₀ : K` moves the coset term to the coset `k₀ • q`, twisted by
`ρ k₀⁻¹`. -/
lemma cosetTwist_right (q : K ⧸ K'.subgroupOf K)
    (f : forms ι K' (ρ.comp (Subgroup.inclusion hle))) (g : G) (k₀ : K) :
    cosetTwist ι ρ hle q f (g * k₀) = ρ k₀⁻¹ (cosetTwist ι ρ hle (k₀ • q) f g) := by
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [MulAction.Quotient.smul_mk, cosetTwist_mk, cosetTwist_mk, translateTwist_apply,
      translateTwist_apply, ← Module.End.mul_apply, ← map_mul, smul_eq_mul,
      inv_mul_cancel_left, Subgroup.coe_mul, mul_assoc]

variable [Finite (K ⧸ K'.subgroupOf K)]

/-- The trace from level `K'` to level `K`, for `K'` of finite index in `K`:
`(trace f) g = ∑ ρ k (f (g * k))`, summed over representatives `k` of the cosets `k K'` in
`K ⧸ K'`. -/
def trace : forms ι K' (ρ.comp (Subgroup.inclusion hle)) →ₗ[R] forms ι K ρ :=
  letI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  LinearMap.codRestrict (forms ι K ρ) (∑ q, cosetTwist ι ρ hle q) fun f => by
    refine ⟨fun γ g => ?_, fun g k₀ => ?_⟩
    · simp only [LinearMap.sum_apply, Finset.sum_apply, cosetTwist_left]
    · simp only [LinearMap.sum_apply, Finset.sum_apply, cosetTwist_right, map_sum]
      exact (Equiv.sum_comp (MulAction.toPerm k₀)
        (fun q => ρ k₀⁻¹ (cosetTwist ι ρ hle q f g))).trans rfl

/-- The trace as a sum of coset terms, for any `Fintype` instance on the cosets. -/
lemma trace_apply_coe [Fintype (K ⧸ K'.subgroupOf K)]
    (f : forms ι K' (ρ.comp (Subgroup.inclusion hle))) (g : G) :
    (trace ι ρ hle f).1 g = ∑ q, cosetTwist ι ρ hle q f g := by
  have h : (trace ι ρ hle f).1 g = @Finset.sum _ _ _
      (@Finset.univ _ (Fintype.ofFinite (K ⧸ K'.subgroupOf K))) (cosetTwist ι ρ hle) f g :=
    rfl
  rw [h, Subsingleton.elim (Fintype.ofFinite _) ‹Fintype (K ⧸ K'.subgroupOf K)›,
    LinearMap.sum_apply, Finset.sum_apply]

/-- The trace formula with chosen coset representatives `Quotient.out`. -/
lemma trace_apply_coe_out [Fintype (K ⧸ K'.subgroupOf K)]
    (f : forms ι K' (ρ.comp (Subgroup.inclusion hle))) (g : G) :
    (trace ι ρ hle f).1 g = ∑ q : K ⧸ K'.subgroupOf K, ρ q.out (f.1 (g * q.out)) := by
  rw [trace_apply_coe]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

/-- Trace after restriction is multiplication by the index `[K : K']`. -/
lemma trace_restrict (f : forms ι K ρ) :
    trace ι ρ hle (restrict ι ρ hle f) = (K'.subgroupOf K).index • f := by
  have := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  ext g
  rw [trace_apply_coe]
  have : ∀ q, cosetTwist ι ρ hle q (restrict ι ρ hle f) g = f.1 g := fun q => by
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [cosetTwist_mk, translateTwist_apply, restrict_apply_coe, f.2.2 g k,
        ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  simp only [this, Finset.sum_const, Finset.card_univ, Subgroup.index_eq_card,
    Nat.card_eq_fintype_card]
  rfl

/-- For `K'` normal in `K`, restricting the trace gives the sum of the translates of `f` under
the quotient action `levelQuotientAction` of `K ⧸ K'`. -/
lemma restrict_trace [(K'.subgroupOf K).Normal] [Fintype (K ⧸ K'.subgroupOf K)]
    (f : forms ι K' (ρ.comp (Subgroup.inclusion hle))) :
    restrict ι ρ hle (trace ι ρ hle f) = ∑ q, levelQuotientAction ι ρ hle q f := by
  ext g
  rw [restrict_apply_coe, trace_apply_coe, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  induction q using QuotientGroup.induction_on with
  | H k => rfl

end Trace

section Transport

variable (ι : Γ →* G) {K L M : Subgroup G} {V W U : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup U] [Module R U]
  (ρ : Representation R K V) (σ : Representation R L W) (τ : Representation R M U)

/-- Transport along `g : G` with `g⁻¹ K g ⊆ L`: given `φ : W → V` with
`φ (σ (g⁻¹ k g) w) = ρ k (φ w)`, the map `f ↦ (x ↦ φ (f (x * g)))` from forms of level `L` for
`σ` to forms of level `K` for `ρ`. -/
def transport (g : G) (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L) (φ : W →ₗ[R] V)
    (hφ : ∀ (k : K) (w : W), φ (σ ⟨g⁻¹ * k * g, hg k k.2⟩ w) = ρ k (φ w)) :
    forms ι L σ →ₗ[R] forms ι K ρ :=
  (φ.compLeft G ∘ₗ LinearMap.funLeft R W (· * g)).restrict fun f hf =>
    ⟨fun γ x => by simp [mul_assoc, hf.1 γ (x * g)], fun x k => by
      have hx : x * k * g = x * g * ((⟨g⁻¹ * k * g, hg k k.2⟩ : L) : G) := by
        simp [mul_assoc]
      have hl : (⟨g⁻¹ * k * g, hg k k.2⟩ : L)⁻¹ = ⟨g⁻¹ * (k⁻¹ : K) * g, hg _ (k⁻¹).2⟩ := by
        ext
        simp [mul_assoc]
      change φ (f (x * k * g)) = ρ k⁻¹ (φ (f (x * g)))
      rw [hx, hf.2, hl, hφ]⟩

@[simp]
lemma transport_apply_coe (g : G) (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L) (φ : W →ₗ[R] V)
    (hφ : ∀ (k : K) (w : W), φ (σ ⟨g⁻¹ * k * g, hg k k.2⟩ w) = ρ k (φ w))
    (f : forms ι L σ) (x : G) :
    (transport ι ρ σ g hg φ hφ f).1 x = φ (f.1 (x * g)) :=
  rfl

/-- Transports compose: along `h` and then along `g` is transport along `g * h` with the
composite intertwiner. -/
lemma transport_comp (g : G) (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L) (φ : W →ₗ[R] V)
    (hφ : ∀ (k : K) (w : W), φ (σ ⟨g⁻¹ * k * g, hg k k.2⟩ w) = ρ k (φ w))
    (h : G) (hh : ∀ l ∈ L, h⁻¹ * l * h ∈ M) (ψ : U →ₗ[R] W)
    (hψ : ∀ (l : L) (u : U), ψ (τ ⟨h⁻¹ * l * h, hh l l.2⟩ u) = σ l (ψ u))
    (hgh : ∀ k ∈ K, (g * h)⁻¹ * k * (g * h) ∈ M)
    (hφψ : ∀ (k : K) (u : U),
      (φ ∘ₗ ψ) (τ ⟨(g * h)⁻¹ * k * (g * h), hgh k k.2⟩ u) = ρ k ((φ ∘ₗ ψ) u)) :
    transport ι ρ σ g hg φ hφ ∘ₗ transport ι σ τ h hh ψ hψ =
      transport ι ρ τ (g * h) hgh (φ ∘ₗ ψ) hφψ := by
  ext f x
  simp [mul_assoc]

/-- Restriction is transport along `1` with the identity intertwiner. -/
lemma restrict_eq_transport (hle : K ≤ L) :
    restrict ι σ hle = transport ι (σ.comp (Subgroup.inclusion hle)) σ 1
      (fun k hk => by simpa using hle hk) LinearMap.id
      (fun k w => by
        change σ _ w = σ (Subgroup.inclusion hle k) w
        congr 2
        ext
        simp) := by
  ext f x
  simp

end Transport

section LevelPresheaf

variable [TopologicalSpace G] (R) (ι : Γ →* G) {V : Type t} [AddCommGroup V] [Module R V]
  (ρ : Representation R G V)

/-- For a representation `ρ` of `G`, transport along a level arrow `a : K ⟶ L`
(`a.element⁻¹ K a.element ⊆ L`) with intertwiner `ρ a.element`:
`f ↦ (x ↦ ρ a.element (f (x * a.element)))`. -/
def levelTransport {K L : CompactOpenLevel G} (a : K ⟶ L) :
    forms ι L.subgroup (ρ.comp L.subgroup.subtype) →ₗ[R]
      forms ι K.subgroup (ρ.comp K.subgroup.subtype) :=
  transport ι _ _ a.element a.respects (ρ a.element) fun k w => by
    change ρ a.element (ρ (a.element⁻¹ * k * a.element) w) = ρ k (ρ a.element w)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group

@[simp]
lemma levelTransport_apply_coe {K L : CompactOpenLevel G} (a : K ⟶ L)
    (f : forms ι L.subgroup (ρ.comp L.subgroup.subtype)) (x : G) :
    (levelTransport R ι ρ a f).1 x = ρ a.element (f.1 (x * a.element)) :=
  rfl

/-- The forms of all compact open levels for a representation `ρ` of `G`, as a presheaf on the
category of levels, with `levelTransport` on arrows. -/
def levelPresheaf : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{max uG t} R where
  obj K := ModuleCat.of R (forms ι K.unop.subgroup (ρ.comp K.unop.subgroup.subtype))
  map a := ModuleCat.ofHom (levelTransport R ι ρ a.unop)
  map_id K := by
    ext f x
    simp
  map_comp a b := by
    ext f x
    simp [mul_assoc]

@[simp]
lemma levelPresheaf_map_apply_coe {K L : (CompactOpenLevel G)ᵒᵖ} (a : K ⟶ L)
    (f : (levelPresheaf R ι ρ).obj K) (x : G) :
    (((levelPresheaf R ι ρ).map a).hom f).1 x = ρ a.unop.element (f.1 (x * a.unop.element)) :=
  rfl

end LevelPresheaf

section Hecke

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- A compact open level has finite index over any other compact open level it contains, or
more generally over its intersection with any compact open level. -/
instance (K K' : CompactOpenLevel G) :
    Finite (K.subgroup ⧸ K'.subgroup.subgroupOf K.subgroup) := by
  have : CompactSpace K.subgroup := isCompact_iff_compactSpace.mp K.isCompact
  exact Subgroup.quotient_finite_of_isOpen _
    (Subgroup.subgroupOf_isOpen _ _ K'.openSubgroup.isOpen)

/-- The intermediate Hecke level `K ∩ g L g⁻¹` is contained in `K`. -/
lemma heckeLevel_le (K L : CompactOpenLevel G) (g : G) :
    (CompactOpenLevel.heckeLevel K L g).subgroup ≤ K.subgroup :=
  fun _ hk => hk.1

/-- Conjugation by `g` maps the intermediate Hecke level `K ∩ g L g⁻¹` into `L`. -/
lemma heckeLevel_conj_mem (K L : CompactOpenLevel G) (g : G) :
    ∀ k ∈ (CompactOpenLevel.heckeLevel K L g).subgroup, g⁻¹ * k * g ∈ L.subgroup :=
  (CompactOpenLevel.heckeRight K L g).respects

variable (ι : Γ →* G) {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W]
  [Module R W]

/-- The Hecke operator of the double coset `K g L`: transport from level `L` to the
intermediate level `K ∩ g L g⁻¹` along `g`, followed by the trace to level `K`. -/
def hecke (K L : CompactOpenLevel G) (g : G) (ρ : Representation R K.subgroup V)
    (σ : Representation R L.subgroup W) (φ : W →ₗ[R] V)
    (hφ : ∀ (k : (CompactOpenLevel.heckeLevel K L g).subgroup) (w : W),
      φ (σ ⟨g⁻¹ * k * g, heckeLevel_conj_mem K L g k k.2⟩ w) =
        ρ (Subgroup.inclusion (heckeLevel_le K L g) k) (φ w)) :
    forms ι L.subgroup σ →ₗ[R] forms ι K.subgroup ρ :=
  trace ι ρ (heckeLevel_le K L g) ∘ₗ
    transport ι _ σ g (heckeLevel_conj_mem K L g) φ hφ

/-- The Hecke operator formula with chosen coset representatives `Quotient.out`. -/
lemma hecke_apply_coe (K L : CompactOpenLevel G) (g : G) (ρ : Representation R K.subgroup V)
    (σ : Representation R L.subgroup W) (φ : W →ₗ[R] V)
    (hφ : ∀ (k : (CompactOpenLevel.heckeLevel K L g).subgroup) (w : W),
      φ (σ ⟨g⁻¹ * k * g, heckeLevel_conj_mem K L g k k.2⟩ w) =
        ρ (Subgroup.inclusion (heckeLevel_le K L g) k) (φ w))
    [Fintype (K.subgroup ⧸ (CompactOpenLevel.heckeLevel K L g).subgroup.subgroupOf K.subgroup)]
    (f : forms ι L.subgroup σ) (x : G) :
    (hecke ι K L g ρ σ φ hφ f).1 x =
      ∑ q : K.subgroup ⧸ (CompactOpenLevel.heckeLevel K L g).subgroup.subgroupOf K.subgroup,
        ρ q.out (φ (f.1 (x * q.out * g))) := by
  rw [hecke, LinearMap.comp_apply, trace_apply_coe_out]
  rfl

variable (R) (ρ : Representation R G V)

/-- The Hecke operator `[K g L]` for a representation `ρ` of `G`, with intertwiner `ρ g`. -/
def heckeOperator (K L : CompactOpenLevel G) (g : G) :
    forms ι L.subgroup (ρ.comp L.subgroup.subtype) →ₗ[R]
      forms ι K.subgroup (ρ.comp K.subgroup.subtype) :=
  hecke ι K L g _ _ (ρ g) fun k w => by
    change ρ g (ρ (g⁻¹ * k * g) w) = ρ k (ρ g w)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group

/-- The classical formula `([K g L] f) x = ∑ ρ (k g) (f (x k g))`, summed over representatives
`k` of `K ⧸ (K ∩ g L g⁻¹)`. -/
lemma heckeOperator_apply_coe (K L : CompactOpenLevel G) (g : G)
    [Fintype (K.subgroup ⧸ (CompactOpenLevel.heckeLevel K L g).subgroup.subgroupOf K.subgroup)]
    (f : forms ι L.subgroup (ρ.comp L.subgroup.subtype)) (x : G) :
    (heckeOperator R ι ρ K L g f).1 x =
      ∑ q : K.subgroup ⧸ (CompactOpenLevel.heckeLevel K L g).subgroup.subgroupOf K.subgroup,
        ρ (q.out * g) (f.1 (x * q.out * g)) := by
  rw [heckeOperator, hecke_apply_coe]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, Module.End.mul_apply]
  rfl

/-- The Hecke operator is the level-presheaf map along the second leg `heckeRight` of the
Hecke correspondence followed by the trace along the first leg. -/
lemma heckeOperator_eq (K L : CompactOpenLevel G) (g : G) :
    heckeOperator R ι ρ K L g =
      trace ι (ρ.comp K.subgroup.subtype) (heckeLevel_le K L g) ∘ₗ
        levelTransport R ι ρ (CompactOpenLevel.heckeRight K L g) :=
  rfl

end Hecke

end Langlands.Shimura.EquivariantForms
