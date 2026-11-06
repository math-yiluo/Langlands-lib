import Mathlib.RepresentationTheory.Invariants
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.BigOperators.Finprod
import Langlands.Representation.Smooth.Definitions
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Finite orbit means

Algebraic infrastructure for compact averaging. Only finite sums in characteristic-zero
modules are used; the modules carry no topology.
-/

namespace Langlands.Compact.CharZero

open scoped BigOperators

universe uK uG uV uW uX uY

variable {k : Type uK} [Field k] [CharZero k]
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable {W : Type uW} [AddCommGroup W] [Module k W]

/-- Normalized finite sum in a module over a field of characteristic zero. -/
noncomputable def finiteMean {X : Type uX} [Fintype X] (f : X → V) : V :=
  (Fintype.card X : k)⁻¹ • ∑ x, f x

private def fiberEquiv {X : Type uX} {Y : Type uY}
    [MulAction G X] [MulAction G Y] (f : X →[G] Y)
    (g : G) (y : Y) : {x // f x = y} ≃ {x // f x = g • y} where
  toFun x := ⟨g • x.val, by simp only [map_smul, x.property]⟩
  invFun x := ⟨g⁻¹ • x.val, by simp only [map_smul, x.property, inv_smul_smul]⟩
  left_inv x := by ext; exact inv_smul_smul g x.val
  right_inv x := by ext; exact smul_inv_smul g x.val

/-- An equivariant map to a transitive finite set has equal-sized fibers, so
pulling back does not change the normalized mean. -/
theorem finiteMean_comp {X : Type uX} {Y : Type uY}
    [Fintype X] [Fintype Y] [Nonempty X]
    [MulAction G X] [MulAction G Y] [MulAction.IsPretransitive G Y]
    (f : X →[G] Y) (h : Y → V) :
    finiteMean (k := k) (h ∘ f) = finiteMean (k := k) h := by
  classical
  let x₀ : X := Classical.choice inferInstance
  let y₀ : Y := f x₀
  let c := Fintype.card {x // f x = y₀}
  have hc : c ≠ 0 := by
    let : Nonempty {x // f x = y₀} := ⟨⟨x₀, rfl⟩⟩
    exact Fintype.card_ne_zero
  have hfiber (y : Y) : Fintype.card {x // f x = y} = c := by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G y₀ y
    exact (Fintype.card_congr (fiberEquiv f g y₀)).symm
  have hcard : Fintype.card X = Fintype.card Y * c := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
    simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hsum : (∑ x, h (f x)) = (c : k) • ∑ y, h y := by
    rw [← Fintype.sum_fiberwise f (fun x => h (f x))]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro y _
    calc
      (∑ x : {x // f x = y}, h (f x)) = ∑ _ : {x // f x = y}, h y :=
        Finset.sum_congr rfl (fun x _ => congrArg h x.property)
      _ = (c : k) • h y := by
        simp only [Finset.sum_const, Finset.card_univ, hfiber, Nat.cast_smul_eq_nsmul]
  have hc' : (c : k) ≠ 0 := by exact_mod_cast hc
  unfold finiteMean
  change (Fintype.card X : k)⁻¹ • (∑ x, h (f x)) = _
  rw [hsum, smul_smul, hcard, Nat.cast_mul, mul_inv_rev]
  congr 1
  field_simp

/-- The action associated to an algebraic representation, installed locally. -/
abbrev representationAction (ρ : Representation k G V) : MulAction G V where
  smul g v := ρ g v
  one_smul v := by change ρ 1 v = v; simp
  mul_smul g h v := by change ρ (g * h) v = ρ g (ρ h v); simp

/-- The orbit of a vector, with no topology on the vector space. -/
def orbit (ρ : Representation k G V) (v : V) : Set V :=
  Set.range (fun g : G => ρ g v)

instance orbitNonempty (ρ : Representation k G V) (v : V) :
    Nonempty (orbit ρ v) :=
  ⟨⟨v, ⟨1, by simp⟩⟩⟩

instance orbitAction (ρ : Representation k G V) (v : V) :
    MulAction G (orbit ρ v) where
  smul g x := ⟨ρ g x.val, by
    obtain ⟨h, hh⟩ := x.property
    exact ⟨g * h, by simp [hh]⟩⟩
  one_smul x := Subtype.ext (by change ρ 1 x.val = x.val; simp)
  mul_smul g h x := Subtype.ext (by change ρ (g * h) x.val = ρ g (ρ h x.val); simp)

instance orbitPretransitive (ρ : Representation k G V) (v : V) :
    MulAction.IsPretransitive G (orbit ρ v) where
  exists_smul_eq x y := by
    obtain ⟨g, hg⟩ := x.property
    obtain ⟨h, hh⟩ := y.property
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    change ρ (h * g⁻¹) x.val = y.val
    rw [← hg, ← Module.End.mul_apply, ← map_mul]
    simpa using hh

/-- The normalized sum of distinct orbit vectors. Its projection properties
require a finite orbit; the total definition uses `Nat.card` and `finsum`. -/
noncomputable def orbitMean (ρ : Representation k G V) (v : V) : V :=
  (Nat.card (orbit ρ v) : k)⁻¹ • ∑ᶠ x : orbit ρ v, x.val

omit [CharZero k] in
theorem orbitMean_eq_finiteMean (ρ : Representation k G V) (v : V)
    [Fintype (orbit ρ v)] :
    orbitMean ρ v = finiteMean (k := k) (fun x : orbit ρ v => x.val) := by
  simp only [orbitMean, finiteMean, Nat.card_eq_fintype_card, finsum_eq_sum_of_fintype]

/-- A linear intertwiner induces the corresponding equivariant map of orbits. -/
def orbitMap (ρ : Representation k G V) (σ : Representation k G W)
    (f : V →ₗ[k] W) (hf : ∀ g v, f (ρ g v) = σ g (f v)) (v : V) :
    orbit ρ v →[G] orbit σ (f v) where
  toFun x := ⟨f x.val, by
    obtain ⟨g, hg⟩ := x.property
    exact ⟨g, (hf g v).symm.trans (congrArg f hg)⟩⟩
  map_smul' g x := Subtype.ext (hf g x.val)

theorem orbitMean_map (ρ : Representation k G V) (σ : Representation k G W)
    (f : V →ₗ[k] W) (hf : ∀ g v, f (ρ g v) = σ g (f v)) (v : V)
    [sourceFinite : Finite (orbit ρ v)] [targetFinite : Finite (orbit σ (f v))] :
    f (orbitMean ρ v) = orbitMean σ (f v) := by
  classical
  let := Fintype.ofFinite (orbit ρ v)
  let := Fintype.ofFinite (orbit σ (f v))
  rw [orbitMean_eq_finiteMean, orbitMean_eq_finiteMean]
  change f ((Fintype.card (orbit ρ v) : k)⁻¹ • ∑ x : orbit ρ v, x.val) = _
  rw [map_smul, map_sum]
  exact finiteMean_comp (orbitMap ρ σ f hf v) (fun x => x.val)

omit [CharZero k] in
/-- A pair of finite orbits has a finite orbit for the product representation. -/
theorem finite_orbit_prod (ρ : Representation k G V) (σ : Representation k G W)
    (v : V) (w : W) [Finite (orbit ρ v)] [Finite (orbit σ w)] :
    Finite (orbit (ρ.prod σ) (v, w)) := by
  let f : orbit (ρ.prod σ) (v, w) → orbit ρ v × orbit σ w := fun x =>
    (⟨x.val.1, by
      obtain ⟨g, hg⟩ := x.property
      exact ⟨g, congrArg Prod.fst hg⟩⟩,
     ⟨x.val.2, by
      obtain ⟨g, hg⟩ := x.property
      exact ⟨g, congrArg Prod.snd hg⟩⟩)
  exact Finite.of_injective f (fun x y h => Subtype.ext
    (Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h)))

theorem orbitMean_add (ρ : Representation k G V) (v w : V)
    [Finite (orbit ρ v)] [Finite (orbit ρ w)] [Finite (orbit ρ (v + w))] :
    orbitMean ρ (v + w) = orbitMean ρ v + orbitMean ρ w := by
  let := finite_orbit_prod ρ ρ v w
  have hfst := orbitMean_map (ρ.prod ρ) ρ (LinearMap.fst k V V)
    (fun _ _ => rfl) (v, w) (targetFinite := inferInstanceAs (Finite (orbit ρ v)))
  have hsnd := orbitMean_map (ρ.prod ρ) ρ (LinearMap.snd k V V)
    (fun _ _ => rfl) (v, w) (targetFinite := inferInstanceAs (Finite (orbit ρ w)))
  have hadd := orbitMean_map (ρ.prod ρ) ρ
    (LinearMap.fst k V V + LinearMap.snd k V V)
    (fun g x => (map_add (ρ g) x.1 x.2).symm) (v, w)
    (targetFinite := inferInstanceAs (Finite (orbit ρ (v + w))))
  exact hadd.symm.trans (congrArg₂ (· + ·) hfst hsnd)

theorem orbitMean_smul (ρ : Representation k G V) (c : k) (v : V)
    [Finite (orbit ρ v)] [Finite (orbit ρ (c • v))] :
    orbitMean ρ (c • v) = c • orbitMean ρ v := by
  let f : V →ₗ[k] V :=
    { toFun := fun x => c • x
      map_add' := smul_add c
      map_smul' := fun a x => smul_comm c a x }
  exact (orbitMean_map ρ ρ f
    (fun g x => (map_smul (ρ g) c x).symm) v
    (targetFinite := inferInstanceAs (Finite (orbit ρ (c • v))))).symm


omit [CharZero k] in
/-- Translating the starting vector preserves its orbit mean. -/
theorem orbitMean_apply (ρ : Representation k G V) (g : G) (v : V) :
    orbitMean ρ (ρ g v) = orbitMean ρ v := by
  have horbit : orbit ρ (ρ g v) = orbit ρ v := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h * g, by simp⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h * g⁻¹, by simp⟩
  exact congrArg (fun S : Set V => (Nat.card S : k)⁻¹ • ∑ᶠ x : S, x.val) horbit

omit [CharZero k] in
theorem orbitMean_invariant (ρ : Representation k G V) (v : V)
    [Finite (orbit ρ v)] (g : G) :
    ρ g (orbitMean ρ v) = orbitMean ρ v := by
  classical
  let := Fintype.ofFinite (orbit ρ v)
  rw [orbitMean_eq_finiteMean]
  unfold finiteMean
  rw [map_smul, map_sum]
  congr 1
  exact Equiv.sum_comp (MulAction.toPerm (β := orbit ρ v) g) (fun x => x.val)

theorem orbitMean_id (ρ : Representation k G V) (v : V)
    [Finite (orbit ρ v)] (hv : ∀ g, ρ g v = v) :
    orbitMean ρ v = v := by
  classical
  let := Fintype.ofFinite (orbit ρ v)
  have hval (x : orbit ρ v) : x.val = v := by
    obtain ⟨g, hg⟩ := x.property
    exact hg.symm.trans (hv g)
  have hcard : (Fintype.card (orbit ρ v) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [orbitMean_eq_finiteMean]
  simp only [finiteMean, hval, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hcard, one_smul]


variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [CharZero k] in
/-- Smooth vectors have finite orbits under compact open subgroups. -/
theorem finite_orbit_of_smooth (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V) :
    Finite (orbit (ρ.comp K.toSubgroup.subtype) v) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let : MulAction K V := representationAction (ρ.comp K.toSubgroup.subtype)
  obtain ⟨U, hU⟩ := hρ v
  have hle : U.toSubgroup.subgroupOf K.toSubgroup ≤ MulAction.stabilizer K v := by
    intro k hk
    exact hU ⟨k.val, hk⟩
  have hopen : IsOpen (MulAction.stabilizer K v : Set K) :=
    Subgroup.isOpen_mono hle
      (Subgroup.subgroupOf_isOpen K.toSubgroup U.toSubgroup U.isOpen)
  let : Finite (K ⧸ MulAction.stabilizer K v) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  exact Finite.of_equiv (K ⧸ MulAction.stabilizer K v)
    (MulAction.orbitEquivQuotientStabilizer K v).symm

/-- Normalized compact-subgroup averaging as a linear endomorphism. -/
noncomputable def averageMap (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) : V →ₗ[k] V where
  toFun := orbitMean (ρ.comp K.toSubgroup.subtype)
  map_add' v w := by
    let := finite_orbit_of_smooth ρ hρ K hK v
    let := finite_orbit_of_smooth ρ hρ K hK w
    let := finite_orbit_of_smooth ρ hρ K hK (v + w)
    exact orbitMean_add _ v w
  map_smul' c v := by
    let := finite_orbit_of_smooth ρ hρ K hK v
    let := finite_orbit_of_smooth ρ hρ K hK (c • v)
    exact orbitMean_smul _ c v

/-- The linear map between fixed-vector submodules induced by an intertwiner. -/
noncomputable def fixedVectorMap (ρ : Representation k G V) (σ : Representation k G W)
    (f : ρ.IntertwiningMap σ) (K : Subgroup G) :
    fixedVectors ρ K →ₗ[k] fixedVectors σ K :=
  (f.toLinearMap.comp (fixedVectors ρ K).subtype).codRestrict
    (fixedVectors σ K) (by
      intro v k
      change σ k.val (f v.val) = f v.val
      rw [← f.isIntertwining ρ σ k.val v.val]
      exact congrArg f (v.property k))

theorem averageMap_mem_fixedVectors (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V) :
    averageMap ρ hρ K hK v ∈ fixedVectors ρ K.toSubgroup := by
  let := finite_orbit_of_smooth ρ hρ K hK v
  exact orbitMean_invariant (ρ.comp K.toSubgroup.subtype) v

theorem averageMap_id (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V)
    (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    averageMap ρ hρ K hK v = v := by
  let := finite_orbit_of_smooth ρ hρ K hK v
  exact orbitMean_id (ρ.comp K.toSubgroup.subtype) v hv

theorem averageMap_isProj (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    LinearMap.IsProj (fixedVectors ρ K.toSubgroup) (averageMap ρ hρ K hK) :=
  ⟨averageMap_mem_fixedVectors ρ hρ K hK, averageMap_id ρ hρ K hK⟩

theorem averageMap_commute (ρ : Representation k G V) (σ : Representation k G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap σ) :
    f.toLinearMap.comp (averageMap ρ hρ K hK) =
      (averageMap σ hσ K hK).comp f.toLinearMap := by
  ext v
  let := finite_orbit_of_smooth ρ hρ K hK v
  let := finite_orbit_of_smooth σ hσ K hK (f v)
  exact orbitMean_map (ρ.comp K.toSubgroup.subtype) (σ.comp K.toSubgroup.subtype)
    f.toLinearMap (fun k x => f.isIntertwining ρ σ k.val x) v


/-- Averaging after an element of the compact subgroup leaves the mean unchanged. -/
theorem averageMap_apply_rho (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : K) (v : V) :
    averageMap ρ hρ K hK (ρ x.val v) = averageMap ρ hρ K hK v :=
  orbitMean_apply (ρ.comp K.toSubgroup.subtype) x v

/-- The normalized projection with codomain the compact-open fixed vectors. -/
noncomputable def fixedProjection (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    V →ₗ[k] fixedVectors ρ K.toSubgroup :=
  (averageMap ρ hρ K hK).codRestrict (fixedVectors ρ K.toSubgroup)
    (averageMap_mem_fixedVectors ρ hρ K hK)

@[simp]
theorem fixedProjection_fixed (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (v : fixedVectors ρ K.toSubgroup) : fixedProjection ρ hρ K hK v.val = v := by
  apply Subtype.ext
  exact averageMap_id ρ hρ K hK v.val v.property

theorem fixedProjection_apply_rho (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : K) (v : V) :
    fixedProjection ρ hρ K hK (ρ x.val v) = fixedProjection ρ hρ K hK v := by
  apply Subtype.ext
  exact averageMap_apply_rho ρ hρ K hK x v

/-- Fixed-vector functors preserve the surjectivity of an intertwiner. -/
theorem fixedVectorMap_surjective (ρ : Representation k G V) (σ : Representation k G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) : Function.Surjective (fixedVectorMap ρ σ f K.toSubgroup) := by
  intro w
  obtain ⟨v, hv⟩ := hf w.val
  refine ⟨fixedProjection ρ hρ K hK v, ?_⟩
  apply Subtype.ext
  change f (averageMap ρ hρ K hK v) = w.val
  have hcomm := LinearMap.congr_fun (averageMap_commute ρ σ hρ hσ K hK f) v
  change f (averageMap ρ hρ K hK v) = averageMap σ hσ K hK (f v) at hcomm
  rw [hcomm, hv]
  exact averageMap_id σ hσ K hK w.val w.property

/-- A fixed-vector functional extends smoothly by composing with the projection. -/
noncomputable def fixedExtension (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (ℓ : Module.Dual k (fixedVectors ρ K.toSubgroup)) : Module.Dual k V :=
  ℓ.comp (fixedProjection ρ hρ K hK)

theorem fixedExtension_isSmoothVector (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (ℓ : Module.Dual k (fixedVectors ρ K.toSubgroup)) :
    IsSmoothVector ρ.dual (fixedExtension ρ hρ K hK ℓ) := by
  refine ⟨K, fun x => ?_⟩
  apply LinearMap.ext
  intro v
  change ℓ (fixedProjection ρ hρ K hK (ρ x.val⁻¹ v)) = ℓ (fixedProjection ρ hρ K hK v)
  exact congrArg ℓ (fixedProjection_apply_rho ρ hρ K hK x⁻¹ v)

@[simp]
theorem fixedExtension_fixed (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (ℓ : Module.Dual k (fixedVectors ρ K.toSubgroup)) (v : fixedVectors ρ K.toSubgroup) :
    fixedExtension ρ hρ K hK ℓ v.val = ℓ v := by
  change ℓ (fixedProjection ρ hρ K hK v.val) = ℓ v
  rw [fixedProjection_fixed]

end Langlands.Compact.CharZero
