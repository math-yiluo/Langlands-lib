import Langlands.ClassFieldTheory.Local.Cohomology
import Langlands.Cohomology.Profinite.Comparison.FiniteQuotients
import Langlands.Cohomology.Profinite.LongExactSequence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Algebra.Group.CompactOpen

namespace Langlands.ProfiniteCohomology

open Topology

/-- `ℚ/ℤ` with the discrete topology: the Library's `RationalModIntegers` (which is
`AddCircle (1 : ℚ)` as a type), as a discrete topological group, so that continuous homomorphisms
`Additive G →ₜ+ QZ` are the characters with open kernel. -/
def QZ : Type := Langlands.ClassFieldTheory.Local.RationalModIntegers

namespace QZ

instance : AddCommGroup QZ := inferInstanceAs (AddCommGroup (AddCircle (1 : ℚ)))

instance : TopologicalSpace QZ := ⊥

instance : DiscreteTopology QZ := ⟨rfl⟩

instance : IsTopologicalAddGroup QZ where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

/-- `QZ` is `AddCircle (1 : ℚ)` (the same type, without its topology). -/
def toAddCircle : QZ ≃+ AddCircle (1 : ℚ) := AddEquiv.refl _

/-- `QZ` is the Library's `RationalModIntegers` (the same type, without its topology). -/
def toRationalModIntegers : QZ ≃+ Langlands.ClassFieldTheory.Local.RationalModIntegers :=
  AddEquiv.refl _

def mk (q : ℚ) : QZ := toAddCircle.symm (q : AddCircle (1 : ℚ))

theorem mk_surjective : Function.Surjective mk := fun x =>
  QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) (toAddCircle x)

@[simp] theorem mk_add (p q : ℚ) : mk (p + q) = mk p + mk q := by
  simp [mk]

@[simp] theorem mk_zero : mk 0 = 0 := by simp [mk]

theorem mk_eq_zero_iff (q : ℚ) : mk q = 0 ↔ ∃ n : ℤ, (n : ℚ) = q := by
  simp only [mk, AddEquivClass.map_eq_zero_iff, AddCircle.coe_eq_zero_iff, zsmul_eq_mul, mul_one]

theorem mk_nsmul (n : ℕ) (q : ℚ) : mk (n • q) = n • mk q := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, mk_add, ih, succ_nsmul]

theorem mk_zsmul (n : ℤ) (q : ℚ) : mk (n • q) = n • mk q := by
  simp [mk]

theorem nsmul_mk_one_div (n : ℕ) : n • mk (1 / n) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [← mk_nsmul, nsmul_eq_mul, mul_one_div_cancel (by exact_mod_cast hn.ne'), mk_eq_zero_iff]
    exact ⟨1, by simp⟩

theorem addOrderOf_mk_one_div {n : ℕ} (hn : 0 < n) : addOrderOf (mk (1 / n)) = n := by
  have : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
  exact AddCircle.addOrderOf_period_div (p := (1 : ℚ)) hn

theorem exists_eq_nsmul_mk_one_div {n : ℕ} (hn : 0 < n) {x : QZ} (hx : n • x = 0) :
    ∃ m : ℕ, x = m • mk (1 / n) := by
  have : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
  obtain ⟨m, -, hm⟩ := (AddCircle.nsmul_eq_zero_iff (p := (1 : ℚ)) (u := x) hn).1 hx
  refine ⟨m, ?_⟩
  rw [← mk_nsmul, ← hm, nsmul_eq_mul, mul_one, mul_one_div]
  rfl

theorem mk_half_ne_zero : mk (1 / 2) ≠ 0 := by
  rw [Ne, mk_eq_zero_iff]
  rintro ⟨n, hn⟩
  have h2 : (2 * n : ℚ) = 1 := by rw [hn]; norm_num
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

theorem mk_half_add_mk_half : mk (1 / 2) + mk (1 / 2) = 0 := by
  rw [← two_nsmul]
  have := nsmul_mk_one_div 2
  norm_num at this
  exact this

end QZ

abbrev QZDual (A : Type*) [AddCommGroup A] [TopologicalSpace A] : Type _ := A →ₜ+ QZ

namespace QZDual

variable {A B C : Type*} [AddCommGroup A] [TopologicalSpace A] [AddCommGroup B]
  [TopologicalSpace B] [AddCommGroup C] [TopologicalSpace C]

def map (f : A →ₜ+ B) : QZDual B →ₜ+ QZDual A :=
  ContinuousAddMonoidHom.compLeft QZ f

@[simp]
theorem map_apply (f : A →ₜ+ B) (χ : QZDual B) (a : A) : map f χ a = χ (f a) :=
  rfl

@[simp]
theorem map_id : map (ContinuousAddMonoidHom.id A) = ContinuousAddMonoidHom.id (QZDual A) :=
  rfl

theorem map_comp (g : B →ₜ+ C) (f : A →ₜ+ B) :
    map (g.comp f) = (map f).comp (map g) :=
  rfl

def toAddMonoidHomEquiv [DiscreteTopology A] : QZDual A ≃+ (A →+ QZ) where
  toFun χ := χ.toAddMonoidHom
  invFun f := { f with continuous_toFun := continuous_of_discreteTopology }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem toAddMonoidHomEquiv_apply [DiscreteTopology A] (χ : QZDual A) (a : A) :
    toAddMonoidHomEquiv χ a = χ a :=
  rfl

@[simp]
theorem toAddMonoidHomEquiv_symm_apply [DiscreteTopology A] (f : A →+ QZ) (a : A) :
    toAddMonoidHomEquiv.symm f a = f a :=
  rfl

variable (A) in

def eval : A →+ QZDual (QZDual A) where
  toFun a :=
    { toFun := fun χ => χ a
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_eval_const a }
  map_zero' := by ext χ; exact map_zero χ
  map_add' a b := by ext χ; exact map_add χ a b

@[simp]
theorem eval_apply (a : A) (χ : QZDual A) : eval A a χ = χ a :=
  rfl

end QZDual

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

section LocallyConstantHom

variable (G : Type*) [Group G] [TopologicalSpace G] (M : Type*) [AddCommGroup M]

def locallyConstantHom : AddSubgroup (Additive G →+ M) where
  carrier := {χ | IsLocallyConstant fun g : G => χ (Additive.ofMul g)}
  zero_mem' := by
    change IsLocallyConstant fun g : G => (0 : Additive G →+ M) (Additive.ofMul g)
    exact IsLocallyConstant.const (0 : M)
  add_mem' {χ ψ} hχ hψ := by
    change IsLocallyConstant fun g : G => (χ + ψ) (Additive.ofMul g)
    exact IsLocallyConstant.add hχ hψ
  neg_mem' {χ} hχ := by
    change IsLocallyConstant fun g : G => (-χ) (Additive.ofMul g)
    exact IsLocallyConstant.neg hχ

def locallyConstantHomQZEquiv : locallyConstantHom G (AddCircle (1 : ℚ)) ≃+ (Additive G →ₜ+ QZ) where
  toFun χ :=
    { toAddMonoidHom := QZ.toAddCircle.symm.toAddMonoidHom.comp χ.1
      continuous_toFun := (IsLocallyConstant.iff_continuous _).1 χ.2 }
  invFun χ := ⟨QZ.toAddCircle.toAddMonoidHom.comp χ.toAddMonoidHom,
    (IsLocallyConstant.iff_continuous (fun x : Additive G => χ x)).2 χ.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable {G} in
@[simp]
theorem locallyConstantHomQZEquiv_apply (χ : locallyConstantHom G (AddCircle (1 : ℚ)))
    (g : Additive G) :
    locallyConstantHomQZEquiv G χ g = QZ.toAddCircle.symm (χ.1 g) :=
  rfl

end LocallyConstantHom

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory Limits MonoidalCategory groupCohomology

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

/-! ### The exact sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` of trivial representations -/

namespace GroupCoh

open CategoryTheory Limits Rep groupCohomology

section Exactness

universe u

variable {k G : Type u} [CommRing k] [Group G]

theorem shortComplex_exact_of_forall {S : ShortComplex (Rep.{u} k G)}
    (h : ∀ x : S.X₂, S.g.hom x = 0 → ∃ y : S.X₁, S.f.hom y = x) : S.Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
    ShortComplex.moduleCat_exact_iff]
  exact h

end Exactness

section Sequence

variable (G : Type) [Group G]

/-- The inclusion `ℤ → ℚ` of trivial representations. -/
noncomputable def intToRat : Rep.trivial ℤ G ℤ ⟶ Rep.trivial ℤ G ℚ :=
  Rep.ofHom ⟨(Int.castAddHom ℚ).toIntLinearMap, fun _ => rfl⟩

/-- The projection `ℚ → ℚ/ℤ` of trivial representations. -/
noncomputable def ratToRatModInt : Rep.trivial ℤ G ℚ ⟶ Rep.trivial ℤ G (AddCircle (1 : ℚ)) :=
  Rep.ofHom ⟨(QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap, fun _ => rfl⟩

/-- The short exact sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` of trivial representations. -/
noncomputable def ratSES : ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (intToRat G) (ratToRatModInt G) (by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun n => ?_))
    change ((n : ℚ) : AddCircle (1 : ℚ)) = 0
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨n, by simp⟩)

theorem ratSES_shortExact : (ratSES G).ShortExact where
  mono_f := (Rep.mono_iff_injective _).2 fun a b h => Int.cast_injective (α := ℚ) h
  epi_g := (Rep.epi_iff_surjective _).2 fun x => QuotientAddGroup.mk_surjective x
  exact := by
    refine shortComplex_exact_of_forall fun q hq => ?_
    have hq' : ((show ℚ from q) : AddCircle (1 : ℚ)) = 0 := hq
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 hq'
    exact ⟨n, by change ((n : ℤ) : ℚ) = (show ℚ from q); rw [← hn, zsmul_one]⟩

end Sequence

theorem bijective_nsmul_of_module_rat {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (hn : n ≠ 0) : Function.Bijective fun v : V => n • v := by
  have : (fun v : V => n • v) = LinearEquiv.smulOfUnit (M := V)
      (IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ))) := by
    funext v
    change _ = IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ)) • v
    rw [Units.smul_def, IsUnit.unit_spec, Nat.cast_smul_eq_nsmul]
  rw [this]
  exact LinearEquiv.bijective _

section Cyclic

variable {G : Type} [Group G] [Fintype G] (σ : G) (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)

include hσ in
theorem orderOf_ofAdd_div_card_dvd :
    orderOf (Multiplicative.ofAdd (((1 : ℚ) / Nat.card G : ℚ) : AddCircle (1 : ℚ))) ∣
      orderOf σ := by
  have : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
  rw [orderOf_ofAdd_eq_addOrderOf, AddCircle.addOrderOf_period_div Nat.card_pos,
    orderOf_eq_card_of_forall_mem_zpowers hσ]

/-- The character of a finite cyclic group `G` generated by `σ` sending `σ` to `1/|G|`. -/
noncomputable def cyclicChar : Additive G →+ AddCircle (1 : ℚ) :=
  MonoidHom.toAdditiveLeft (monoidHomOfForallMemZpowers hσ (orderOf_ofAdd_div_card_dvd σ hσ))

theorem cyclicChar_apply_gen :
    cyclicChar σ hσ (Additive.ofMul σ) = (((1 : ℚ) / Nat.card G : ℚ) : AddCircle (1 : ℚ)) := by
  change Multiplicative.toAdd
    (monoidHomOfForallMemZpowers hσ (orderOf_ofAdd_div_card_dvd σ hσ) σ) = _
  rw [monoidHomOfForallMemZpowers_apply_gen]
  rfl

end Cyclic

end GroupCoh

section Nsmul

/-- Multiplication by a divisor of `n` is bijective when multiplication by `n` is. -/
theorem bijective_nsmul_of_dvd {A : Type*} [AddCommGroup A] {m n : ℕ} (hmn : m ∣ n)
    (hn : Function.Bijective fun a : A => n • a) : Function.Bijective fun a : A => m • a := by
  obtain ⟨c, rfl⟩ := hmn
  refine ⟨fun a b hab => hn.1 ?_, fun a => ?_⟩
  · have hab' : m • a = m • b := hab
    change (m * c) • a = (m * c) • b
    rw [mul_comm, ← smul_smul, ← smul_smul, hab']
  · obtain ⟨b, rfl⟩ := hn.2 a
    exact ⟨c • b, by change m • c • b = (m * c) • b; rw [smul_smul]⟩

end Nsmul

open CategoryTheory Limits MonoidalCategory groupCohomology GroupCoh

section Multiplication

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]

theorem cochainsMap_nsmul (f : A ⟶ B) (m : ℕ) : coeffCochainsMap (m • f) = m • coeffCochainsMap f := by
  induction m with
  | zero => rw [zero_smul, zero_smul, coeffCochainsMap_zero]
  | succ m ih =>
    rw [succ_nsmul, succ_nsmul, ← ih]
    ext n c : 3
    apply Subtype.ext
    funext x
    rfl

variable (A) in

theorem cohomologyMap_nsmul_id (m n : ℕ) : coeffMap (m • 𝟙 A) n = m • 𝟙 (cohomology A n) := by
  change HomologicalComplex.homologyMap (coeffCochainsMap (m • 𝟙 A)) n =
    m • 𝟙 ((cochains A).homology n)
  rw [cochainsMap_nsmul, coeffCochainsMap_id]
  have := (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).map_nsmul
    (f := 𝟙 (cochains A)) (n := m)
  simp only [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_id] at this
  exact this

end Multiplication

section Divisible

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

theorem isZero_cohomology_of_bijective_nsmul {k : Type u} [CommRing k] (A : Rep.{u} k G)
    [IsSmoothRep A] (hA : ∀ m : ℕ, m ≠ 0 → Function.Bijective fun a : A => m • a) {n : ℕ}
    (hn : 1 ≤ n) : IsZero (cohomology A n) := by
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => ?_⟩
  suffices h : ∀ x : cohomology A n, x = 0 by rw [h x, h y]
  intro x
  obtain ⟨m, hm, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (isTorsion_cohomology A hn x)
  have hiso : IsIso (m • 𝟙 A) := by
    have hb : Function.Bijective (m • 𝟙 A).hom := hA m hm.ne'
    have he : (Rep.mkIso ((m • 𝟙 A).hom.ofBijective hb)).hom = m • 𝟙 A := Rep.hom_ext rfl
    rw [← he]
    infer_instance
  have hH : IsIso (coeffMap (m • 𝟙 A) n) :=
    ⟨coeffMap (inv (m • 𝟙 A)) n, by rw [← coeffMap_comp, IsIso.hom_inv_id,
      coeffMap_id], by rw [← coeffMap_comp, IsIso.inv_hom_id, coeffMap_id]⟩
  have hinj : Function.Injective (coeffMap (m • 𝟙 A) n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [map_zero, cohomologyMap_nsmul_id]
  exact hx

end Divisible

section DivisibleRat

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

theorem isZero_cohomology_trivial_rat {n : ℕ} (hn : 1 ≤ n) :
    IsZero (cohomology (Rep.trivial ℤ G ℚ) n) :=
  isZero_cohomology_of_bijective_nsmul _
    (fun _ hm => bijective_nsmul_of_module_rat (V := ℚ) hm) hn

end DivisibleRat

section H1Trivial

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : Type) [AddCommGroup M]

theorem cochains_d_zero_one_trivial :
    (cochains (Rep.trivial ℤ G M)).d 0 1 = 0 := by
  rw [cochains_d]
  ext f : 2
  apply Subtype.ext
  funext g
  rw [dLocallyConstant_hom_apply]
  have h : ∀ x : Fin 0 → G, (f : (Fin 0 → G) → M) x = (f : (Fin 0 → G) → M) Fin.elim0 :=
    fun x => by rw [Subsingleton.elim x Fin.elim0]
  simp [inhomogeneousCochains.d_hom_apply, h]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
variable {G M} in

theorem d_one_trivial_apply (f : (Fin 1 → G) → M) (g : Fin 2 → G) :
    (inhomogeneousCochains.d (Rep.trivial ℤ G M) 1).hom f g =
      f (fun _ => g 1) - f (fun _ => g 0 * g 1) + f (fun _ => g 0) := by
  have e1 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := by
    funext i; rw [Fin.fin_one_eq_zero i]; rfl
  have e2 : Fin.contractNth 0 (· * ·) g = fun _ => g 0 * g 1 := by
    funext i; rw [Fin.fin_one_eq_zero i]; simp [Fin.contractNth]
  have e3 : Fin.contractNth 1 (· * ·) g = fun _ => g 0 := by
    funext i; rw [Fin.fin_one_eq_zero i]; simp [Fin.contractNth]
  simp only [inhomogeneousCochains.d_hom_apply]
  simp only [e1]
  simp
  rw [e2, e3]
  abel

variable {G M} in

theorem dLocallyConstant_one_trivial_eq_zero_iff
    (f : locallyConstantCochains (Rep.trivial ℤ G M) 1) :
    (dLocallyConstant (Rep.trivial ℤ G M) 1).hom f = 0 ↔
      ∀ x y : G, f.1 (fun _ => x * y) = f.1 (fun _ => x) + f.1 (fun _ => y) := by
  constructor
  · intro h x y
    have h' := congrFun (congrArg Subtype.val h) ![x, y]
    change (inhomogeneousCochains.d (Rep.trivial ℤ G M) 1).hom f.1 ![x, y] = 0 at h'
    rw [d_one_trivial_apply] at h'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h'
    rw [← sub_eq_zero, ← neg_eq_zero, ← h']
    abel
  · intro h
    apply Subtype.ext
    funext g
    change (inhomogeneousCochains.d (Rep.trivial ℤ G M) 1).hom f.1 g = 0
    rw [d_one_trivial_apply, h (g 0) (g 1)]
    abel

theorem ker_sc_one_g_trivial :
    LinearMap.ker ((cochains (Rep.trivial ℤ G M)).sc 1).g.hom =
      LinearMap.ker (dLocallyConstant (Rep.trivial ℤ G M) 1).hom := by
  have hn : (ComplexShape.up ℕ).next 1 = 1 + 1 := by simp
  have e := (cochains (Rep.trivial ℤ G M)).d_comp_XIsoOfEq_hom hn 1
  rw [cochains_d] at e
  ext x
  simp only [LinearMap.mem_ker]
  rw [← e]
  have hinj := (ModuleCat.mono_iff_injective
    ((cochains (Rep.trivial ℤ G M)).XIsoOfEq hn).hom).1 inferInstance
  change _ ↔ ((cochains (Rep.trivial ℤ G M)).XIsoOfEq hn).hom.hom
    (((cochains (Rep.trivial ℤ G M)).d 1 _).hom x) = 0
  rw [map_eq_zero_iff _ hinj]
  rfl

variable {G M} in

theorem mem_ker_sc_one_trivial_iff (f : ((cochains (Rep.trivial ℤ G M)).sc 1).X₂) :
    f ∈ LinearMap.ker ((cochains (Rep.trivial ℤ G M)).sc 1).g.hom ↔
      ∀ x y : G, f.1 (fun _ => x * y) = f.1 (fun _ => x) + f.1 (fun _ => y) :=
  (SetLike.ext_iff.1 (ker_sc_one_g_trivial G M) f).trans
    (dLocallyConstant_one_trivial_eq_zero_iff f)

noncomputable def cocyclesOneTrivialEquiv :
    LinearMap.ker ((cochains (Rep.trivial ℤ G M)).sc 1).g.hom ≃ₗ[ℤ]
      locallyConstantHom G M where
  toFun f :=
    ⟨{ toFun := fun x => f.1.1 (fun _ => Additive.toMul x)
       map_zero' := by
         have h := (mem_ker_sc_one_trivial_iff f.1).1 f.2 1 1
         rw [mul_one] at h
         change f.1.1 (fun _ => (1 : G)) = 0
         simpa using h
       map_add' := fun x y =>
         (mem_ker_sc_one_trivial_iff f.1).1 f.2 (Additive.toMul x) (Additive.toMul y) },
     (f.1.2 : IsLocallyConstant f.1.1).comp_continuous (continuous_pi fun _ => continuous_id)⟩
  invFun χ := ⟨⟨fun v => χ.1 (Additive.ofMul (v 0)),
      (χ.2 : IsLocallyConstant fun g : G => χ.1 (Additive.ofMul g)).comp_continuous
        (continuous_apply 0)⟩,
    (mem_ker_sc_one_trivial_iff _).2 fun x y => χ.1.map_add (Additive.ofMul x) (Additive.ofMul y)⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change f.1.1 (fun _ => v 0) = f.1.1 v
    have hv : (fun _ : Fin 1 => v 0) = v := by
      funext i
      rw [Fin.fin_one_eq_zero i]
    rw [hv]
  right_inv χ := by
    apply Subtype.ext
    ext x
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def cohomologyOneIsoOfIsTrivial :
    cohomology (Rep.trivial ℤ G M) 1 ≅ ModuleCat.of ℤ (locallyConstantHom G M) :=
  ((cochains (Rep.trivial ℤ G M)).isoHomologyπ 0 1 (by simp)
      (cochains_d_zero_one_trivial G M)).symm ≪≫
    ((cochains (Rep.trivial ℤ G M)).sc 1).moduleCatCyclesIso ≪≫
    (cocyclesOneTrivialEquiv G M).toModuleIso

theorem cohomologyOneIsoOfIsTrivial_hom_cohomologyπ (z : cocycles (Rep.trivial ℤ G M) 1) (g : G) :
    ((cohomologyOneIsoOfIsTrivial G M).hom.hom ((cohomologyπ _ 1).hom z)).1 (Additive.ofMul g) =
      (((cochains (Rep.trivial ℤ G M)).iCycles 1).hom z).1 (fun _ => g) := by
  let K := cochains (Rep.trivial ℤ G M)
  let e := K.isoHomologyπ 0 1 (by simp) (cochains_d_zero_one_trivial G M)
  have h1 : e.inv.hom ((K.homologyπ 1).hom z) = z := by
    have := ConcreteCategory.congr_hom e.hom_inv_id z
    rwa [HomologicalComplex.isoHomologyπ_hom] at this
  have h2 := (K.sc 1).moduleCatCyclesIso_hom_i_apply z
  show ((cocyclesOneTrivialEquiv G M)
    ((K.sc 1).moduleCatCyclesIso.hom.hom (e.inv.hom ((K.homologyπ 1).hom z)))).1
      (Additive.ofMul g) = _
  rw [h1]
  show (((K.sc 1).moduleCatLeftHomologyData.i).hom ((K.sc 1).moduleCatCyclesIso.hom.hom z)).1
    (fun _ => g) = _
  rw [h2]
  rfl

noncomputable def cohomologyOneRatModIntIso :
    cohomology (Rep.trivial ℤ G (AddCircle (1 : ℚ))) 1 ≅ ModuleCat.of ℤ (Additive G →ₜ+ QZ) :=
  cohomologyOneIsoOfIsTrivial G (AddCircle (1 : ℚ)) ≪≫
    (locallyConstantHomQZEquiv G).toIntLinearEquiv.toModuleIso

end H1Trivial

section Profinite

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

instance : IsSmoothRep (ratSES G).X₁ :=
  inferInstanceAs (IsSmoothRep (Rep.trivial ℤ G ℤ))

instance : IsSmoothRep (ratSES G).X₂ :=
  inferInstanceAs (IsSmoothRep (Rep.trivial ℤ G ℚ))

instance : IsSmoothRep (ratSES G).X₃ :=
  inferInstanceAs (IsSmoothRep (Rep.trivial ℤ G (AddCircle (1 : ℚ))))

theorem isIso_δ_ratSES : IsIso (δ (ratSES_shortExact G) 1 2 rfl) := by
  have h1 : IsZero (cohomology (ratSES G).X₂ 1) :=
    isZero_cohomology_trivial_rat (G := G) le_rfl
  have h2 : IsZero (cohomology (ratSES G).X₂ 2) :=
    isZero_cohomology_trivial_rat (G := G) (by norm_num)
  have := (cohomology_exact₃ (ratSES_shortExact G) 1 2 rfl).mono_g
    (h1.eq_of_src _ _)
  have := (cohomology_exact₁ (ratSES_shortExact G) 1 2 rfl).epi_f
    (h2.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

noncomputable def cohomologyOneRatModIntIsoTwoInt :
    cohomology (Rep.trivial ℤ G (AddCircle (1 : ℚ))) 1 ≅ cohomology (Rep.trivial ℤ G ℤ) 2 :=
  @asIso _ _ _ _ (δ (ratSES_shortExact G) 1 2 rfl) (isIso_δ_ratSES G)

noncomputable def cohomologyTwoIntIso :
    cohomology (Rep.trivial ℤ G ℤ) 2 ≅ ModuleCat.of ℤ (Additive G →ₜ+ QZ) :=
  (cohomologyOneRatModIntIsoTwoInt G).symm ≪≫ cohomologyOneRatModIntIso G

noncomputable def cohomologyTwoIntAddEquiv :
    cohomology (Rep.trivial ℤ G ℤ) 2 ≃+ (Additive G →ₜ+ QZ) :=
  (cohomologyTwoIntIso G).toLinearEquiv.toAddEquiv

theorem cohomologyTwoIntAddEquiv_symm_apply (χ : Additive G →ₜ+ QZ) :
    (cohomologyTwoIntAddEquiv G).symm χ =
      (δ (ratSES_shortExact G) 1 2 rfl).hom
        ((cohomologyOneRatModIntIso G).inv.hom χ) :=
  rfl

end Profinite

end Langlands.ProfiniteCohomology
