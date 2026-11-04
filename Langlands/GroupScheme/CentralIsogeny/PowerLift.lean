import Langlands.AbelianScheme.Multiplication
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.SemidirectProduct
import Langlands.GroupScheme.SubgroupIntersection

/-! # Lifting a power map of a commutative subgroup through a central quotient

Let `π : G ⟶ H` be a homomorphism of group schemes over an arbitrary base whose underlying
scheme morphism is quasi-compact, flat and surjective, whose kernel is central and killed by
`N`. For every homomorphism `i : S ⟶ H` from a commutative group scheme, the map
`S ⟶ H` given by `i` after multiplication by `2 * N` lifts to `G`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralPowerLift

section GroupLemma

variable {M : Type*} [Group M] {a b c : M}

private theorem pow_mul_of_mul_eq (hba : b * a = a * b * c) (hb : Commute b c) :
    ∀ n : ℕ, b ^ n * a = a * b ^ n * c ^ n
  | 0 => by simp
  | n + 1 => by
    have hbn : b ^ n * c = c * b ^ n := (hb.symm.pow_right n).eq.symm
    calc b ^ (n + 1) * a = b * (b ^ n * a) := by rw [pow_succ', mul_assoc]
      _ = b * a * b ^ n * c ^ n := by rw [pow_mul_of_mul_eq hba hb n]; simp only [mul_assoc]
      _ = a * b * (c * b ^ n) * c ^ n := by rw [hba]; simp only [mul_assoc]
      _ = a * b ^ (n + 1) * c ^ (n + 1) := by
        rw [← hbn, pow_succ', pow_succ']; simp only [mul_assoc]

private theorem mul_pow_eq_of_mul_eq (hba : b * a = a * b * c) (ha : Commute a c)
    (hb : Commute b c) : ∀ n : ℕ, (a * b) ^ n = a ^ n * b ^ n * c ^ n.choose 2
  | 0 => by simp
  | n + 1 => by
    have hca : c ^ n.choose 2 * a = a * c ^ n.choose 2 := (ha.pow_right _).eq.symm
    have hcb : c ^ (n + n.choose 2) * b = b * c ^ (n + n.choose 2) := (hb.pow_right _).eq.symm
    calc (a * b) ^ (n + 1) = a ^ n * b ^ n * (c ^ n.choose 2 * a) * b := by
          rw [pow_succ, mul_pow_eq_of_mul_eq hba ha hb n]; simp only [mul_assoc]
      _ = a ^ n * (b ^ n * a) * c ^ n.choose 2 * b := by rw [hca]; simp only [mul_assoc]
      _ = a ^ n * a * b ^ n * (c ^ (n + n.choose 2) * b) := by
          rw [pow_mul_of_mul_eq hba hb n, pow_add]; simp only [mul_assoc]
      _ = a ^ (n + 1) * b ^ (n + 1) * c ^ (n + 1).choose 2 := by
          rw [hcb, Nat.choose_succ_succ', Nat.choose_one_right, pow_succ, pow_succ]
          simp only [mul_assoc]

/-- If the commutator `c = b⁻¹ * a⁻¹ * b * a` commutes with `a` and `b` and `c ^ N = 1`, then
the `2 * N`-th power map is multiplicative on `a` and `b`. -/
theorem mul_pow_two_mul_eq (N : ℕ) (ha : Commute a (b⁻¹ * a⁻¹ * b * a))
    (hb : Commute b (b⁻¹ * a⁻¹ * b * a)) (hN : (b⁻¹ * a⁻¹ * b * a) ^ N = 1) :
    (a * b) ^ (2 * N) = a ^ (2 * N) * b ^ (2 * N) := by
  have hba : b * a = a * b * (b⁻¹ * a⁻¹ * b * a) := by group
  rw [mul_pow_eq_of_mul_eq hba ha hb, Nat.choose_two_right]
  have h2 : 2 * N * (2 * N - 1) / 2 = N * (2 * N - 1) := by
    rw [mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  rw [h2, pow_mul (b⁻¹ * a⁻¹ * b * a) N, hN, one_pow, mul_one]

end GroupLemma

variable {B : Scheme.{u}} {G H S : GroupScheme B} [IsCommMonObj S.X]
variable (π : G ⟶ H) (i : S ⟶ H) (N : ℕ)

/-- The `2 * N`-th power of the projection from the inverse image of `S` to `G`. -/
def powerMap : (subgroupIntersection π i).X ⟶ G.X :=
  (subgroupIntersectionFst π i).hom.hom ^ (2 * N)

omit [IsCommMonObj S.X] in
theorem quasiCompact_snd [QuasiCompact π.hom.hom.left] :
    QuasiCompact (subgroupIntersectionSnd π i).hom.hom.left :=
  MorphismProperty.of_isPullback (subgroupIntersection_isPullback_scheme π i) ‹_›

omit [IsCommMonObj S.X] in
theorem flat_snd [Flat π.hom.hom.left] : Flat (subgroupIntersectionSnd π i).hom.hom.left :=
  MorphismProperty.of_isPullback (subgroupIntersection_isPullback_scheme π i) ‹_›

omit [IsCommMonObj S.X] in
theorem surjective_snd [Surjective π.hom.hom.left] :
    Surjective (subgroupIntersectionSnd π i).hom.hom.left :=
  MorphismProperty.of_isPullback (subgroupIntersection_isPullback_scheme π i) ‹_›

variable {π} {N}

theorem isMonHom_powerMap
    (hc : ∀ (T : Over B) (x : T ⟶ G.X), x ≫ π.hom.hom = 1 → x ∈ (center G).carrier T)
    (hN : ∀ (T : Over B) (x : T ⟶ G.X), x ≫ π.hom.hom = 1 → x ^ N = 1) :
    IsMonHom (powerMap π i N) := by
  refine Semidirect.isMonHom_of_mul_comp _ fun {X} x y => ?_
  let fst := (subgroupIntersectionFst π i).hom.hom
  let snd := (subgroupIntersectionSnd π i).hom.hom
  have hw : fst ≫ π.hom.hom = snd ≫ i.hom.hom :=
    congrArg (fun f => f.hom.hom) (subgroupIntersection_condition π i)
  set a : X ⟶ G.X := x ≫ fst
  set b : X ⟶ G.X := y ≫ fst
  have hab : Commute (a ≫ π.hom.hom) (b ≫ π.hom.hom) := by
    have hs : Commute (x ≫ snd) (y ≫ snd) := Commute.all _ _
    have := hs.map (IsMonHom.monoidHom i.hom.hom X)
    simpa only [IsMonHom.monoidHom, MonoidHom.coe_mk, OneHom.coe_mk, a, b, Category.assoc,
      hw] using this
  let c : X ⟶ G.X := b⁻¹ * a⁻¹ * b * a
  have hcπ : c ≫ π.hom.hom = 1 := by
    calc c ≫ π.hom.hom = (b ≫ π.hom.hom)⁻¹ * (a ≫ π.hom.hom)⁻¹ * (b ≫ π.hom.hom) *
          (a ≫ π.hom.hom) := by simp only [c, MonObj.mul_comp, GrpObj.inv_comp]
      _ = ((a ≫ π.hom.hom) * (b ≫ π.hom.hom))⁻¹ * ((b ≫ π.hom.hom) * (a ≫ π.hom.hom)) := by
          group
      _ = 1 := by rw [hab.eq, inv_mul_cancel]
  have hcc := hc X c hcπ
  change (x * y) ≫ fst ^ (2 * N) = (x ≫ fst ^ (2 * N)) * (y ≫ fst ^ (2 * N))
  rw [MonObj.comp_pow, MonObj.comp_pow, MonObj.comp_pow, MonObj.mul_comp]
  exact mul_pow_two_mul_eq N (commute_of_mem_center hcc a).symm
    (commute_of_mem_center hcc b).symm (hN X c hcπ)

variable (π) in
/-- The `2 * N`-th power map as an actual homomorphism from the inverse image of `S`. -/
def powerHom
    (hc : ∀ (T : Over B) (x : T ⟶ G.X), x ≫ π.hom.hom = 1 → x ∈ (center G).carrier T)
    (hN : ∀ (T : Over B) (x : T ⟶ G.X), x ≫ π.hom.hom = 1 → x ^ N = 1) :
    subgroupIntersection π i ⟶ G :=
  have := isMonHom_powerMap i hc hN
  Grp.homMk (powerMap π i N)

theorem powerHom_hom
    (hc : ∀ (T : Over B) (x : T ⟶ G.X), x ≫ π.hom.hom = 1 → x ∈ (center G).carrier T)
    (hN : ∀ (T : Over B) (x : T ⟶ G.X), x ≫ π.hom.hom = 1 → x ^ N = 1) :
    (powerHom π i hc hN).hom.hom = (subgroupIntersectionFst π i).hom.hom ^ (2 * N) :=
  rfl

/-- The power homomorphism kills the full kernel of the projection to `S`. -/
theorem kernelι_comp_powerHom
    (hc : ∀ (T : Over B) (x : T ⟶ G.X), x ≫ π.hom.hom = 1 → x ∈ (center G).carrier T)
    (hN : ∀ (T : Over B) (x : T ⟶ G.X), x ≫ π.hom.hom = 1 → x ^ N = 1) :
    kernelι (subgroupIntersectionSnd π i) ≫ powerHom π i hc hN = 0 := by
  apply Grp.hom_ext
  let ιk := (kernelι (subgroupIntersectionSnd π i)).hom.hom
  let x : (kernel (subgroupIntersectionSnd π i)).X ⟶ G.X :=
    ιk ≫ (subgroupIntersectionFst π i).hom.hom
  have hx : x ≫ π.hom.hom = 1 := by
    have hw : (subgroupIntersectionFst π i).hom.hom ≫ π.hom.hom =
        (subgroupIntersectionSnd π i).hom.hom ≫ i.hom.hom :=
      congrArg (fun f => f.hom.hom) (subgroupIntersection_condition π i)
    change ιk ≫ (subgroupIntersectionFst π i).hom.hom ≫ π.hom.hom = 1
    rw [hw, ← Category.assoc, (kernel_isPullback (subgroupIntersectionSnd π i)).w,
      Category.assoc, IsMonHom.one_hom]
    rfl
  change ιk ≫ (subgroupIntersectionFst π i).hom.hom ^ (2 * N) = toUnit _ ≫ η[G.X]
  rw [MonObj.comp_pow, mul_comm, pow_mul, hN _ x hx, one_pow]
  rfl

/-- **Power lift.** If `π` is quasi-compact, flat and surjective with central kernel killed by
`N`, then for every homomorphism `i : S ⟶ H` from a commutative group scheme there is a
homomorphism `Φ : S ⟶ G` with `Φ ≫ π = [2 * N]_S ≫ i`. -/
theorem exists_comp_eq_multiplication_comp
    [QuasiCompact π.hom.hom.left] [Flat π.hom.hom.left] [Surjective π.hom.hom.left]
    (hc : ∀ (T : Over B) (x : T ⟶ G.X), x ≫ π.hom.hom = 1 → x ∈ (center G).carrier T)
    (hN : ∀ (T : Over B) (x : T ⟶ G.X), x ≫ π.hom.hom = 1 → x ^ N = 1) :
    ∃ Φ : S ⟶ G, Φ ≫ π = multiplication S (2 * N : ℕ) ≫ i := by
  let p := subgroupIntersectionSnd π i
  have := quasiCompact_snd π i
  have := flat_snd π i
  have := surjective_snd π i
  refine ⟨FpqcHomDescent.hom p (powerHom π i hc hN) (kernelι_comp_powerHom i hc hN), ?_⟩
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi p.hom.hom.left).mp
  have hfac := congrArg (fun f => f.hom.hom)
    (FpqcHomDescent.fac p (powerHom π i hc hN) (kernelι_comp_powerHom i hc hN))
  have hw : (subgroupIntersectionFst π i).hom.hom ≫ π.hom.hom = p.hom.hom ≫ i.hom.hom :=
    congrArg (fun f => f.hom.hom) (subgroupIntersection_condition π i)
  have key : p.hom.hom ≫ (FpqcHomDescent.hom p (powerHom π i hc hN)
      (kernelι_comp_powerHom i hc hN)).hom.hom ≫ π.hom.hom =
      p.hom.hom ≫ (multiplication S (2 * N : ℕ)).hom.hom ≫ i.hom.hom := by
    rw [← Category.assoc, ← Grp.comp_hom_hom, hfac, ← Category.assoc, points_multiplication]
    rw [powerHom_hom, MonObj.pow_comp, hw, zpow_natCast, MonObj.pow_comp]
  exact congrArg (fun f => f.left) key

/-- The power lift for a central isogeny whose actual scheme-theoretic kernel is killed by `N`. -/
theorem _root_.Langlands.GroupScheme.IsCentralIsogeny.exists_comp_eq_multiplication_comp
    (hπ : IsCentralIsogeny π) (hN : ∀ (T : Over B) (x : T ⟶ (kernel π).X), x ^ N = 1) :
    ∃ Φ : S ⟶ G, Φ ≫ π = multiplication S (2 * N : ℕ) ≫ i := by
  have := hπ.isFinite
  have := hπ.flat
  have := hπ.surjective
  refine CentralPowerLift.exists_comp_eq_multiplication_comp i (fun _ _ hx => hπ.mem_center_of_comp_eq_one hx)
    fun T x hx => ?_
  let y := (kernelPointsEquiv π T).symm ⟨x, hx⟩
  have hy : y ≫ (kernelι π).hom.hom = x :=
    congrArg Subtype.val ((kernelPointsEquiv π T).apply_symm_apply ⟨x, hx⟩)
  rw [← hy, ← MonObj.pow_comp, hN T y, MonObj.one_comp]

end Langlands.GroupScheme.CentralPowerLift
