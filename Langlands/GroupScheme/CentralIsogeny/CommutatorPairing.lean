import Langlands.GroupScheme.CentralIsogeny.CommutatorDescent
import Langlands.GroupScheme.ActionDescent
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Rational.SplitUnipotentStableCenter

/-! # The commutator pairing of a central extension with commutative quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Group

variable {M : Type*} [Group M]

/-- A central commutator makes the commutator multiplicative in the first argument. -/
theorem commutator_mul_left_of_commute (a b c : M)
    (h : ∀ g, Commute (b * c * b⁻¹ * c⁻¹) g) :
    (a * b) * c * (a * b)⁻¹ * c⁻¹ = (a * c * a⁻¹ * c⁻¹) * (b * c * b⁻¹ * c⁻¹) := by
  calc (a * b) * c * (a * b)⁻¹ * c⁻¹
      = (a * (b * c * b⁻¹ * c⁻¹)) * (c * a⁻¹ * c⁻¹) := by group
    _ = ((b * c * b⁻¹ * c⁻¹) * a) * (c * a⁻¹ * c⁻¹) := by rw [(h a).eq]
    _ = (b * c * b⁻¹ * c⁻¹) * (a * c * a⁻¹ * c⁻¹) := by group
    _ = (a * c * a⁻¹ * c⁻¹) * (b * c * b⁻¹ * c⁻¹) := (h _).eq

end Group

namespace CommutatorDescent

variable {S : Scheme.{u}} {C G : GroupScheme S} (π : C ⟶ G)
  [QuasiCompact π.hom.hom.left] [Flat π.hom.hom.left] [Surjective π.hom.hom.left]

/-- Equality of maps out of a test scheme can be checked after locally lifting
two quotient points. -/
theorem hom_ext_of_local_quotient_lift₂ {T Y : Over S} (x y : T ⟶ G.X) (f f' : T ⟶ Y)
    (he : ∀ (V : Over S) (b : V ⟶ T) (g h : V ⟶ C.X),
      b ≫ x = g ≫ π.hom.hom → b ≫ y = h ≫ π.hom.hom → b ≫ f = b ≫ f') :
    f = f' := by
  apply AutomorphicAction.hom_ext_of_local_quotient_lift π x f f'
  intro V b g hg
  apply AutomorphicAction.hom_ext_of_local_quotient_lift π (b ≫ y) (b ≫ f) (b ≫ f')
  intro V' b' h hh
  have := he V' (b' ≫ b) (b' ≫ g) h
    (by rw [Category.assoc, hg, Category.assoc]) (by rw [Category.assoc, hh])
  simpa only [Category.assoc] using this

/-- Equality of maps out of a test scheme can be checked after locally lifting
three quotient points. -/
theorem hom_ext_of_local_quotient_lift₃ {T Y : Over S} (x y z : T ⟶ G.X) (f f' : T ⟶ Y)
    (he : ∀ (V : Over S) (b : V ⟶ T) (g h l : V ⟶ C.X),
      b ≫ x = g ≫ π.hom.hom → b ≫ y = h ≫ π.hom.hom → b ≫ z = l ≫ π.hom.hom →
        b ≫ f = b ≫ f') :
    f = f' := by
  apply AutomorphicAction.hom_ext_of_local_quotient_lift π x f f'
  intro V b g hg
  apply hom_ext_of_local_quotient_lift₂ π (b ≫ y) (b ≫ z) (b ≫ f) (b ≫ f')
  intro V' b' h l hh hl
  have := he V' (b' ≫ b) (b' ≫ g) h l
    (by rw [Category.assoc, hg, Category.assoc]) (by rw [Category.assoc, hh])
    (by rw [Category.assoc, hl])
  simpa only [Category.assoc] using this

variable (hπ : IsCentral (kernelι π))

/-- The descended commutator is natural in the test scheme. -/
theorem lift_hom_naturality {T T' : Over S} (b : T' ⟶ T) (x y : T ⟶ G.X) :
    b ≫ (lift x y ≫ hom π hπ) = lift (b ≫ x) (b ≫ y) ≫ hom π hπ := by
  rw [← Category.assoc, comp_lift]

/-- The descended commutator on two lifted points, in the form used below. -/
theorem lift_hom_of_eq {T : Over S} {x y : T ⟶ G.X} {g h : T ⟶ C.X}
    (hg : x = g ≫ π.hom.hom) (hh : y = h ≫ π.hom.hom) :
    lift x y ≫ hom π hπ = g * h * g⁻¹ * h⁻¹ := by
  rw [hg, hh, lift_hom]

/-- Equivariance of the descended commutator under compatible automorphic actions
on the extension and on the quotient. -/
theorem lift_hom_act {H : GroupScheme S} (a : AutomorphicAction H C)
    (b : AutomorphicAction H G)
    (hab : ∀ (T : Over S) (h : T ⟶ H.X) (g : T ⟶ C.X),
      b.act h (g ≫ π.hom.hom) = a.act h g ≫ π.hom.hom)
    {T : Over S} (h : T ⟶ H.X) (x y : T ⟶ G.X) :
    lift (b.act h x) (b.act h y) ≫ hom π hπ = a.act h (lift x y ≫ hom π hπ) := by
  apply hom_ext_of_local_quotient_lift₂ π x y
  intro V t g g' hg hg'
  rw [lift_hom_naturality, a.naturality, lift_hom_naturality, b.naturality, b.naturality,
    hg, hg', hab, hab, lift_hom, lift_hom, a.act_mul_right,
    a.act_mul_right, a.act_mul_right, a.act_inv, a.act_inv]

/-- The descended commutator of a pair with the identity in the first slot. -/
theorem lift_one_hom {T : Over S} (y : T ⟶ G.X) : lift (1 : T ⟶ G.X) y ≫ hom π hπ = 1 := by
  apply AutomorphicAction.hom_ext_of_local_quotient_lift π y
  intro V b h hh
  rw [lift_hom_naturality, MonObj.comp_one, MonObj.comp_one,
    show (1 : V ⟶ G.X) = (1 : V ⟶ C.X) ≫ π.hom.hom from (MonObj.one_comp _).symm, hh,
    lift_hom]
  group

/-- The descended commutator of a pair with the identity in the second slot. -/
theorem lift_hom_one {T : Over S} (x : T ⟶ G.X) : lift x (1 : T ⟶ G.X) ≫ hom π hπ = 1 := by
  apply AutomorphicAction.hom_ext_of_local_quotient_lift π x
  intro V b g hg
  rw [lift_hom_naturality, MonObj.comp_one, MonObj.comp_one,
    show (1 : V ⟶ G.X) = (1 : V ⟶ C.X) ≫ π.hom.hom from (MonObj.one_comp _).symm, hg,
    lift_hom]
  group

/-- The descended commutator is alternating. -/
theorem lift_self_hom {T : Over S} (x : T ⟶ G.X) : lift x x ≫ hom π hπ = 1 := by
  apply AutomorphicAction.hom_ext_of_local_quotient_lift π x
  intro V b g hg
  rw [lift_hom_naturality, MonObj.comp_one, hg, lift_hom]
  group

/-- Exchanging the two points inverts the descended commutator. -/
theorem lift_swap_hom {T : Over S} (x y : T ⟶ G.X) :
    lift y x ≫ hom π hπ = (lift x y ≫ hom π hπ)⁻¹ := by
  apply hom_ext_of_local_quotient_lift₂ π x y
  intro V b g h hg hh
  rw [lift_hom_naturality, GrpObj.comp_inv, lift_hom_naturality, hg, hh, lift_hom, lift_hom]
  group

section Commutative

variable (hG : ∀ (T : Over S) (x y : T ⟶ G.X), Commute x y)

include hG

/-- For a commutative quotient, the descended commutator takes values in the
actual kernel. -/
theorem lift_hom_comp {T : Over S} (x y : T ⟶ G.X) :
    (lift x y ≫ hom π hπ) ≫ π.hom.hom = 1 := by
  rw [Category.assoc, hom_comp, commutatorMap_lift]
  simp only [Grp.id_hom_hom, Category.comp_id]
  rw [(hG T x y).eq]
  group

/-- For a commutative quotient, the descended commutator lies in the range of
the actual kernel inclusion. -/
theorem lift_hom_mem_range_kernelι {T : Over S} (x y : T ⟶ G.X) :
    lift x y ≫ hom π hπ ∈ (SubgroupFunctor.range (kernelι π)).carrier T :=
  (mem_range_kernelι_iff π _).mpr (lift_hom_comp π hπ hG x y)

/-- For a commutative quotient, the descended commutator is central. -/
theorem lift_hom_commute {T : Over S} (x y : T ⟶ G.X) (z : T ⟶ C.X) :
    Commute (lift x y ≫ hom π hπ) z :=
  commute_of_mem_center
    ((isCentral_kernelι_iff π).mp hπ T _ (lift_hom_comp π hπ hG x y)) z

/-- For a commutative quotient, the descended commutator is multiplicative in
the first point. -/
theorem lift_mul_hom {T : Over S} (x x' y : T ⟶ G.X) :
    lift (x * x') y ≫ hom π hπ = (lift x y ≫ hom π hπ) * (lift x' y ≫ hom π hπ) := by
  apply hom_ext_of_local_quotient_lift₃ π x x' y
  intro V b g g' h hg hg' hh
  have hc : ∀ l, Commute (g' * h * g'⁻¹ * h⁻¹) l := by
    intro l
    rw [← lift_hom_of_eq π hπ (rfl : g' ≫ π.hom.hom = _) (rfl : h ≫ π.hom.hom = _)]
    exact lift_hom_commute π hπ hG _ _ l
  rw [lift_hom_naturality, MonObj.comp_mul, MonObj.comp_mul, lift_hom_naturality,
    lift_hom_naturality, hg, hg', hh, ← MonObj.mul_comp, lift_hom, lift_hom, lift_hom,
    commutator_mul_left_of_commute g g' h hc]

/-- For a commutative quotient, the descended commutator is multiplicative in
the second point. -/
theorem lift_hom_mul {T : Over S} (x y y' : T ⟶ G.X) :
    lift x (y * y') ≫ hom π hπ = (lift x y ≫ hom π hπ) * (lift x y' ≫ hom π hπ) := by
  apply hom_ext_of_local_quotient_lift₃ π x y y'
  intro V b g h h' hg hh hh'
  have hc : ∀ l, Commute (g * h' * g⁻¹ * h'⁻¹) l := by
    intro l
    rw [← lift_hom_of_eq π hπ (rfl : g ≫ π.hom.hom = _) (rfl : h' ≫ π.hom.hom = _)]
    exact lift_hom_commute π hπ hG _ _ l
  rw [lift_hom_naturality, MonObj.comp_mul, MonObj.comp_mul, lift_hom_naturality,
    lift_hom_naturality, hg, hh, hh', ← MonObj.mul_comp, lift_hom, lift_hom, lift_hom]
  exact RationalDensity.commutatorElement_mul_of_commute g h h' hc

section Pairing

variable {K : GroupScheme S} {κ : K ⟶ C}
  (hκ : (SubgroupFunctor.range (kernelι π)).IsRepresentedBy κ)

include hκ

/-- The commutator pairing of a central extension with commutative quotient, with values in a
group scheme `K` representing the kernel: on lifted points it is the commutator of the lifts. -/
def pairing : G.X ⊗ G.X ⟶ K.X :=
  (hκ.pointsEquiv _).symm ⟨hom π hπ, by
    simpa only [lift_fst_snd, Category.id_comp] using
      lift_hom_mem_range_kernelι π hπ hG (fst G.X G.X) (snd G.X G.X)⟩

/-- The pairing followed by the kernel inclusion is the descended commutator. -/
@[reassoc]
theorem pairing_comp : pairing π hπ hG hκ ≫ κ.hom.hom = hom π hπ :=
  hκ.pointsEquiv_symm_comp _

/-- The pairing of two points, followed by the kernel inclusion. -/
theorem lift_pairing_comp {T : Over S} (x y : T ⟶ G.X) :
    (lift x y ≫ pairing π hπ hG hκ) ≫ κ.hom.hom = lift x y ≫ hom π hπ := by
  rw [Category.assoc, pairing_comp]

/-- On lifted points, the pairing followed by the kernel inclusion is the commutator of the
lifts. -/
theorem lift_pairing {T : Over S} (g h : T ⟶ C.X) :
    (lift (g ≫ π.hom.hom) (h ≫ π.hom.hom) ≫ pairing π hπ hG hκ) ≫ κ.hom.hom =
      g * h * g⁻¹ * h⁻¹ := by
  rw [lift_pairing_comp, lift_hom]

/-- The pairing is natural in the test scheme. -/
theorem lift_pairing_naturality {T T' : Over S} (b : T' ⟶ T) (x y : T ⟶ G.X) :
    b ≫ (lift x y ≫ pairing π hπ hG hκ) = lift (b ≫ x) (b ≫ y) ≫ pairing π hπ hG hκ := by
  rw [← Category.assoc, comp_lift]

/-- The pairing is multiplicative in the first point. -/
theorem lift_mul_pairing {T : Over S} (x x' y : T ⟶ G.X) :
    lift (x * x') y ≫ pairing π hπ hG hκ =
      (lift x y ≫ pairing π hπ hG hκ) * (lift x' y ≫ pairing π hπ hG hκ) := by
  have : Mono κ.hom.hom := hκ.1
  apply (cancel_mono κ.hom.hom).mp
  rw [MonObj.mul_comp, lift_pairing_comp, lift_pairing_comp, lift_pairing_comp,
    lift_mul_hom π hπ hG]

/-- The pairing is multiplicative in the second point. -/
theorem lift_pairing_mul {T : Over S} (x y y' : T ⟶ G.X) :
    lift x (y * y') ≫ pairing π hπ hG hκ =
      (lift x y ≫ pairing π hπ hG hκ) * (lift x y' ≫ pairing π hπ hG hκ) := by
  have : Mono κ.hom.hom := hκ.1
  apply (cancel_mono κ.hom.hom).mp
  rw [MonObj.mul_comp, lift_pairing_comp, lift_pairing_comp, lift_pairing_comp,
    lift_hom_mul π hπ hG]

/-- The pairing vanishes when the first point is the identity. -/
theorem lift_one_pairing {T : Over S} (y : T ⟶ G.X) :
    lift (1 : T ⟶ G.X) y ≫ pairing π hπ hG hκ = 1 := by
  have : Mono κ.hom.hom := hκ.1
  apply (cancel_mono κ.hom.hom).mp
  rw [lift_pairing_comp, lift_one_hom, MonObj.one_comp]

/-- The pairing vanishes when the second point is the identity. -/
theorem lift_pairing_one {T : Over S} (x : T ⟶ G.X) :
    lift x (1 : T ⟶ G.X) ≫ pairing π hπ hG hκ = 1 := by
  have : Mono κ.hom.hom := hκ.1
  apply (cancel_mono κ.hom.hom).mp
  rw [lift_pairing_comp, lift_hom_one, MonObj.one_comp]

/-- The pairing is alternating. -/
theorem lift_self_pairing {T : Over S} (x : T ⟶ G.X) :
    lift x x ≫ pairing π hπ hG hκ = 1 := by
  have : Mono κ.hom.hom := hκ.1
  apply (cancel_mono κ.hom.hom).mp
  rw [lift_pairing_comp, lift_self_hom, MonObj.one_comp]

/-- Exchanging the two points inverts the pairing. -/
theorem lift_swap_pairing {T : Over S} (x y : T ⟶ G.X) :
    lift y x ≫ pairing π hπ hG hκ = (lift x y ≫ pairing π hπ hG hκ)⁻¹ := by
  have : Mono κ.hom.hom := hκ.1
  apply (cancel_mono κ.hom.hom).mp
  rw [GrpObj.inv_comp, lift_pairing_comp, lift_pairing_comp, lift_swap_hom]

/-- Equivariance of the pairing under compatible automorphic actions on the extension, the
quotient and the kernel. -/
theorem lift_pairing_act {H : GroupScheme S} (a : AutomorphicAction H C)
    (b : AutomorphicAction H G) (c : AutomorphicAction H K)
    (hab : ∀ (T : Over S) (h : T ⟶ H.X) (g : T ⟶ C.X),
      b.act h (g ≫ π.hom.hom) = a.act h g ≫ π.hom.hom)
    (hac : ∀ (T : Over S) (h : T ⟶ H.X) (l : T ⟶ K.X),
      a.act h (l ≫ κ.hom.hom) = c.act h l ≫ κ.hom.hom)
    {T : Over S} (h : T ⟶ H.X) (x y : T ⟶ G.X) :
    lift (b.act h x) (b.act h y) ≫ pairing π hπ hG hκ =
      c.act h (lift x y ≫ pairing π hπ hG hκ) := by
  have : Mono κ.hom.hom := hκ.1
  apply (cancel_mono κ.hom.hom).mp
  rw [lift_pairing_comp, lift_hom_act π hπ a b hab, ← hac, lift_pairing_comp]

end Pairing

end Commutative

omit [QuasiCompact π.hom.hom.left] [Flat π.hom.hom.left] [Surjective π.hom.hom.left] in
/-- The actual kernel inclusion represents its own range. -/
theorem isRepresentedBy_kernelι :
    (SubgroupFunctor.range (kernelι π)).IsRepresentedBy (kernelι π) :=
  ⟨inferInstance, rfl⟩

end CommutatorDescent

/-- A homomorphism whose kernel is a subgroup functor commuting with every point has central
kernel. -/
theorem isCentral_kernelι_of_commute {S : Scheme.{u}} {C G : GroupScheme S} (π : C ⟶ G)
    {N : SubgroupFunctor C} (hN : SubgroupFunctor.range (kernelι π) = N)
    (hc : ∀ (T : Over S) (x y : T ⟶ C.X), x ∈ N.carrier T → Commute x y) :
    IsCentral (kernelι π) := by
  apply (isCentral_kernelι_iff π).mpr
  intro T x hx T' a h
  apply hc T' _ h
  rw [← hN]
  exact (SubgroupFunctor.range (kernelι π)).comp_mem a ((mem_range_kernelι_iff π x).mpr hx)

end Langlands.GroupScheme
