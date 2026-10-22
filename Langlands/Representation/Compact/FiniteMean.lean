import Mathlib.RepresentationTheory.Invariants
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Finite orbit means

Algebraic infrastructure for compact averaging. Only finite sums in complex
modules are used; the modules carry no topology.
-/

namespace Langlands.Compact

open scoped BigOperators

universe uG uV uW uX uY

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Normalized finite sum in a complex module. -/
noncomputable def finiteMean {X : Type uX} [Fintype X] (f : X → V) : V :=
  (Fintype.card X : ℂ)⁻¹ • ∑ x, f x

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
    finiteMean (h ∘ f) = finiteMean h := by
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
  have hsum : (∑ x, h (f x)) = (c : ℂ) • ∑ y, h y := by
    rw [← Fintype.sum_fiberwise f (fun x => h (f x))]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro y _
    calc
      (∑ x : {x // f x = y}, h (f x)) = ∑ _ : {x // f x = y}, h y :=
        Finset.sum_congr rfl (fun x _ => congrArg h x.property)
      _ = (c : ℂ) • h y := by
        simp only [Finset.sum_const, Finset.card_univ, hfiber, Nat.cast_smul_eq_nsmul]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  unfold finiteMean
  change (Fintype.card X : ℂ)⁻¹ • (∑ x, h (f x)) = _
  rw [hsum, smul_smul, hcard, Nat.cast_mul, mul_inv_rev]
  congr 1
  field_simp

/-- The action associated to an algebraic representation, installed locally. -/
abbrev representationAction (ρ : Representation ℂ G V) : MulAction G V where
  smul g v := ρ g v
  one_smul v := by change ρ 1 v = v; simp
  mul_smul g h v := by change ρ (g * h) v = ρ g (ρ h v); simp

/-- The orbit of a vector, with no topology on the vector space. -/
def orbit (ρ : Representation ℂ G V) (v : V) : Set V :=
  Set.range (fun g : G => ρ g v)

instance orbitNonempty (ρ : Representation ℂ G V) (v : V) :
    Nonempty (orbit ρ v) :=
  ⟨⟨v, ⟨1, by simp⟩⟩⟩

instance orbitAction (ρ : Representation ℂ G V) (v : V) :
    MulAction G (orbit ρ v) where
  smul g x := ⟨ρ g x.val, by
    obtain ⟨h, hh⟩ := x.property
    exact ⟨g * h, by simp [hh]⟩⟩
  one_smul x := Subtype.ext (by change ρ 1 x.val = x.val; simp)
  mul_smul g h x := Subtype.ext (by change ρ (g * h) x.val = ρ g (ρ h x.val); simp)

instance orbitPretransitive (ρ : Representation ℂ G V) (v : V) :
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
noncomputable def orbitMean (ρ : Representation ℂ G V) (v : V) : V :=
  (Nat.card (orbit ρ v) : ℂ)⁻¹ • ∑ᶠ x : orbit ρ v, x.val

theorem orbitMean_eq_finiteMean (ρ : Representation ℂ G V) (v : V)
    [Fintype (orbit ρ v)] :
    orbitMean ρ v = finiteMean (fun x : orbit ρ v => x.val) := by
  simp only [orbitMean, finiteMean, Nat.card_eq_fintype_card, finsum_eq_sum_of_fintype]

/-- A linear intertwiner induces the corresponding equivariant map of orbits. -/
def orbitMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (f : V →ₗ[ℂ] W) (hf : ∀ g v, f (ρ g v) = σ g (f v)) (v : V) :
    orbit ρ v →[G] orbit σ (f v) where
  toFun x := ⟨f x.val, by
    obtain ⟨g, hg⟩ := x.property
    exact ⟨g, (hf g v).symm.trans (congrArg f hg)⟩⟩
  map_smul' g x := Subtype.ext (hf g x.val)

theorem orbitMean_map (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (f : V →ₗ[ℂ] W) (hf : ∀ g v, f (ρ g v) = σ g (f v)) (v : V)
    [sourceFinite : Finite (orbit ρ v)] [targetFinite : Finite (orbit σ (f v))] :
    f (orbitMean ρ v) = orbitMean σ (f v) := by
  classical
  let := Fintype.ofFinite (orbit ρ v)
  let := Fintype.ofFinite (orbit σ (f v))
  rw [orbitMean_eq_finiteMean, orbitMean_eq_finiteMean]
  change f ((Fintype.card (orbit ρ v) : ℂ)⁻¹ • ∑ x : orbit ρ v, x.val) = _
  rw [map_smul, map_sum]
  exact finiteMean_comp (orbitMap ρ σ f hf v) (fun x => x.val)

/-- A pair of finite orbits has a finite orbit for the product representation. -/
theorem finite_orbit_prod (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
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

theorem orbitMean_add (ρ : Representation ℂ G V) (v w : V)
    [Finite (orbit ρ v)] [Finite (orbit ρ w)] [Finite (orbit ρ (v + w))] :
    orbitMean ρ (v + w) = orbitMean ρ v + orbitMean ρ w := by
  let := finite_orbit_prod ρ ρ v w
  have hfst := orbitMean_map (ρ.prod ρ) ρ (LinearMap.fst ℂ V V)
    (fun _ _ => rfl) (v, w) (targetFinite := inferInstanceAs (Finite (orbit ρ v)))
  have hsnd := orbitMean_map (ρ.prod ρ) ρ (LinearMap.snd ℂ V V)
    (fun _ _ => rfl) (v, w) (targetFinite := inferInstanceAs (Finite (orbit ρ w)))
  have hadd := orbitMean_map (ρ.prod ρ) ρ
    (LinearMap.fst ℂ V V + LinearMap.snd ℂ V V)
    (fun g x => (map_add (ρ g) x.1 x.2).symm) (v, w)
    (targetFinite := inferInstanceAs (Finite (orbit ρ (v + w))))
  exact hadd.symm.trans (congrArg₂ (· + ·) hfst hsnd)

theorem orbitMean_smul (ρ : Representation ℂ G V) (c : ℂ) (v : V)
    [Finite (orbit ρ v)] [Finite (orbit ρ (c • v))] :
    orbitMean ρ (c • v) = c • orbitMean ρ v := by
  let f : V →ₗ[ℂ] V :=
    { toFun := fun x => c • x
      map_add' := smul_add c
      map_smul' := fun a x => smul_comm c a x }
  exact (orbitMean_map ρ ρ f
    (fun g x => (map_smul (ρ g) c x).symm) v
    (targetFinite := inferInstanceAs (Finite (orbit ρ (c • v))))).symm

end Langlands.Compact
