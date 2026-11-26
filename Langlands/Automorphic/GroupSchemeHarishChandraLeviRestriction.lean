import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Automorphic.GroupSchemeSliceAdelicGrowthReduction
import Langlands.Global.AdelicIwasawaHeight
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.AdelicParabolicQuotient
import Langlands.GroupScheme.Absolute.SolvableUnipotentFactorizationOfQuotient
import Langlands.GroupScheme.Rational.LeviMultiplication
import Mathlib.RingTheory.Artinian.Module

/-! # Finite Levi restrictions on the adelic parabolic quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme AdelicGroupPoints

private theorem exists_finset_detects_zero {X : Type*} (E : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ E] :
    ∃ t : Finset X, ∀ f ∈ E, (∀ x ∈ t, f x = 0) → f = 0 := by
  classical
  let K (t : Finset X) : Submodule ℂ E :=
    ⨅ x ∈ t, LinearMap.ker ((LinearMap.proj x).comp E.subtype)
  have hK (t : Finset X) (f : E) : f ∈ K t ↔ ∀ x ∈ t, f.val x = 0 := by
    simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.subtype_apply]
  obtain ⟨_, ⟨t, rfl⟩, hmin⟩ :=
    IsArtinian.set_has_minimal (Set.range K) ⟨K ∅, ∅, rfl⟩
  refine ⟨t, fun f hf hz => funext fun x => ?_⟩
  have hle : K (insert x t) ≤ K t := fun w hw => (hK t w).mpr fun y hy =>
    (hK _ w).mp hw y (Finset.mem_insert_of_mem hy)
  have heq : K (insert x t) = K t := eq_of_le_of_not_lt hle (hmin _ ⟨insert x t, rfl⟩)
  have hw : (⟨f, hf⟩ : E) ∈ K (insert x t) := heq.symm ▸ (hK t ⟨f, hf⟩).mpr hz
  exact (hK _ _).mp hw x (Finset.mem_insert_self x t)

variable {F : Type u} [Field F] [NumberField F]
  {G Q M V : GroupScheme (Spec (CommRingCat.of F))}
  {q : Q ⟶ G}

/-- Restriction of the right translate by `t` to the actual adelic Levi points. -/
def translatedLeviRestriction (l : M ⟶ Q) (t : AdelicGroupPoints F G) :
    (AdelicGroupPoints F G → ℂ) →ₗ[ℂ] (AdelicGroupPoints F M → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun m => map F M G (l ≫ q) m * t

@[simp] theorem translatedLeviRestriction_apply (l : M ⟶ Q) (t : AdelicGroupPoints F G)
    (f : AdelicGroupPoints F G → ℂ) (m : AdelicGroupPoints F M) :
    translatedLeviRestriction (q := q) l t f m = f (map F M G (l ≫ q) m * t) := rfl

variable [IsAffine G.X.left] (iV : V ⟶ Q) (l : M ⟶ Q)
  {K : Subgroup (AdelicGroupPoints F G)}

local notation "K∞" => K.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G))

omit [IsAffine G.X.left] in
private theorem exists_unipotent_levi_compact [IsIso (subgroupMultiplication l iV)]
    (hK : IsIwasawaCompact q K) (g : AdelicGroupPoints F G) :
    ∃ (v : AdelicGroupPoints F V) (m : AdelicGroupPoints F M) (k : K),
      map F V G (iV ≫ q) v * (map F M G (l ≫ q) m * (k : AdelicGroupPoints F G)) = g := by
  obtain ⟨x, k, hk, rfl⟩ := hK.exists_eq g
  let : IsIso (subgroupMultiplication iV l) :=
    (isIso_subgroupMultiplication_reverse_iff l iV).mp inferInstance
  obtain ⟨v, m, h⟩ := exists_factorization_of_isIso_subgroupMultiplication iV l x
  change map F V Q iV v * map F M Q l m = x at h
  refine ⟨v, m, ⟨k, hk⟩, ?_⟩
  rw [← h, map_mul, ← mul_assoc, map_comp_apply_of_hom, map_comp_apply_of_hom]

private theorem compact_infinite_mem (hK : IsMaximalCompactSubgroup F G K) (k : K) :
    infinite F G k.val ∈ K∞ := by
  exact ((hK.mem_iff k.val).mp k.property).1

/-- Bounds for the translated Levi restrictions imply finiteness on the parabolic quotient.
The evaluation bounds on the infinite compact and the right level at the finite places
allow the proof to use finitely many of these restrictions. -/
theorem finiteDimensional_span_of_leviRestrictions
    [IsIso (subgroupMultiplication l iV)]
    (hKmax : IsMaximalCompactSubgroup F G K) (hK : IsIwasawaCompact q K)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G))
    (E : Submodule ℂ (K∞ → ℂ)) [FiniteDimensional ℂ E]
    (A : Set (AdelicGroupPoints F G → ℂ))
    (hA : ∀ f ∈ A,
      IsLeftInvariantUnder F G (parabolicUnipotentImage F q iV) f ∧
      (∀ b ∈ L, ∀ g : AdelicGroupPoints F G, f (g * ofFinite F G b) = f g) ∧
      ∀ g : AdelicGroupPoints F G, (fun k : K∞ => f (g * ofInfinite F G k)) ∈ E)
    (hLevi : ∀ (b : FiniteAdelicGroupPoints F G) (k : K∞),
      ∃ W : Submodule ℂ (AdelicGroupPoints F M → ℂ), FiniteDimensional ℂ W ∧
        ∀ f ∈ A, translatedLeviRestriction (q := q) l (ofFinite F G b * ofInfinite F G k) f ∈ W) :
    FiniteDimensional ℂ (Submodule.span ℂ A) := by
  classical
  obtain ⟨D, hD⟩ := exists_finset_detects_zero E
  obtain ⟨B, hB⟩ := exists_finset_mem_leftCoset L (hK.isCompact.image (finite F G).continuous)
  choose W hW hLevi using fun (b : B) (k : D) => hLevi b.val k.val
  let S := Submodule.span ℂ A
  let R (b : B) (k : D) :=
    translatedLeviRestriction (q := q) l (ofFinite F G b * ofInfinite F G k)
  have hR (b : B) (k : D) : S ≤ (W b k).comap (R b k) :=
    Submodule.span_le.mpr (fun f hf => hLevi b k f hf)
  let T : S →ₗ[ℂ] (∀ (b : B) (k : D), W b k) := LinearMap.pi fun b =>
    LinearMap.pi fun k => ((R b k).comp S.subtype).codRestrict (W b k) (fun f => hR b k f.property)
  let (b : B) (k : D) : FiniteDimensional ℂ (W b k) := hW b k
  refine Module.Finite.of_injective T (LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_))
  intro ⟨f, hmem⟩ hf
  have hS : IsLeftInvariantUnder F G (parabolicUnipotentImage F q iV) f ∧
      (∀ b ∈ L, ∀ g : AdelicGroupPoints F G, f (g * ofFinite F G b) = f g) ∧
      ∀ g : AdelicGroupPoints F G, (fun k : K∞ => f (g * ofInfinite F G k)) ∈ E := by
    clear hf
    induction hmem using Submodule.span_induction with
    | mem g hg => exact hA g hg
    | zero => exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => E.zero_mem⟩
    | add g h _ _ hg hh =>
        exact ⟨fun x hx y => congrArg₂ (· + ·) (hg.1 x hx y) (hh.1 x hx y),
          fun b hb y => congrArg₂ (· + ·) (hg.2.1 b hb y) (hh.2.1 b hb y),
          fun y => E.add_mem (hg.2.2 y) (hh.2.2 y)⟩
    | smul c g _ hg =>
        exact ⟨fun x hx y => congrArg (c • ·) (hg.1 x hx y),
          fun b hb y => congrArg (c • ·) (hg.2.1 b hb y), fun y => E.smul_mem c (hg.2.2 y)⟩
  apply Subtype.ext
  funext g
  obtain ⟨v, m, k, rfl⟩ := exists_unipotent_levi_compact iV l hK g
  change f (map F V G (iV ≫ q) v * (map F M G (l ≫ q) m * k.val)) = 0
  rw [hS.1 (map F V G (iV ≫ q) v) ⟨v, rfl⟩]
  obtain ⟨b, hb, hbL⟩ := hB _ ⟨k.val, k.property, rfl⟩
  change b⁻¹ * finite F G k.val ∈ L at hbL
  let a : K∞ := ⟨infinite F G k.val, compact_infinite_mem hKmax k⟩
  let x := map F M G (l ≫ q) m * ofFinite F G b
  have hx : map F M G (l ≫ q) m * k.val =
      (x * ofInfinite F G a) * ofFinite F G (b⁻¹ * finite F G k.val) := by
    have hk : ofFinite F G b * ofInfinite F G a * ofFinite F G (b⁻¹ * finite F G k.val) =
        k.val := by
      rw [(factors_commute F G a b).eq.symm, mul_assoc, ← map_mul, mul_inv_cancel_left,
        ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one, one_mul]
      exact pair_projections F G k.val
    simpa only [x, mul_assoc] using
      (congrArg (map F M G (l ≫ q) m * ·) hk).symm
  rw [hx, hS.2.1 _ hbL (x * ofInfinite F G a)]
  have he := hD (fun j : K∞ => f (x * ofInfinite F G j)) (hS.2.2 x) fun j hj => by
    have hz := congrArg (fun t : ∀ (b : B) (k : D), W b k =>
      (t ⟨b, hb⟩ ⟨j, hj⟩).val m) hf
    change f (map F M G (l ≫ q) m * (ofFinite F G b * ofInfinite F G j)) = 0 at hz
    simpa only [x, mul_assoc] using hz
  exact congrFun he a

end Langlands.Automorphic.GroupSchemeFunctions
