import Langlands.AlgebraicGeometry.GroupoidCoactionCore
import Langlands.AlgebraicGeometry.GroupoidCoactionSubmodule
import Langlands.AlgebraicGeometry.GroupoidCoactionCocycleExtension

/-! # Reducing cocycle vanishing to finite subcoactions -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M : Type v} [AddCommGroup M] [Module B M]
variable (θ : GroupoidCoaction t M)

/-- Finite stable submodules of a fixed coaction. -/
def finiteStableSubmodules : Set (Submodule B M) :=
  {H | Module.Finite B H ∧ θ.IsStableSubmodule H}

/-- The sum of stable submodules is stable. -/
theorem IsStableSubmodule.sup {H K : Submodule B M}
    (hH : θ.IsStableSubmodule H) (hK : θ.IsStableSubmodule K) :
    θ.IsStableSubmodule (H ⊔ K) := by
  intro m
  obtain ⟨h, hh, k, hk, hmk⟩ := Submodule.mem_sup.mp m.property
  obtain ⟨x, hx⟩ := hH ⟨h, hh⟩
  obtain ⟨y, hy⟩ := hK ⟨k, hk⟩
  change LinearMap.lTensor C H.subtype x = θ.coaction h at hx
  change LinearMap.lTensor C K.subtype y = θ.coaction k at hy
  refine ⟨LinearMap.lTensor C (Submodule.inclusion le_sup_left) x +
    LinearMap.lTensor C (Submodule.inclusion le_sup_right) y, ?_⟩
  change LinearMap.lTensor C (H ⊔ K).subtype _ = θ.coaction m
  rw [map_add, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply,
    Submodule.subtype_comp_inclusion, Submodule.subtype_comp_inclusion, hx, hy,
    ← map_add, hmk]

/-- Finite stable submodules are directed by inclusion. -/
theorem finiteStableSubmodules_directed :
    Directed (· ≤ ·)
      (fun H : θ.finiteStableSubmodules => (H.val : Submodule B M)) := by
  intro H K
  let : Module.Finite B H.val := H.property.1
  let : Module.Finite B K.val := K.property.1
  exact ⟨⟨H.val ⊔ K.val, inferInstance, H.property.2.sup θ K.property.2⟩,
    le_sup_left, le_sup_right⟩

/-- Over a Noetherian base, every element lies in a finite stable submodule. -/
theorem finiteStableSubmodules_cover [IsNoetherianRing B]
    (hE : RingEtaleEquivalenceRelation t) (m : M) :
    ∃ H : θ.finiteStableSubmodules, m ∈ H.val := by
  obtain ⟨H, θH, hfin, hm, hi⟩ := exists_finite_subcoaction hE θ m
  exact ⟨⟨H, hfin, (isStableSubmodule_iff_exists_coaction θ H hE).mpr ⟨θH, hi⟩⟩, hm⟩

/-- Vanishing on finite subcoactions implies vanishing on the whole module. -/
theorem oneCohomologyVanishes_of_finite_subcoactions [IsNoetherianRing B]
    (hE : RingEtaleEquivalenceRelation t)
    (hfinite : ∀ (H : Submodule B M) [Module.Finite B H]
      (θH : GroupoidCoaction t H), θH.IsHom θ H.subtype → θH.OneCohomologyVanishes) :
    θ.OneCohomologyVanishes := by
  apply oneCohomologyVanishes_of_directed_submodules θ hE
    (fun H : θ.finiteStableSubmodules => H.val)
    (finiteStableSubmodules_directed θ) (finiteStableSubmodules_cover θ hE)
    (fun H => H.property.2)
  intro H
  let : Module.Finite B H.val := H.property.1
  exact hfinite H.val (submodule θ H.val hE H.property.2)
    (submodule_subtype_isHom θ H.val hE H.property.2)

end Langlands.AlgebraicGeometry.GroupoidCoaction

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C} {M : Type u} [AddCommGroup M] [Module B M]

/-- The published acyclicity predicate reduces to finite subcoactions. -/
theorem isAcyclic_of_finite_subcoactions [IsNoetherianRing B]
    (θ : GroupoidCoaction t M) (hE : RingEtaleEquivalenceRelation t)
    (hfinite : ∀ (H : Submodule B M) [Module.Finite B H]
      (θH : GroupoidCoaction t H), θH.IsHom θ H.subtype → θH.IsAcyclic) :
    θ.IsAcyclic := by
  apply (oneCohomologyVanishes_iff_isAcyclic θ hE).mp
  apply oneCohomologyVanishes_of_finite_subcoactions θ hE
  intro H _ θH hi
  exact oneCohomologyVanishes_of_isAcyclic θH hE (hfinite H θH hi)

end Langlands.AlgebraicGeometry.GroupoidCoaction
