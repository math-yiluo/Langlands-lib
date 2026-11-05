import Langlands.Global.FinitePlaceGroupBaseChange
import Langlands.Global.CoordinateCompactPatching

/-! # Transport of local Iwasawa compact data to actual finite-place points -/

noncomputable section

universe u v w x

open scoped Pointwise

namespace Langlands.Global.CoordinateCompactPatching

variable {H : Type u} {H' : Type v} [Group H] [Group H']
  [TopologicalSpace H] [TopologicalSpace H']
  {Q : Type w} {Q' : Type x} [Group Q] [Group Q']

/-- A commuting point-map square transports compactness, unrestricted compact
maximality, and source-left covering through a continuous group equivalence. -/
theorem IsLocalIwasawaCompact.map
    {φ : Q →* H} {φ' : Q' →* H'} {K : Subgroup H}
    (hK : IsLocalIwasawaCompact φ K)
    (e : H ≃ₜ* H') (d : Q → Q')
    (hcomm : ∀ q, e (φ q) = φ' (d q)) :
    IsLocalIwasawaCompact φ' (K.map e.toMonoidHom) := by
  rcases hK with ⟨⟨hc, hm⟩, hp⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Subgroup.coe_map]
    exact hc.image e.continuous
  · intro L hL hKL
    have hLc : IsCompact ((L.comap e.toMonoidHom : Subgroup H) : Set H) :=
      e.toHomeomorph.isCompact_preimage.mpr hL
    have hKpre : K ≤ L.comap e.toMonoidHom := by
      intro k hk
      exact hKL ⟨k, hk, rfl⟩
    have hLeq := hm (L.comap e.toMonoidHom) hLc hKpre
    apply le_antisymm ?_ hKL
    intro l hl
    have hpre : e.symm l ∈ K := by
      rw [← hLeq]
      change e (e.symm l) ∈ L
      rwa [e.apply_symm_apply]
    exact ⟨e.symm l, hpre, e.apply_symm_apply l⟩
  · apply Set.eq_univ_of_forall
    intro g
    have hg : e.symm g ∈ Set.range φ * (K : Set H) := by
      rw [hp]
      exact Set.mem_univ _
    rcases hg with ⟨_, ⟨q, rfl⟩, k, hk, hqk⟩
    change φ q * k = e.symm g at hqk
    refine ⟨φ' (d q), ⟨d q, rfl⟩, e k, ⟨k, hk, rfl⟩, ?_⟩
    change φ' (d q) * e k = g
    rw [← hcomm q, ← map_mul, hqk, e.apply_symm_apply]

end Langlands.Global.CoordinateCompactPatching

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.FinitePlaceGroupPoints

open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

local instance compactSource_isAffine (v : FinitePlace F) :
    IsAffine (baseChangedGroup F G v).X.left := by
  change IsAffine (pullback G.X.hom (Spec.algebraMap F (FiniteCompletion F v)))
  infer_instance

local instance compactSource_topology (v : FinitePlace F) :
    TopologicalSpace (rationalPoints (baseChangedGroup F G v)) :=
  rationalPointTopology (FiniteCompletion F v) (baseChangedGroup F G v).X

/-- Transport a supplied local Iwasawa compact subgroup on rational points of
the actual base change to the original finite-completion point carrier. -/
def baseChangeIwasawaCompact
    {P : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G) (v : FinitePlace F) :
    {K : Subgroup (rationalPoints (baseChangedGroup F G v)) //
      CoordinateCompactPatching.IsLocalIwasawaCompact
        (rationalPoints.map
          ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v))).map p)) K} →
    {K : Subgroup (FinitePlaceGroupPoints F G v) //
      CoordinateCompactPatching.IsLocalIwasawaCompact
        (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))) K} :=
  fun K => ⟨K.1.map (baseChangeContinuousMulEquiv F G v).toMonoidHom,
    K.2.map (baseChangeContinuousMulEquiv F G v) (baseChangeMulEquiv F P v)
      (baseChangeMulEquiv_map F G p v)⟩

end Langlands.Global.FinitePlaceGroupPoints
