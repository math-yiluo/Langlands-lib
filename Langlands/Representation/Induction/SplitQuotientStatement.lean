import Langlands.Representation.Induction.Definitions
import Mathlib.Basic.Complex.Basic

/-!
# Compact induction across a continuous split quotient

Compact induction from a closed subgroup `H ≤ G` containing the kernel of a continuous
retraction `r : G →* L`, restricted along a continuous section `s`, compared with compact
induction from `H.comap s ≤ L`.
-/

open CategoryTheory

namespace Langlands.Induction

universe uR uG uK uH uV uW

section Restriction

variable {R : Type uR} [CommRing R] {K : Type uK} {H : Type uH} [Group K] [Group H]
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The same linear map as an intertwiner between the restrictions along `i`. -/
def restrictAlongMap (i : K →* H) {ρ : Representation R H V} {σ : Representation R H W}
    (T : ρ.IntertwiningMap σ) : Representation.IntertwiningMap (ρ.comp i) (σ.comp i) where
  toLinearMap := T.toLinearMap
  isIntertwining' k := T.isIntertwining' (i k)

end Restriction

/-- For a continuous retraction `r : G →* L` with continuous section `s` and a closed
subgroup `H ⊇ ker r`, restriction along `s` of compact induction from `H` is, naturally in
coefficients on which `H ∩ ker r` acts trivially, compact induction from `H.comap s` of the
coefficients restricted along `s.subgroupComap H`, by `f ↦ f ∘ s` with inverse `k ↦ k ∘ r`. -/
def CompactInductionSplitQuotient : Prop :=
  ∀ (G L : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (r : G →* L) (s : L →* G), Continuous r → Continuous s → (∀ l : L, r (s l) = l) →
    ∀ H : Subgroup G, IsClosed (H : Set G) → r.ker ≤ H →
      ∃ e : ∀ A : Langlands.SmoothRep.{0, uG, uV} ℂ H,
          (∀ h : H, r (h : G) = 1 → ∀ v : A, A.representation h v = v) →
          Representation.Equiv ((compactInduced H A.representation).comp s)
            (compactInduced (H.comap s) (A.representation.comp (s.subgroupComap H))),
        (∀ (A : Langlands.SmoothRep.{0, uG, uV} ℂ H)
            (hA : ∀ h : H, r (h : G) = 1 → ∀ v : A, A.representation h v = v)
            (f : CompactFunctions H A.representation) (l : L),
          eval (H.comap s) (A.representation.comp (s.subgroupComap H)) (e A hA f).val l =
            eval H A.representation f.val (s l)) ∧
        (∀ (A : Langlands.SmoothRep.{0, uG, uV} ℂ H)
            (hA : ∀ h : H, r (h : G) = 1 → ∀ v : A, A.representation h v = v)
            (k : CompactFunctions (H.comap s) (A.representation.comp (s.subgroupComap H)))
            (g : G),
          eval H A.representation ((e A hA).symm k).val g =
            eval (H.comap s) (A.representation.comp (s.subgroupComap H)) k.val (r g)) ∧
        (∀ (A B : Langlands.SmoothRep.{0, uG, uV} ℂ H)
            (hA : ∀ h : H, r (h : G) = 1 → ∀ v : A, A.representation h v = v)
            (hB : ∀ h : H, r (h : G) = 1 → ∀ v : B, B.representation h v = v)
            (T : A ⟶ B) (f : CompactFunctions H A.representation),
          e B hB (compactInducedMap H (Langlands.SmoothRep.hom T) f) =
            compactInducedMap (H.comap s)
              (restrictAlongMap (s.subgroupComap H) (Langlands.SmoothRep.hom T)) (e A hA f))

end Langlands.Induction
