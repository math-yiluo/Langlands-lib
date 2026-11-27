import Langlands.GroupScheme.Rational.NumberFieldQuadraticOppositeBorelTorus
import Langlands.GroupScheme.Descent.GaloisClosedSubgroups
import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.BaseChange

/-! # Descent of the intersection of quadratic conjugate Borels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {F Q : Type u} [Field F] [Field Q] [Algebra F Q]
  [FiniteDimensional F Q] [IsGalois F Q]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local notation "b" => algebraBaseMap F Q
local notation "GQ" => Functor.obj (GroupScheme.baseChange b) G

omit [FiniteDimensional F Q] [IsGalois F Q] [IsAffineHom G.X.hom] in
private theorem transport_inf (σ : Q ≃ₐ[F] Q) (A B : SubgroupFunctor GQ) :
    SubgroupFunctor.galoisTransport F Q G σ (A ⊓ B) =
      SubgroupFunctor.galoisTransport F Q G σ A ⊓
        SubgroupFunctor.galoisTransport F Q G σ B := by
  apply SubgroupFunctor.ext
  intro Z
  apply Subgroup.ext
  intro z
  change z ∈ (SubgroupFunctor.descentTransport _ _ _ _ (A ⊓ B)).carrier Z ↔
    z ∈ (SubgroupFunctor.descentTransport _ _ _ _ A ⊓
      SubgroupFunctor.descentTransport _ _ _ _ B).carrier Z
  rw [SubgroupFunctor.mem_descentTransport_iff_descentPoint, SubgroupFunctor.inf_carrier,
    Subgroup.mem_inf, SubgroupFunctor.inf_carrier, Subgroup.mem_inf,
    SubgroupFunctor.mem_descentTransport_iff_descentPoint,
    SubgroupFunctor.mem_descentTransport_iff_descentPoint]

/-- A maximal torus given by the full intersection of quadratic conjugate
Borels descends to a maximal torus of the original group. -/
theorem exists_quadraticOppositeBorelTorus_of_intersection
    (hdeg : Module.finrank F Q = 2) (σ : Q ≃ₐ[F] Q) (hσ : σ ≠ 1)
    {B : GroupScheme (Spec (CommRingCat.of Q))} (j : B ⟶ GQ)
    (TQ : CommGroupScheme (Spec (CommRingCat.of Q))) (tQ : TQ.toGrp ⟶ GQ)
    (htQ : IsMaximalTorus tQ)
    (hinter : SubgroupFunctor.range j ⊓ SubgroupFunctor.range (radicalGaloisHom j σ) =
      SubgroupFunctor.range tQ) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (t : T.toGrp ⟶ G),
      IsMaximalTorus t ∧
      SubgroupFunctor.range j ⊓ SubgroupFunctor.range (radicalGaloisHom j σ) =
        SubgroupFunctor.range ((GroupScheme.baseChange b).map t) := by
  classical
  let ρ := SubgroupFunctor.galoisTransport F Q G
  have hcard : Nat.card (Q ≃ₐ[F] Q) = 2 := (IsGalois.card_aut_eq_finrank F Q).trans hdeg
  have hσ₂ : σ ^ 2 = 1 := by simpa only [hcard] using (pow_card_eq_one' (x := σ))
  obtain ⟨_, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : Q ≃ₐ[F] Q)).mp hcard
  have htransport {H : GroupScheme (Spec (CommRingCat.of Q))} (i : H ⟶ GQ)
      (τ : Q ≃ₐ[F] Q) : ρ τ (SubgroupFunctor.range i) =
        SubgroupFunctor.range (radicalGaloisHom i τ) :=
    SubgroupFunctor.descentTransport_range _ _ _ _ i
  have hinv (τ : Q ≃ₐ[F] Q) :
      SubgroupFunctor.range (radicalGaloisHom tQ τ) = SubgroupFunctor.range tQ := by
    rw [← htransport, ← hinter]
    by_cases ht : τ = 1
    · subst τ
      exact congrFun (map_one ρ) _
    have ht' : τ = σ := (huniq τ ht).trans (huniq σ hσ).symm
    subst τ
    simp only [← htransport]
    change ρ σ (_ ⊓ _) = _
    rw [show ρ σ (_ ⊓ _) = _ from transport_inf σ _ _]
    have htwice (D : SubgroupFunctor GQ) : ρ σ (ρ σ D) = D := by
      change (ρ σ * ρ σ) D = D
      rw [← map_mul, ← pow_two, hσ₂, map_one]
      rfl
    rw [htwice]
    apply SubgroupFunctor.ext
    intro Z
    simp only [SubgroupFunctor.inf_carrier]
    exact inf_comm _ _
  obtain ⟨P, t, e, _, ht, he⟩ := htQ.2.1.exists_descent_of_galois_range_eq hinv
  have hP : IsTorus P := IsTorus.of_baseChange (htQ.1.of_iso e)
  let T : CommGroupScheme (Spec (CommRingCat.of F)) :=
    { toGrp := P, comm := hP.isCommMonObj }
  have hmaxQ : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map t) := by
    rw [he]
    exact htQ.iso_comp (T' := (CommGroupScheme.baseChange b).obj T) e
  have hmax : IsMaximalTorus (T := T) t := by
    refine ⟨hP, ht, fun W w f hW hw hf => ?_⟩
    obtain ⟨hs, hf', hq⟩ := fieldExtension_fpqc F Q
    let : Surjective b := hs
    let : Flat b := hf'
    let : QuasiCompact b := hq
    let C := GroupScheme.baseChange b
    let : IsIso (C.map f) := hmaxQ.2.2 ((CommGroupScheme.baseChange b).obj W)
      (C.map w) (C.map f) hW.baseChange (hw.baseChange b) (by rw [← C.map_comp, hf])
    exact isIso_of_baseChange b f
  refine ⟨T, t, hmax, hinter.trans ?_⟩
  rw [he, SubgroupFunctor.range_iso_comp]

end Langlands.GroupScheme
