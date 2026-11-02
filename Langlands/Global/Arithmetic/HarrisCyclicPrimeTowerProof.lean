import Langlands.LocalFactor.Ramification.InertiaSolvabilityProof
import Langlands.FieldTheory.SolvableGaloisTowerProof
import Langlands.Global.Arithmetic.HarrisCyclicPrimeTowerStatement
import Mathlib.Data.Fin.Rev

noncomputable section

namespace Langlands.Global.GeneralPosition

universe u v

private def primeFieldAutHom (p : ℕ) [Fact p.Prime] (R : Type u)
    [Field R] [Algebra (ZMod p) R] : RingAut R →* (R ≃ₐ[ZMod p] R) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ) fun x =>
    RingHom.congr_fun (RingHom.ext_zmod
      (σ.toRingHom.comp (algebraMap (ZMod p) R)) (algebraMap (ZMod p) R)) x
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

private theorem primeFieldAutHom_injective (p : ℕ) [Fact p.Prime] (R : Type u)
    [Field R] [Algebra (ZMod p) R] :
    Function.Injective (primeFieldAutHom p R) := by
  intro σ τ h
  exact RingEquiv.ext fun x => DFunLike.congr_fun h x

private theorem ringAut_isSolvable (p : ℕ) [Fact p.Prime] (R : Type u)
    [Field R] [Algebra (ZMod p) R] [Finite R] : Group.IsSolvable (RingAut R) :=
  Group.isSolvable_of_isSolvable_injective (primeFieldAutHom_injective p R)

private theorem localAut_isSolvable {p : ℕ} [Fact p.Prime] {L : PadicField.{u} p}
    (T : L.TopologicalData) (K : Type v) [Field K] [Algebra (Padic p) K]
    [Algebra K L.Carrier] [IsScalarTower (Padic p) K L.Carrier] :
    Group.IsSolvable (L.Carrier ≃ₐ[K] L.Carrier) := by
  let := T.residueAlgebra
  let := T.finite_residueField
  let := ringAut_isSolvable p T.ResidueField
  let := Ramification.Padic.isSolvable_inertia T K
  exact Group.isSolvable_of_ker_le_range
    (Ramification.Padic.inertia T K).subtype (Ramification.Padic.residueHom T K)
    (by rw [Subgroup.range_subtype]; exact le_rfl)

open LocalFactor.CommonClosure

private def liftExtension {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (E : Extension F) (A : IntermediateField F.Carrier E.field) : Extension F :=
  ⟨(IntermediateField.lift A), FiniteDimensional.of_injective
    (IntermediateField.liftAlgEquiv A).symm.toLinearMap
    (IntermediateField.liftAlgEquiv A).symm.injective⟩

private theorem lift_prime_step {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (E : Extension F) (A B : IntermediateField F.Carrier E.field)
    (h : A ≤ B)
    (hstep :
      letI alg : Algebra A B := (IntermediateField.inclusion h).toAlgebra
      letI : Module A B := @Algebra.toModule _ _ _ _ alg
      FiniteDimensional A B ∧ IsGalois A B ∧ IsCyclic (B ≃ₐ[A] B) ∧
        Nat.Prime (Module.finrank A B)) :
    IsCyclicPrimeStep F (liftExtension F E A) (liftExtension F E B) := by
  let alg : Algebra A B := (IntermediateField.inclusion h).toAlgebra
  let : Module A B := @Algebra.toModule _ _ _ _ alg
  obtain ⟨hfd, hGal, _, hprime⟩ := hstep
  let := hfd
  let := hGal
  let hLift : (IntermediateField.lift A) ≤ (IntermediateField.lift B) := IntermediateField.map_mono E.field.val h
  let eA : A ≃+* (IntermediateField.lift A) := (IntermediateField.liftAlgEquiv A).toRingEquiv
  let eB : B ≃+* IntermediateField.extendScalars hLift :=
    (IntermediateField.liftAlgEquiv B).toRingEquiv
  have hcomp : (algebraMap (IntermediateField.lift A) (IntermediateField.extendScalars hLift)).comp eA.toRingHom =
      eB.toRingHom.comp (algebraMap A B) := by
    ext x
    rfl
  let : IsGalois (IntermediateField.lift A) (IntermediateField.extendScalars hLift) :=
    IsGalois.of_equiv_equiv (f := eA) (g := eB) hcomp
  have hprime' : Nat.Prime (Module.finrank (IntermediateField.lift A) (IntermediateField.extendScalars hLift)) := by
    rw [← Algebra.finrank_eq_of_equiv_equiv eA eB hcomp]
    exact hprime
  let : FiniteDimensional (IntermediateField.lift A) (IntermediateField.extendScalars hLift) :=
    Module.finite_of_finrank_pos hprime'.pos
  let := Fact.mk hprime'
  exact ⟨hLift, (inferInstance : IsGalois (IntermediateField.lift A)
    (IntermediateField.extendScalars hLift)), isCyclic_of_prime_card
    (IsGalois.card_aut_eq_finrank (IntermediateField.lift A) (IntermediateField.extendScalars hLift)), hprime'⟩

private theorem localCyclicPrimeTower {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (E : Extension F) [IsGalois F.Carrier E.field] :
    ∃ (n : ℕ) (T : Fin (n + 1) → Extension F),
      (T 0).field = E.field ∧ (T (Fin.last n)).field = ⊥ ∧
        ∀ i : Fin n, IsCyclicPrimeStep F (T i.succ) (T i.castSucc) := by
  let alg : Algebra (Padic p) E.field :=
    ((algebraMap F.Carrier E.field).comp (algebraMap (Padic p) F.Carrier)).toAlgebra
  let : Module (Padic p) E.field := @Algebra.toModule _ _ _ _ alg
  let : IsScalarTower (Padic p) F.Carrier E.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Group.IsSolvable (E.field ≃ₐ[F.Carrier] E.field) :=
    localAut_isSolvable (L := E.asPadicField (p := p))
      (E.asPadicField (p := p)).canonicalTopologicalData F.Carrier
  obtain ⟨n, T, h0, htop, hsteps⟩ :=
    Langlands.FieldTheory.solvableGaloisPrimeTower F.Carrier E.field
  refine ⟨n, fun i => liftExtension F E (T i.rev), ?_, ?_, ?_⟩
  · change IntermediateField.lift (T (Fin.rev 0)) = E.field
    rw [Fin.rev_zero, htop]
    apply le_antisymm (IntermediateField.lift_le _)
    intro x hx
    exact ⟨⟨x, hx⟩, IntermediateField.mem_top, rfl⟩
  · change IntermediateField.lift (T (Fin.rev (Fin.last n))) = ⊥
    rw [Fin.rev_last, h0]
    exact IntermediateField.map_bot E.field.val
  · intro i
    obtain ⟨h, hs⟩ := hsteps i.rev
    simpa only [Fin.rev_succ, Fin.rev_castSucc] using
      lift_prime_step F E (T i.rev.castSucc) (T i.rev.succ) h hs

end Langlands.Global.GeneralPosition

namespace Langlands.Global

universe u

/-- The cyclic prime-step tower for an actual finite Galois p-adic extension
in the common algebraic closure. -/
theorem harrisCyclicPrimeTower : HarrisCyclicPrimeTowerStatement.{u} := by
  intro p hp F E hGal
  exact GeneralPosition.localCyclicPrimeTower F E

end Langlands.Global
