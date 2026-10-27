import Langlands.Representation.Filtration.RepresentationLength
import Langlands.Representation.SubrepresentationLattice
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Subrepresentations from scalar central subrepresentations

Internal algebraic reductions, dual to `Langlands.quotientOfScalarCentralQuotients`
and `Langlands.quotientOfIsotypicRange`: an irreducible quotient becomes an
irreducible subrepresentation. No analytic assertion or existence of an
analytic projector is part of this module.
-/

noncomputable section

namespace Langlands.ScalarSubReduction

universe uR uG uV uW

variable {R : Type uR} [Field R] {G : Type uG} [Group G]
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The inclusion of an invariant subspace. -/
def inclusion (ρ : Representation R G V) (S : Subrepresentation ρ) :
    S.toRepresentation.IntertwiningMap ρ :=
  { toLinearMap := S.toSubmodule.subtype
    isIntertwining' := fun _ => rfl }

theorem inclusion_injective (ρ : Representation R G V) (S : Subrepresentation ρ) :
    Function.Injective (inclusion ρ S) :=
  Submodule.injective_subtype _

/-- The central defect `ρ z - c` of a central element and a scalar. -/
def centralDefect (ρ : Representation R G V)
    (z : Subgroup.center G) (c : R) : ρ.IntertwiningMap ρ :=
  { toLinearMap := ρ z
    isIntertwining' g := by
      change ρ (z : G) * ρ g = ρ g * ρ (z : G)
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.property g] } -
    c • Representation.IntertwiningMap.id ρ

theorem centralDefect_apply (ρ : Representation R G V)
    (z : Subgroup.center G) (c : R) (v : V) :
    centralDefect ρ z c v = ρ z v - c • v := rfl

/-- If a finite-length representation has an irreducible quotient on which `z`
acts by `c`, then the central defect `ρ z - c` is not injective. -/
theorem centralDefect_not_injective
    {ρ : Representation R G V} {σ : Representation R G W}
    (hfin : IsFiniteLength (MonoidAlgebra R G) ρ.asModule)
    (hσ : σ.IsIrreducible) (z : Subgroup.center G) (c : R)
    (hσz : ∀ w, σ z w = c • w)
    (q : ρ.IntertwiningMap σ) (hq : Function.Surjective q) :
    ¬ Function.Injective (centralDefect ρ z c) := by
  let : IsSimpleModule (MonoidAlgebra R G) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  have hnontriv : Nontrivial σ.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra R G) σ.asModule
  let := hnontriv
  let : Nontrivial W := σ.asModuleEquiv.toEquiv.symm.nontrivial
  obtain ⟨_, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfin
  let := hart
  intro hinj
  have hsurj : Function.Surjective (centralDefect ρ z c) :=
    IsArtinian.surjective_of_injective_endomorphism
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (centralDefect ρ z c)) hinj
  have hzero (v : V) : q (centralDefect ρ z c v) = 0 := by
    rw [centralDefect_apply, map_sub, map_smul,
      Representation.IntertwiningMap.isIntertwining _ _ q, hσz, sub_self]
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, hv⟩ := hq w
  obtain ⟨x, hx⟩ := hsurj v
  apply hw
  rw [← hv, ← hx]
  exact hzero x

/-- An idempotent self-intertwiner whose range is the intrinsic `σ`-isotypic
sum and whose kernel has no subquotient isomorphic to `σ` turns an irreducible
quotient `σ` into an injective intertwiner from `σ`. -/
theorem exists_injective_of_isotypicProjector
    {ρ : Representation R G V} {σ : Representation R G W}
    (hσ : σ.IsIrreducible) (P : ρ.IntertwiningMap ρ) (hPP : P.comp P = P)
    (hrange : P.range = ⨆ f : σ.IntertwiningMap ρ, f.range)
    (hker : ∀ K : Subrepresentation P.ker.toRepresentation,
      ¬ ∃ q : K.toRepresentation.IntertwiningMap σ, Function.Surjective q)
    (q : ρ.IntertwiningMap σ) (hq : Function.Surjective q) :
    ∃ f : σ.IntertwiningMap ρ, Function.Injective f := by
  let := hσ
  let : IsSimpleModule (MonoidAlgebra R G) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  have hnontriv : Nontrivial σ.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra R G) σ.asModule
  let := hnontriv
  let : Nontrivial W := σ.asModuleEquiv.toEquiv.symm.nontrivial
  let qK := q.comp (inclusion ρ P.ker)
  have hqK : qK = 0 := by
    rcases Representation.IsIrreducible.surjective_or_eq_zero qK with hs | hz
    · exfalso
      apply hker ⊤
      refine ⟨qK.comp (inclusion _ ⊤), fun w => ?_⟩
      obtain ⟨v, hv⟩ := hs w
      exact ⟨⟨v, trivial⟩, hv⟩
    · exact hz
  have hqP (v : V) : q v = q (P v) := by
    have hmem : v - P v ∈ P.ker := by
      change P (v - P v) = 0
      rw [map_sub]
      have h := congrArg (fun h : ρ.IntertwiningMap ρ => h v) hPP
      change P (P v) = P v at h
      rw [h, sub_self]
    have h0 : q (v - P v) = 0 :=
      congrArg (fun h : P.ker.toRepresentation.IntertwiningMap σ => h ⟨v - P v, hmem⟩) hqK
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  have hmap : ∃ f : σ.IntertwiningMap ρ, f ≠ 0 := by
    by_contra h
    push Not at h
    have hr : P.range = ⊥ := by
      rw [hrange]
      apply eq_bot_iff.mpr
      apply iSup_le_iff.mpr
      intro f
      rw [h f]
      intro v hv
      obtain ⟨w, hw⟩ := hv
      exact hw.symm
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨v, hv⟩ := hq w
    apply hw
    have hPv : P v = 0 := hr.le ⟨v, rfl⟩
    rw [← hv, hqP v, hPv, map_zero]
  obtain ⟨f, hf⟩ := hmap
  exact ⟨f, (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf⟩

private theorem sub_exists
    (ρ : Representation R G V) (σ : Representation R G W)
    (χ : Subgroup.center G → R)
    (hfin : IsFiniteLength (MonoidAlgebra R G) ρ.asModule)
    (hσ : σ.IsIrreducible) (hχ : ∀ (z : Subgroup.center G) w, σ z w = χ z • w)
    (hscalar : ∀ {U : Type uV} [AddCommGroup U] [Module R U]
      (τ : Representation R G U) (i : τ.IntertwiningMap ρ),
      Function.Injective i →
      (∀ (z : Subgroup.center G) u, τ z u = χ z • u) →
      (∃ q : τ.IntertwiningMap σ, Function.Surjective q) →
      ∃ f : σ.IntertwiningMap τ, Function.Injective f)
    (hq : ∃ q : ρ.IntertwiningMap σ, Function.Surjective q) :
    ∃ f : σ.IntertwiningMap ρ, Function.Injective f := by
  classical
  have key : ∀ n : ℕ, ∀ {U : Type uV} [AddCommGroup U] [Module R U]
      (τ : Representation R G U) (i : τ.IntertwiningMap ρ),
      Function.Injective i → (repLength τ).toNat = n →
      (∃ q : τ.IntertwiningMap σ, Function.Surjective q) →
      ∃ f : σ.IntertwiningMap τ, Function.Injective f := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U _ _ τ i hi hn hqτ
      by_cases hτχ : ∀ (z : Subgroup.center G) u, τ z u = χ z • u
      · exact hscalar τ i hi hτχ hqτ
      · push Not at hτχ
        obtain ⟨z, v, hv⟩ := hτχ
        obtain ⟨q, hqs⟩ := hqτ
        let D := centralDefect τ z (χ z)
        let K := D.ker
        let A := D.range
        let iK := inclusion τ K
        let iA := inclusion τ A
        let pA : τ.IntertwiningMap A.toRepresentation :=
          { toLinearMap := D.toLinearMap.rangeRestrict
            isIntertwining' g := by
              ext u
              change D (τ g u) = τ g (D u)
              exact Representation.IntertwiningMap.isIntertwining _ _ D g u }
        have hpA : Function.Surjective pA := by
          rintro ⟨u, x, hx⟩
          exact ⟨x, Subtype.ext hx⟩
        have hfinτ : IsFiniteLength (MonoidAlgebra R G) τ.asModule :=
          hfin.of_injective
            (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ i) hi
        have hfinK : IsFiniteLength (MonoidAlgebra R G) K.toRepresentation.asModule :=
          hfinτ.of_injective
            (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ iK)
            (inclusion_injective τ K)
        have hfinA : IsFiniteLength (MonoidAlgebra R G) A.toRepresentation.asModule :=
          hfinτ.of_surjective
            (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ pA) hpA
        have hKfin : repLength K.toRepresentation ≠ ⊤ :=
          Module.length_ne_top_iff.mpr hfinK
        have hAfin : repLength A.toRepresentation ≠ ⊤ :=
          Module.length_ne_top_iff.mpr hfinA
        have hD : ¬ Function.Injective D :=
          centralDefect_not_injective hfinτ hσ z (χ z) (hχ z) q hqs
        have hKne : repLength K.toRepresentation ≠ 0 := by
          intro hzero
          let := repLength_eq_zero_iff.mp hzero
          apply hD
          intro x y hxy
          have hmem : x - y ∈ K := by
            change D (x - y) = 0
            rw [map_sub, hxy, sub_self]
          have h0 : (⟨x - y, hmem⟩ : K.toSubmodule) = 0 := Subsingleton.elim _ _
          exact sub_eq_zero.mp (congrArg Subtype.val h0)
        have hAne : repLength A.toRepresentation ≠ 0 := by
          intro hzero
          let := repLength_eq_zero_iff.mp hzero
          have hz : (⟨D v, ⟨v, rfl⟩⟩ : A.toSubmodule) = 0 := Subsingleton.elim _ _
          have hz' : D v = 0 := congrArg Subtype.val hz
          apply hv
          exact sub_eq_zero.mp hz'
        have hlen : repLength τ = repLength K.toRepresentation + repLength A.toRepresentation := by
          refine repLength_eq_add_of_exact iK pA (inclusion_injective τ K) hpA ?_
          ext x
          constructor
          · rintro ⟨y, rfl⟩
            exact Subtype.ext y.property
          · intro hx
            have hx' : D x = 0 := congrArg Subtype.val hx
            exact ⟨⟨x, hx'⟩, rfl⟩
        have hKnpos := ENat.toNat_pos hKne hKfin
        have hAnpos := ENat.toNat_pos hAne hAfin
        have hadd : n = (repLength K.toRepresentation).toNat +
            (repLength A.toRepresentation).toNat := by
          rw [← hn, hlen]
          exact ENat.toNat_add hKfin hAfin
        let := hσ
        rcases Representation.IsIrreducible.surjective_or_eq_zero (q.comp iK) with hs | hz
        · obtain ⟨f, hf⟩ := ih (repLength K.toRepresentation).toNat (by omega)
            K.toRepresentation (i.comp iK) (hi.comp (inclusion_injective τ K)) rfl
            ⟨q.comp iK, hs⟩
          exact ⟨iK.comp f, (inclusion_injective τ K).comp hf⟩
        · have hK : LinearMap.ker pA.toLinearMap ≤ LinearMap.ker q.toLinearMap := by
            intro x hx
            have hx' : D x = 0 := congrArg Subtype.val hx
            exact congrArg
              (fun r : K.toRepresentation.IntertwiningMap σ => r ⟨x, hx'⟩) hz
          let e := pA.toLinearMap.quotKerEquivOfSurjective hpA
          let qA : A.toRepresentation.IntertwiningMap σ :=
            { toLinearMap :=
                ((LinearMap.ker pA.toLinearMap).liftQ q.toLinearMap hK).comp
                  e.symm.toLinearMap
              isIntertwining' g := by
                ext a
                obtain ⟨x, rfl⟩ := hpA a
                have hpg : pA (τ g x) = A.toRepresentation g (pA x) :=
                  Representation.IntertwiningMap.isIntertwining _ _ pA g x
                change (LinearMap.ker pA.toLinearMap).liftQ q.toLinearMap hK
                    (e.symm (A.toRepresentation g (pA x))) =
                  σ g ((LinearMap.ker pA.toLinearMap).liftQ q.toLinearMap hK
                    (e.symm (pA x)))
                rw [← hpg]
                have he (y : U) : e.symm (pA y) =
                    (LinearMap.ker pA.toLinearMap).mkQ y := by
                  apply e.injective
                  rw [LinearEquiv.apply_symm_apply]
                  rfl
                rw [he, he]
                change q (τ g x) = σ g (q x)
                exact Representation.IntertwiningMap.isIntertwining _ _ q g x }
          have hqA : Function.Surjective qA := by
            intro w
            obtain ⟨x, hx⟩ := hqs w
            refine ⟨pA x, ?_⟩
            change (LinearMap.ker pA.toLinearMap).liftQ q.toLinearMap hK
              (e.symm (pA x)) = w
            have he : e.symm (pA x) = (LinearMap.ker pA.toLinearMap).mkQ x := by
              apply e.injective
              rw [LinearEquiv.apply_symm_apply]
              rfl
            rw [he]
            exact hx
          obtain ⟨f, hf⟩ := ih (repLength A.toRepresentation).toNat (by omega)
            A.toRepresentation (i.comp iA) (hi.comp (inclusion_injective τ A)) rfl
            ⟨qA, hqA⟩
          exact ⟨iA.comp f, (inclusion_injective τ A).comp hf⟩
  exact key (repLength ρ).toNat ρ (Representation.IntertwiningMap.id ρ)
    Function.injective_id rfl hq

end Langlands.ScalarSubReduction

namespace Langlands

universe uR uG uV uW

/-- Reduce extraction of an irreducible subrepresentation from an irreducible
quotient to subrepresentations on which the full center acts by the prescribed
scalar function, using finite composition length. -/
theorem exists_injective_of_scalarCentralSubs
    {R : Type uR} [Field R] {G : Type uG} [Group G]
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (ρ : Representation R G V) (σ : Representation R G W)
    (χ : Subgroup.center G → R)
    (hfin : IsFiniteLength (MonoidAlgebra R G) ρ.asModule)
    (hσ : σ.IsIrreducible) (hχ : ∀ (z : Subgroup.center G) w, σ z w = χ z • w)
    (hscalar : ∀ {U : Type uV} [AddCommGroup U] [Module R U]
      (τ : Representation R G U) (i : τ.IntertwiningMap ρ),
      Function.Injective i →
      (∀ (z : Subgroup.center G) u, τ z u = χ z • u) →
      (∃ q : τ.IntertwiningMap σ, Function.Surjective q) →
      ∃ f : σ.IntertwiningMap τ, Function.Injective f)
    (hq : ∃ q : ρ.IntertwiningMap σ, Function.Surjective q) :
    ∃ f : σ.IntertwiningMap ρ, Function.Injective f :=
  ScalarSubReduction.sub_exists ρ σ χ hfin hσ hχ hscalar hq

end Langlands
