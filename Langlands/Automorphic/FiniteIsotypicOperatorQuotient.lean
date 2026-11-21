import Langlands.Automorphic.AlgebraOperatorSubquotient
import Mathlib.RingTheory.SimpleModule.Isotypic

/-! # A simple operator subquotient preserving a prescribed finite representation -/

noncomputable section

universe uV

open scoped MonoidAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Automorphic

section Restriction

variable {R V G : Type*} [Ring R] [Algebra ℂ R] [AddCommGroup V]
  [Module ℂ V] [Module R V] [IsScalarTower ℂ R V] [Monoid G]
  (op : G → R) (ρ : Representation ℂ G V) (hρ : ∀ g v, op g • v = ρ g v)
  (P : Submodule R V)

private def submoduleRepresentation : Representation ℂ G P where
  toFun g := Algebra.lsmul ℂ ℂ P (op g)
  map_one' := LinearMap.ext fun x => Subtype.ext (by
    change op 1 • x.val = x.val
    rw [hρ, map_one, Module.End.one_apply])
  map_mul' g h := LinearMap.ext fun x => Subtype.ext (by
    change op (g * h) • x.val = op g • (op h • x.val)
    simp only [hρ, map_mul, Module.End.mul_apply])

private def submoduleIntertwiner : (submoduleRepresentation op ρ hρ P).IntertwiningMap ρ :=
  ⟨P.subtype.restrictScalars ℂ, fun g => LinearMap.ext fun x => hρ g x.val⟩

private def quotientRepresentation (Q : Submodule R P) : Representation ℂ G (P ⧸ Q) where
  toFun g := Algebra.lsmul ℂ ℂ (P ⧸ Q) (op g)
  map_one' := LinearMap.ext fun y => by
    obtain ⟨x, rfl⟩ := Q.mkQ_surjective y
    change op 1 • Q.mkQ x = Q.mkQ x
    rw [← map_smul]
    congr 1
    exact LinearMap.congr_fun (map_one (submoduleRepresentation op ρ hρ P)) x
  map_mul' g h := LinearMap.ext fun y => by
    obtain ⟨x, rfl⟩ := Q.mkQ_surjective y
    change op (g * h) • Q.mkQ x = op g • (op h • Q.mkQ x)
    simp only [← map_smul]
    congr 1
    exact LinearMap.congr_fun (map_mul (submoduleRepresentation op ρ hρ P) g h) x

private def quotientIntertwiner (Q : Submodule R P) :
    (submoduleRepresentation op ρ hρ P).IntertwiningMap (quotientRepresentation op ρ hρ P Q) :=
  ⟨Q.mkQ.restrictScalars ℂ, fun g => LinearMap.ext fun x => Q.mkQ.map_smul (op g) x⟩

end Restriction

section Isotypic

variable {G X V W : Type*} [Monoid G]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ξ : Representation ℂ G X) [ξ.IsIrreducible]
  {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}

set_option maxHeartbeats 1200000 in
private theorem exists_embedding_of_isotypic_subquotient
    (hρ : isotypicComponent ℂ[G] ρ.asModule ξ.asModule = ⊤)
    {D : Type*} [AddCommGroup D] [Module ℂ D] (ρD : Representation ℂ G D)
    (i : ρD.IntertwiningMap ρ) (hi : Function.Injective i)
    (q : ρD.IntertwiningMap ρ') (hq : Function.Surjective q) [Nontrivial W] :
    ∃ e : ξ.IntertwiningMap ρ', Function.Injective e := by
  let A := ℂ[G]
  let ι := Representation.IntertwiningMap.equivLinearMapAsModule _ _ i
  let p := Representation.IntertwiningMap.equivLinearMapAsModule _ _ q
  let : IsSimpleModule A ξ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ξ).mp inferInstance
  let : IsSemisimpleModule A ρ.asModule := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    apply top_unique
    change (⊤ : Submodule ℂ[G] ρ.asModule) ≤
      sSup {L : Submodule ℂ[G] ρ.asModule | IsSimpleModule ℂ[G] L}
    rw [← hρ]
    refine sSup_le ?_
    intro L hL
    obtain ⟨e⟩ : Nonempty (L ≃ₗ[A] ξ.asModule) := hL
    exact le_sSup (s := {D : Submodule A ρ.asModule | IsSimpleModule A D})
      (IsSimpleModule.congr e)
  let : IsSemisimpleModule A ρD.asModule := IsSemisimpleModule.of_injective ι hi
  let : IsSemisimpleModule A ρ'.asModule := IsSemisimpleModule.of_surjective p hq
  have hiso := (IsIsotypicOfType.of_isotypicComponent_eq_top hρ).of_injective ι hi
  have hD : isotypicComponent A ρD.asModule ξ.asModule = ⊤ :=
    isotypicComponent_eq_top_iff.mpr hiso
  have hp : ⊤ ≤ (isotypicComponent A ρ'.asModule ξ.asModule).comap p :=
    hD ▸ p.le_comap_isotypicComponent ξ.asModule
  have h' : isotypicComponent A ρ'.asModule ξ.asModule = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := (show Function.Surjective p from hq) x
    exact hp (Submodule.mem_top (x := y))
  let T : Submodule A ρ'.asModule := ⊤
  let : IsSemisimpleModule A T := IsSemisimpleModule.of_injective T.subtype T.subtype_injective
  let : Nontrivial ρ'.asModule := ‹Nontrivial W›
  have hne : T ≠ ⊥ := top_ne_bot
  obtain ⟨L, -, hL⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le T).resolve_left hne
  let := hL
  obtain ⟨e⟩ := IsIsotypicOfType.of_isotypicComponent_eq_top h' L
  refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm
    (L.subtype.comp e.symm.toLinearMap), ?_⟩
  change Function.Injective (L.subtype.comp e.symm.toLinearMap)
  exact L.subtype_injective.comp e.symm.injective

end Isotypic

section SimpleQuotient

variable {R G K X : Type*} [Ring R] [Algebra ℂ R] [Monoid G] [Monoid K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
  (a : R →ₐ[ℂ] Module.End ℂ V) (fin : G → R) (cmp : K → R)
  (ρ : Representation ℂ G V) (κ : Representation ℂ K V) (ξ : Representation ℂ G X)

/-- A simple quotient for the full operator action with the specified finite
representation embedded in its finite restriction. -/
def HasSimpleOperatorQuotientWithFiniteType : Prop :=
  ∃ (Y : Type uV) (_ : AddCommGroup Y) (_ : Module ℂ Y)
    (b : R →ₐ[ℂ] Module.End ℂ Y) (_ : Representation.IsIrreducible b.toMonoidHom)
    (σ : Representation ℂ G Y) (ν : Representation ℂ K Y),
    (∀ g, b (fin g) = σ g) ∧ (∀ k, b (cmp k) = ν k) ∧
    (∃ j : ξ.IntertwiningMap σ, Function.Injective j) ∧
    ∃ (U : Subrepresentation a.toMonoidHom)
      (q : U.toRepresentation.IntertwiningMap b.toMonoidHom), Function.Surjective q

/-- A nonzero finite-isotypic representation of the full algebra has a simple
operator subquotient still containing the prescribed finite representation. -/
theorem hasSimpleOperatorQuotientWithFiniteType_of_isotypic [Nontrivial V] [ξ.IsIrreducible]
    (hfin : ∀ g, a (fin g) = ρ g) (hcmp : ∀ k, a (cmp k) = κ k)
    (hρ : isotypicComponent ℂ[G] ρ.asModule ξ.asModule = ⊤) :
    HasSimpleOperatorQuotientWithFiniteType a fin cmp ξ := by
  let := moduleOfAlgebraAction a
  let : IsScalarTower ℂ R V := IsScalarTower.of_algebraMap_smul fun c x => by
    change a (algebraMap ℂ R c) x = c • x
    rw [a.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let P := Submodule.span R ({v} : Set V)
  let v' : P := ⟨v, Submodule.subset_span (Set.mem_singleton v)⟩
  let : Nontrivial P := ⟨⟨v', 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  let : Module.Finite R P := Module.Finite.span_of_finite R (Set.finite_singleton v)
  obtain ⟨N, hN, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R P)).resolve_left bot_ne_top
  let Y := P ⧸ N
  let b : R →ₐ[ℂ] Module.End ℂ Y := Algebra.lsmul ℂ ℂ Y
  have hb : Representation.IsIrreducible b.toMonoidHom := by
    apply (isSimpleModule_iff_irreducible_algebraAction b).mp
    exact isSimpleModule_iff_isCoatom.mpr hN
  let : IsSimpleModule R Y := isSimpleModule_iff_isCoatom.mpr hN
  let : Nontrivial Y := IsSimpleModule.nontrivial R Y
  have hf (g : G) (x : V) : fin g • x = ρ g x := LinearMap.congr_fun (hfin g) x
  have hk (k : K) (x : V) : cmp k • x = κ k x := LinearMap.congr_fun (hcmp k) x
  let σ := quotientRepresentation fin ρ hf P N
  let ν := quotientRepresentation cmp κ hk P N
  let ρP := submoduleRepresentation fin ρ hf P
  let i := submoduleIntertwiner fin ρ hf P
  let p := quotientIntertwiner fin ρ hf P N
  have hj := exists_embedding_of_isotypic_subquotient ξ hρ ρP i Subtype.val_injective p N.mkQ_surjective
  let U := submoduleOrderIsoOfAlgebraAction a P
  let q : U.toRepresentation.IntertwiningMap b.toMonoidHom :=
    ⟨N.mkQ.restrictScalars ℂ, fun o => LinearMap.ext fun x => N.mkQ.map_smul o x⟩
  exact ⟨Y, inferInstance, inferInstance, b, hb, σ, ν, fun _ => rfl, fun _ => rfl, hj, U, q,
    N.mkQ_surjective⟩

end SimpleQuotient

end Langlands.Automorphic
