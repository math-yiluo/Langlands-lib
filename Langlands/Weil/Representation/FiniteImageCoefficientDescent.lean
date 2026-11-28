import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Weil.Representation.AbsoluteIrreducibility
import Langlands.Weil.Representation.Restriction
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.RepresentationTheory.Maschke

/-! # Coefficient descent for irreducible representations of finite image -/

noncomputable section

set_option autoImplicit false

open scoped MonoidAlgebra TensorProduct

namespace Langlands.FiniteRepresentation

universe uk uE uG uV

variable {k : Type uk} [Field k] [IsAlgClosed k]
  (E : Type uE) [Field E] [Algebra k E] {G : Type uG} [Group G]

private theorem irreducible_extend_of_irreducible
    (B : FiniteRepresentation k G) (hB : Representation.IsIrreducible B.representation) :
    Representation.IsIrreducible (B.extendCoefficients E).representation := by
  apply irreducible_extendCoefficients_of_isAlgClosed k E
  let e : Equiv (B.extendCoefficients k) B :=
    Representation.Equiv.mk (TensorProduct.lid k B) fun g => by
      ext x
      change TensorProduct.lid k B (1 ⊗ₜ[k] (B.representation g x)) =
        B.representation g (TensorProduct.lid k B (1 ⊗ₜ[k] x))
      simp only [TensorProduct.lid_tmul, one_smul]
  exact (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv e).mpr hB

/-- Every irreducible action of a finite group descends along an extension of
an algebraically closed field when the group order is invertible there. -/
theorem exists_extendCoefficients_of_finiteGroup [Finite G] [NeZero (Nat.card G : k)]
    (A : FiniteRepresentation.{uE, uG, uV} E G)
    (hA : Representation.IsIrreducible A.representation) :
    ∃ B : FiniteRepresentation.{uk, uG, max uk uG} k G,
      Representation.IsIrreducible B.representation ∧
        Nonempty (Equiv (B.extendCoefficients E) A) := by
  let : Module k A := Module.restrictScalars k E A
  let : IsScalarTower k E A := IsScalarTower.restrictScalars k E A
  let ρ : Representation k G A :=
    { toFun := fun g => (A.representation g).restrictScalars k
      map_one' := by
        ext x
        simp
      map_mul' := fun g h => by
        ext x
        simp [Module.End.mul_apply] }
  obtain ⟨v, hv⟩ := CentralEigenspaceSplitting.exists_ne_zero_of_isIrreducible hA
  let ev := LinearMap.toSpanSingleton (R := k[G]) (M := ρ.asModule) (ρ.asModuleEquiv.symm v)
  have hev : ev ≠ 0 := by
    intro h
    have hz := congrArg (fun f : k[G] →ₗ[k[G]] ρ.asModule => f 1) h
    exact hv (ρ.asModuleEquiv.symm.map_eq_zero_iff.mp (by simpa [ev] using hz))
  obtain ⟨S, hS, hne⟩ := LinearMap.exists_ne_zero_of_sSup_eq_top hev
    {S | IsSimpleModule k[G] S} (IsSemisimpleModule.sSup_simples_eq_top _ _)
  let Sₖ := S.restrictScalars k
  let ρS := Representation.ofModule' (k := k) (G := G) Sₖ
  let : FiniteDimensional k Sₖ := Module.Finite.of_injective Sₖ.subtype Sₖ.subtype_injective
  let B := FiniteRepresentation.of ρS
  let eS : ρS.asModule ≃ₗ[k[G]] Sₖ :=
    { toAddEquiv := ρS.asModuleEquiv.toAddEquiv
      map_smul' := fun a x => by
        change ρS.asModuleEquiv (a • x) = a • ρS.asModuleEquiv x
        rw [Representation.asModuleEquiv_map_smul]
        change (MonoidAlgebra.lift k (Module.End k Sₖ) G
          ((MonoidAlgebra.lift k (Module.End k Sₖ) G).symm (Algebra.lsmul k k Sₖ)))
          a (ρS.asModuleEquiv x) = a • ρS.asModuleEquiv x
        rw [Equiv.apply_symm_apply]
        rfl }
  have hB : Representation.IsIrreducible B.representation := by
    let : IsSimpleModule k[G] S := hS
    exact (Representation.irreducible_iff_isSimpleModule_asModule ρS).mpr
      (IsSimpleModule.congr (eS.trans (S.restrictScalarsEquiv k)))
  let evS : Sₖ →ₗ[k[G]] ρ.asModule := ev.comp S.subtype
  let f₀ : B →ₗ[k] A := ρ.asModuleEquiv.toLinearMap.comp (evS.restrictScalars k)
  have hf₀ (g : G) (x : B) : f₀ (B.representation g x) = A.representation g (f₀ x) := by
    change ρ.asModuleEquiv (evS (MonoidAlgebra.of k G g • x)) =
      A.representation g (ρ.asModuleEquiv (evS x))
    rw [LinearMap.map_smul, ρ.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
    rfl
  let f : (B.extendCoefficients E).representation.IntertwiningMap A.representation :=
    ⟨f₀.liftBaseChange E, fun g => by
      ext x
      change f₀.liftBaseChange E ((B.extendCoefficients E).representation g (1 ⊗ₜ[k] x)) =
        A.representation g (f₀.liftBaseChange E (1 ⊗ₜ[k] x))
      rw [extendCoefficients_apply_tmul, LinearMap.liftBaseChange_one_tmul,
        LinearMap.liftBaseChange_one_tmul, hf₀]⟩
  have hf : f ≠ 0 := by
    intro h
    apply hne
    apply LinearMap.ext
    intro x
    apply ρ.asModuleEquiv.injective
    let y : B := (S.restrictScalarsEquiv k).symm x
    have hz := congrArg (fun F : (B.extendCoefficients E).representation.IntertwiningMap
      A.representation => F ((1 : E) ⊗ₜ[k] y)) h
    change f₀.liftBaseChange E (1 ⊗ₜ[k] y) = 0 at hz
    rw [LinearMap.liftBaseChange_one_tmul] at hz
    have heq : evS y = (ev.comp S.subtype) x := rfl
    rw [LinearMap.zero_apply, map_zero, ← heq]
    exact hz
  let := hA
  let := irreducible_extend_of_irreducible E B hB
  exact ⟨B, hB, ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩⟩

/-- A model of a finite-image action over the smaller field, with the original
kernel and an actual scalar-extension equivalence. -/
structure FiniteImageCoefficientModel (A : FiniteRepresentation.{uE, uG, uV} E G) where
  model : FiniteRepresentation.{uk, uG, max uk uV} k G
  irreducible : Representation.IsIrreducible model.representation
  finite_range : (Set.range model.representation).Finite
  ker_eq : model.representation.ker = A.representation.ker
  scalarEquiv : Equiv (model.extendCoefficients E) A

set_option maxHeartbeats 500000 in
/-- Descend an irreducible finite-image action through its finite image group.
The algebraically closed smaller field has characteristic zero. -/
def finiteImageCoefficientModel [CharZero k] (A : FiniteRepresentation.{uE, uG, uV} E G)
    (hA : Representation.IsIrreducible A.representation)
    (hfin : (Set.range A.representation).Finite) :
    FiniteImageCoefficientModel (k := k) E A := Classical.choice (by
  let ρ := A.representation.asGroupHom
  let Q := ρ.range
  let q : G →* Q := ρ.rangeRestrict
  have hQ : (Set.range ρ).Finite := by
    apply Set.Finite.of_finite_image (f := Units.val) ?_ Units.val_injective.injOn
    rw [← Set.range_comp']
    exact hfin
  let : Finite Q := hQ.to_subtype
  have : NeZero (Nat.card Q : k) := ⟨Nat.cast_ne_zero.mpr (Nat.card_pos (α := Q)).ne'⟩
  let A₀ := FiniteRepresentation.of ((Units.coeHom _).comp Q.subtype)
  have hA₀ : Representation.IsIrreducible A₀.representation := by
    let inflate : Subrepresentation A₀.representation → Subrepresentation A.representation :=
      fun S => ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (q g) hv⟩
    have hinj : Function.Injective inflate := by
      intro S T h
      exact Subrepresentation.toSubmodule_injective
        (congrArg (fun V : Subrepresentation A.representation => V.toSubmodule) h)
    let := hA
    have : Nontrivial (Subrepresentation A₀.representation) :=
      ⟨⊥, ⊤, fun h => bot_ne_top (congrArg inflate h)⟩
    exact ⟨fun S => (eq_bot_or_eq_top (inflate S)).imp (fun h => hinj h) (fun h => hinj h)⟩
  obtain ⟨B₀, _, ⟨e₀⟩⟩ := exists_extendCoefficients_of_finiteGroup (k := k) E A₀ hA₀
  let B := restrict q B₀
  let e : Equiv (B.extendCoefficients E) A :=
    Representation.Equiv.mk e₀.toLinearEquiv fun g => e₀.isIntertwining' (q g)
  have hB := irreducible_of_extendCoefficients E B
    ((CentralEigenspaceSplitting.isIrreducible_iff_of_equiv e).mpr hA)
  have hBfin : (Set.range B.representation).Finite :=
    (Set.finite_range B₀.representation).subset (fun _ ⟨g, hg⟩ => ⟨q g, hg⟩)
  refine ⟨⟨B, hB, hBfin, le_antisymm ?_ ?_, e⟩⟩
  · intro g hg
    change A.representation g = 1
    rw [← e.conj_apply_self g]
    change e.toLinearEquiv.conjRingEquiv
      ((Module.End.baseChangeHom k E B).toMonoidHom (B.representation g)) = 1
    rw [MonoidHom.mem_ker.mp hg, map_one, map_one]
  · intro g hg
    have hq : q g = 1 := Subtype.ext (Units.ext (MonoidHom.mem_ker.mp hg))
    change B₀.representation (q g) = 1
    rw [hq, map_one])

end Langlands.FiniteRepresentation
