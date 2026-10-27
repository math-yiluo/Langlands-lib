import Langlands.ClassFieldTheory.Local.InvariantTransferConsequencesStatement
import Langlands.ClassFieldTheory.Local.SameBaseConjugacy

/-!
# Relative conjugacy from the inflation and restriction laws

View the target extension `M` over the source base `K` through the base
equivalence. Conjugacy along a compatible square then factors as conjugacy
over the same base followed by restriction along the degree-one extension
`K'/K`. The restriction law in degree one and same-base conjugacy give the
conjugacy law.
-/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u

section Factorization

variable {K K' L M : Type u} [Field K] [Field K'] [Field L] [Field M]
  [Algebra K L] [Algebra K' M] [Algebra K K'] [Algebra K M] [IsScalarTower K K' M]

/-- Conjugacy along a compatible square factors through conjugacy over the
same base followed by restriction to the target base. -/
theorem relativeConjugacy_hom_eq_comp_relativeRestriction
    (eK : K ≃+* K') (eL : L ≃+* M)
    (h : CompatibleFieldEquivalences eK eL)
    (h' : CompatibleFieldEquivalences (RingEquiv.refl K) eL) (n : ℕ) :
    (relativeConjugacy eK eL h n).hom =
      (relativeConjugacy (RingEquiv.refl K) eL h' n).hom ≫
        relativeRestriction K K' M n := by
  unfold relativeConjugacy groupCohomology.mapIso
  dsimp only
  rw [← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext σ x
    rfl
  · rfl

end Factorization

namespace InvariantFamily

variable {p : ℕ} [Fact p.Prime]

/-- Inflation compatibility and the restriction law imply the relative
conjugacy law. -/
theorem relativeConjugacy_of_inflationCompatibility (I : InvariantFamily.{u,u} p)
    (hInf : I.InflationCompatibility) (hRes : I.RelativeRestriction) :
    I.RelativeConjugacy := by
  intro F E L M _ _ _ _ _ _ _ _ eF eL h x
  let _ : Algebra F.Carrier E.Carrier := eF.toRingEquiv.toRingHom.toAlgebra
  let _ : Algebra F.Carrier M :=
    ((algebraMap E.Carrier M).comp eF.toRingEquiv.toRingHom).toAlgebra
  have _ : IsScalarTower F.Carrier E.Carrier M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower (Padic p) F.Carrier E.Carrier :=
    IsScalarTower.of_algebraMap_eq fun a => (eF.commutes a).symm
  have hbij : Function.Bijective (Algebra.linearMap F.Carrier E.Carrier) :=
    eF.bijective
  have _ : FiniteDimensional F.Carrier E.Carrier :=
    Module.Finite.of_surjective (Algebra.linearMap F.Carrier E.Carrier) hbij.2
  have _ : FiniteDimensional F.Carrier M := Module.Finite.trans E.Carrier M
  have _ : IsGalois F.Carrier M :=
    IsGalois.of_equiv_equiv (F := E.Carrier) (E := M)
      (f := eF.symm.toRingEquiv) (g := RingEquiv.refl M) (by
        ext y
        change algebraMap E.Carrier M (eF (eF.symm y)) = algebraMap E.Carrier M y
        rw [eF.apply_symm_apply])
  have hdeg : Module.finrank F.Carrier E.Carrier = 1 := by
    rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq, Module.finrank_self]
  let e : L ≃ₐ[F.Carrier] M := { eL with commutes' := h }
  have h' : CompatibleFieldEquivalences (RingEquiv.refl F.Carrier) e.toRingEquiv := h
  rw [relativeConjugacy_hom_eq_comp_relativeRestriction eF.toRingEquiv eL h h' 2,
    ConcreteCategory.comp_apply, hRes F E M, hdeg, one_nsmul]
  exact I.relative_relativeConjugacy_refl_of_inflationCompatibility hInf F e h' x

end InvariantFamily

/-- Relative invariants commute with conjugacy for every family with the
inflation and restriction laws. -/
theorem invariantRelativeConjugacy : InvariantRelativeConjugacyStatement.{u} := by
  intro p _ I hInf hRes
  exact I.relativeConjugacy_of_inflationCompatibility hInf hRes

end Langlands.ClassFieldTheory.Local
