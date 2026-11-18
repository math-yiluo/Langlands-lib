import Langlands.GroupScheme.Torus.NagataReductionStatements
import Langlands.GroupScheme.FiniteTypeIdentityComponent
import Langlands.GroupScheme.MatrixRepresentation.ComponentAveraging
import Langlands.GroupScheme.MatrixRepresentation.MultiplicativeTypeSemisimplicity
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Mathlib.Algebra.CharP.Invertible

/-! # The sufficient implication in Nagata's theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace IdentityComponent.FiniteType

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType G.X.hom]
  {H : GroupScheme (Spec (CommRingCat.of k))}

/-- Any supplied open identity-component presentation is the canonical one. -/
def isoOfIdentityRange (i : H ⟶ G) [IsOpenImmersion i.hom.hom.left]
    (hi : Set.range i.hom.hom.left = IdentityComponent.identitySet G) :
    H ≅ finiteTypeIdentityComponent G where
  hom := IdentityComponent.liftHom (finiteTypeIdentityComponentι G) i (by
    rw [range_finiteTypeIdentityComponentι, hi])
  inv := IdentityComponent.liftHom i (finiteTypeIdentityComponentι G) (by
    rw [range_finiteTypeIdentityComponentι, hi])
  hom_inv_id := IdentityComponent.hom_ext_of_isOpenImmersion i (by simp)
  inv_hom_id := IdentityComponent.hom_ext_of_isOpenImmersion
    (finiteTypeIdentityComponentι G) (by simp)

end IdentityComponent.FiniteType

namespace MatrixRepresentation

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Multiplicative type of the identity component and invertible component order
supply actual stable complements over an algebraically closed field. -/
theorem isSemisimple_of_multiplicativeType_identityComponent
    (ρ : MatrixRepresentation G n) (p : ℕ) [CharP k p]
    (hMT : IsMultiplicativeType (finiteTypeIdentityComponent G))
    (horder : ¬ p ∣ Nat.card (IdentityComponent.ComponentPointQuotient G)) :
    ρ.IsSemisimple := by
  classical
  let : Finite (rationalPoints G ⧸ IdentityComponent.rationalIdentityKernel G) :=
    inferInstanceAs (Finite (IdentityComponent.ComponentPointQuotient G))
  let : Fintype (rationalPoints G ⧸ IdentityComponent.rationalIdentityKernel G) :=
    Fintype.ofFinite _
  have hcard : ¬ p ∣ Fintype.card
      (rationalPoints G ⧸ IdentityComponent.rationalIdentityKernel G) := by
    simpa only [IdentityComponent.ComponentPointQuotient, Nat.card_eq_fintype_card] using horder
  let := invertibleOfCharPNotDvd (K := k) hcard
  apply (isSemisimple_iff_exists_stable_complement ρ).mpr
  intro V hV
  have hV₀ := hV.restrict (finiteTypeIdentityComponentι G)
  have hρ₀ := isSemisimple_of_isMultiplicativeType
    (ρ.restrict (finiteTypeIdentityComponentι G)) hMT
  obtain ⟨W, hW, hVW⟩ :=
    (isSemisimple_iff_exists_stable_complement _).mp hρ₀ V hV₀
  obtain ⟨P, hP⟩ := exists_equivariantProjection_of_componentProjection ρ
    (finiteTypeIdentityComponentι G)
    (IdentityComponent.FiniteType.range_finiteTypeIdentityComponentι G)
    (IdentityComponent.FiniteType.isNormal_range_finiteTypeIdentityComponentι G)
    V hV (V.projection W hVW) (isEquivariantProjection_of_isCompl hV₀ hW hVW)
  exact ⟨LinearMap.ker P, hP.stable_complement⟩

end MatrixRepresentation

/-- The exact sufficient implication in Nagata's theorem, over arbitrary fields
and with the non-smooth identity-component scope of the published statement. -/
theorem nagataLinearlyReductiveSufficiency : NagataLinearlyReductiveSufficiencyStatement.{u} := by
  intro k _ p _ _hp G _ _ h
  rcases h with ⟨⟨H, i, hi, himage, hMT⟩, horder⟩
  let := hi
  have hMT₀ : IsMultiplicativeType (finiteTypeIdentityComponent G) :=
    IsMultiplicativeType.of_iso
      (IdentityComponent.FiniteType.isoOfIdentityRange G i himage).symm hMT
  let K := AlgebraicClosure k
  let GK := (GroupScheme.baseChange (algebraBaseMap k K)).obj G
  let : LocallyOfFiniteType GK.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom
      (algebraBaseMap k K)))
  let : IsAffineHom GK.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
      (algebraBaseMap k K)))
  have hMTK : IsMultiplicativeType (finiteTypeIdentityComponent GK) :=
    IsMultiplicativeType.of_iso
      (IdentityComponent.FiniteType.baseChangeIso G (algebraMap k K)).symm
      (MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic
        k K (finiteTypeIdentityComponent G) hMT₀)
  have horderK : ¬ p ∣ Nat.card (IdentityComponent.ComponentPointQuotient GK) := by
    simpa only [IdentityComponent.natCard_geometricComponents_eq_componentPointQuotient]
      using horder
  intro n ρ
  change ρ.IsSemisimple
  apply MatrixRepresentation.isSemisimple_of_baseChange (K := K) ρ
  exact MatrixRepresentation.isSemisimple_of_multiplicativeType_identityComponent
    (ρ.baseChange (algebraBaseMap k K)) p hMTK horderK

end Langlands.GroupScheme
