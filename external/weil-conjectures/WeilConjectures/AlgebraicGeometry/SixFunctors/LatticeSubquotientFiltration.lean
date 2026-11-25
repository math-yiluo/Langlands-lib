/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedOrderedFiltration
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedSpectralLattices
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLocallyClosedScalarExtension

/-!
# Integral lattice subquotients of a lisse extension by zero

A lisse sheaf `L` with coefficients in a finite extension `E/ℚ_ℓ` on a locally closed
subscheme `S` of `X` has a stratification of `S` and integral lattices on the strata whose
rationalized extensions are the successive quotients of a filtration of the extension by zero
`a_! L` (`AlgebraicGeometry.ProEtale.exists_latticeSubquotientFiltration`).

## Implementation details

The assertion uses the condensed continuous coefficient rings, pulled back from Profinite, and
their internal module objects. Its lattices rationalize along their own inclusions. Filtration
terms are subobjects of the specified locally closed extension, which is `i_* u_!` through the
scheme-theoretic closure, for both integral and field coefficients.

The filtration is built from ordered integral lattice inclusions
(`exists_orderedSpectralLattices`) by pushing forward the open-prefix filtration; on each
stratum the invertible lattice adjoint identifies the rational restriction with the scalar
extension of the integral lattice, and this is carried through extension by zero.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- For a map of coefficient rings `c : A ⟶ B` and an immersion `a : S ⟶ X`: every lisse
`B`-module `L` on `S` has a stratification with lisse `A`-lattices on the strata whose
rationalizations are the successive quotients of a filtration of the extension of `L` along
`a`. -/
def LatticeSubquotientFiltrationData
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] {S X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) [IsImmersion a] : Prop :=
  ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S),
    IsLisseCoefficientModule B L →
    ∃ R : S.FiniteLocallyClosedStratification,
      (∀ b : Fin (R.n + 1),
        IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i)) ∧
      ∃ M : ∀ b : Fin R.n,
        Mod (Sheaf (Scheme.ProEt.topology (R.domain b)) Ab.{u + 1})
          (condensedRingObj A (R.domain b)),
        (∀ b : Fin R.n, IsLisseCoefficientModule A (M b) ∧
          ∃ ι : M b ⟶ (Mod.comap ((upperStarFromPoint (R.domain b)).map c)).obj
              ((CondensedRing.upperStar B (R.immersion b)).obj L),
            Mono ι ∧ IsIso
              (((Mod.extendRestrictAdjunction ((upperStarFromPoint (R.domain b)).map c)).homEquiv
                (M b) ((CondensedRing.upperStar B (R.immersion b)).obj L)).symm ι)) ∧
        ∃ F : Fin (R.n + 1) →
            Subobject ((coefficientHeartLocallyClosedExtension B a inferInstance).obj L),
          F 0 = ⊥ ∧ F (Fin.last R.n) = ⊤ ∧
          ∃ h : ∀ b : Fin R.n, F b.castSucc ≤ F b.succ,
            ∀ b : Fin R.n,
              letI : IsImmersion (R.immersion b) := R.isImmersion b
              Nonempty (cokernel (Subobject.ofLE (F b.castSucc) (F b.succ) (h b)) ≅
                (Mod.extendScalars ((upperStarFromPoint X).map c)).obj
                  ((coefficientHeartLocallyClosedExtension A (R.immersion b ≫ a)
                    inferInstance).obj (M b)))

/-- The lattice and ordered subquotient assertion for `a : S ⟶ X` over `k`, with coefficients
in `E` carrying the canonical spectral norm topology and its ring of integers. -/
def LatticeSubquotientFiltration (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (k : Type u) [Field k] {S X : Scheme.{u}}
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (a : S ⟶ X) [IsImmersion a] : Prop :=
  letI := spectralNorm.nontriviallyNormedField ℚ_[ℓ] E
  let A := coefficientHeartRingObj (Profinite.continuousMapRingSheafOfUniverse.{u, u}
    (Padic.coefficientExtensionIntegers ℓ E))
  letI : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ E))
      (fun U (a b : ULift.{u + 1} C(U.unop, Padic.coefficientExtensionIntegers ℓ E)) ↦
        mul_comm a b)
  let B := coefficientHeartRingObj (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
  letI : IsCommMonObj B := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
      (fun U (a b : ULift.{u + 1} C(U.unop, E)) ↦ mul_comm a b)
  let c := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)
  letI : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  LatticeSubquotientFiltrationData A B c a

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  coefficientHeartLocallyClosedExtension
  CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.upperStarLowerStarAdjunction
  CondensedRing.openImmersionLowerShriek

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Compose quotient comparisons over abstract coefficients to keep their structures shared.
private theorem lattice_filtration_assembly
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] {S X : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian X] (a : S ⟶ X) [IsImmersion a]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S))
    (R : S.FiniteLocallyClosedStratification)
    (ho : ∀ b : Fin (R.n + 1),
      IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i))
    (M : ∀ b : Fin R.n,
      Mod (Sheaf (Scheme.ProEt.topology (R.domain b)) Ab.{u + 1})
        (condensedRingObj A (R.domain b)))
    (he : ∀ b : Fin R.n, Nonempty
      ((Mod.extendScalars ((upperStarFromPoint (R.domain b)).map c)).obj (M b) ≅
        (CondensedRing.upperStar B (R.immersion b)).obj L)) :
    ∃ F : Fin (R.n + 1) →
        Subobject ((coefficientHeartLocallyClosedExtension B a inferInstance).obj L),
      F 0 = ⊥ ∧ F (Fin.last R.n) = ⊤ ∧
      ∃ h : ∀ b : Fin R.n, F b.castSucc ≤ F b.succ,
        ∀ b : Fin R.n,
          letI : IsImmersion (R.immersion b) := R.isImmersion b
          Nonempty (cokernel (Subobject.ofLE (F b.castSucc) (F b.succ) (h b)) ≅
            (Mod.extendScalars ((upperStarFromPoint X).map c)).obj
              ((coefficientHeartLocallyClosedExtension A (R.immersion b ≫ a)
                inferInstance).obj (M b))) := by
  obtain ⟨F, h0, hn, h, hq⟩ := exists_locallyClosedOrderedFiltration B a L R ho
  refine ⟨F, h0, hn, h, fun b ↦ ?_⟩
  have : IsImmersion (R.immersion b) := R.isImmersion b
  obtain ⟨e₀⟩ := hq b
  obtain ⟨e₁⟩ := he b
  obtain ⟨e₂⟩ := condensedLocallyClosedExtension_scalar A B c (R.immersion b ≫ a) (M b)
  exact ⟨e₀ ≪≫
    (coefficientHeartLocallyClosedExtension B (R.immersion b ≫ a) inferInstance).mapIso
      e₁.symm ≪≫ e₂⟩

private theorem lattice_filtration_from_lattices
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] {S X : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian X] (a : S ⟶ X) [IsImmersion a]
    (hlat :
  ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S),
    IsLisseCoefficientModule B L →
    ∃ R : S.FiniteLocallyClosedStratification,
      (∀ b : Fin (R.n + 1),
        IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i)) ∧
      ∃ M : ∀ b : Fin R.n,
        Mod (Sheaf (Scheme.ProEt.topology (R.domain b)) Ab.{u + 1})
          (condensedRingObj A (R.domain b)),
        ∀ b : Fin R.n, IsLisseCoefficientModule A (M b) ∧
          ∃ ι : M b ⟶ (Mod.comap ((upperStarFromPoint (R.domain b)).map c)).obj
              ((CondensedRing.upperStar B (R.immersion b)).obj L),
            Mono ι ∧ IsIso
              (((Mod.extendRestrictAdjunction ((upperStarFromPoint (R.domain b)).map c)).homEquiv
                (M b) ((CondensedRing.upperStar B (R.immersion b)).obj L)).symm ι)) :
    LatticeSubquotientFiltrationData A B c a := by
  unfold LatticeSubquotientFiltrationData
  intro L hL
  obtain ⟨R, ho, M, hM⟩ := hlat L hL
  refine ⟨R, ho, M, hM, ?_⟩
  apply lattice_filtration_assembly A B c a L R ho M
  intro b
  obtain ⟨_, ι, _, hi⟩ := hM b
  have := hi
  exact ⟨asIso (((Mod.extendRestrictAdjunction
    ((upperStarFromPoint (R.domain b)).map c)).homEquiv
      (M b) ((CondensedRing.upperStar B (R.immersion b)).obj L)).symm ι)⟩

/-- A lisse field-coefficient sheaf has stratified integral lattices whose rationalized
extensions are the successive quotients of its extension by zero. Ranks may vary and
filtration inclusions need not be strict. -/
theorem exists_latticeSubquotientFiltration (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (_hpℓ : p ≠ ℓ)
    (S X : Scheme.{u}) [S.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (a : S ⟶ X) [a.IsOver (Spec (.of k))] [IsImmersion a] :
    LatticeSubquotientFiltration ℓ E k a := by
  have hlat := exists_orderedSpectralLattices ℓ E p k _hpℓ S
  let := spectralNorm.nontriviallyNormedField ℚ_[ℓ] E
  let A := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers ℓ E))
  let B := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
  let c := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)
  have : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ E))
      (fun U (a b : ULift.{u + 1} C(U.unop, Padic.coefficientExtensionIntegers ℓ E)) ↦
        mul_comm a b)
  have : IsCommMonObj B := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
      (fun U (a b : ULift.{u + 1} C(U.unop, E)) ↦ mul_comm a b)
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  have : IsNoetherian S :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k)) }
  have result := @lattice_filtration_from_lattices _ _ _ _ _ _ _ _ S X
    inferInstance inferInstance a inferInstance hlat
  exact result

end AlgebraicGeometry.ProEtale
