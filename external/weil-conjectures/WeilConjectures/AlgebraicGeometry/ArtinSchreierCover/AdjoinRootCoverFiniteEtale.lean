/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover.AdjoinRootCover
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.RingTheory.Etale.StandardEtale
import WeilConjectures.Mathlib.RingTheory.AdjoinRoot

/-! # Finiteness and étaleness of `adjoinRootCover`

For a monic polynomial `P`, the base change `adjoinRootCover S P` of `Spec Γ(S)[T]/(P)` is
finite locally free of degree `deg P`; when moreover `P'` is a unit modulo `P` it is étale.
Source: blueprint, lemma-artin-schreier-character-sheaf, step (1); lem-weil-pbc-monic-quotient-free,
lem-weil-pbc-standard-etale-monic-derivative.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

noncomputable section

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {P : Polynomial Γ(S, ⊤)}

/-- A monic polynomial whose derivative is a unit modulo it gives a standard étale pair with
`g = 1`. -/
def standardEtalePairOfIsUnitDerivative {R : Type*} [CommRing R] {Q : R[X]} (hQ : Q.Monic)
    (hd : IsUnit (AdjoinRoot.mk Q (derivative Q))) : StandardEtalePair R where
  f := Q
  monic_f := hQ
  g := 1
  cond := by
    obtain ⟨v, hv⟩ := hd.exists_right_inv
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective v
    rw [← map_mul, ← (AdjoinRoot.mk Q).map_one, AdjoinRoot.mk_eq_mk] at hv
    obtain ⟨r, hr⟩ := hv
    exact ⟨q, -r, 0, by rw [pow_zero]; linear_combination hr⟩

/-- `R[T]/(Q)` is étale when `Q` is monic and `Q'` is a unit modulo `Q`. -/
lemma Algebra.etale_adjoinRoot_of_isUnit_derivative {R : Type u} [CommRing R] {Q : R[X]}
    (hQ : Q.Monic) (hd : IsUnit (AdjoinRoot.mk Q (derivative Q))) :
    Algebra.Etale R (AdjoinRoot Q) := by
  let E := standardEtalePairOfIsUnitDerivative hQ hd
  have hmap : E.HasMap (AdjoinRoot.root Q) :=
    ⟨by simp [E, standardEtalePairOfIsUnitDerivative, AdjoinRoot.aeval_eq], by
      simp [E, standardEtalePairOfIsUnitDerivative]⟩
  have hX : aeval E.X Q = 0 := StandardEtalePair.hasMap_X.1
  let e : E.Ring ≃ₐ[R] AdjoinRoot Q := AlgEquiv.ofAlgHom (E.lift _ hmap)
    (AdjoinRoot.liftAlgHom Q (Algebra.ofId R E.Ring) E.X hX)
    (AdjoinRoot.algHom_ext (by simp)) (StandardEtalePair.hom_ext (by simp))
  exact Algebra.Etale.of_equiv e

variable (S P)

/-- `adjoinRootCover S P` is finite for monic `P`. -/
lemma isFinite_adjoinRootCover (hP : P.Monic) : IsFinite (adjoinRootCover S P).hom := by
  have : Module.Finite Γ(S, ⊤) (AdjoinRoot P) := hP.finite_adjoinRoot
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (AdjoinRoot P)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  exact MorphismProperty.pullback_fst (P := @IsFinite) _ _ this

/-- `adjoinRootCover S P` is étale when `P` is monic and `P'` is a unit modulo `P`. -/
lemma etale_adjoinRootCover (hP : P.Monic) (hd : IsUnit (AdjoinRoot.mk P (derivative P))) :
    Etale (adjoinRootCover S P).hom := by
  have := Algebra.etale_adjoinRoot_of_isUnit_derivative hP hd
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (AdjoinRoot P)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  exact MorphismProperty.pullback_fst (P := @Etale) _ _ this

/-- `adjoinRootCover S P` is finite locally free of degree `deg P` for monic `P`. -/
lemma isFiniteLocallyFreeOfDegree_adjoinRootCover (hP : P.Monic) :
    (adjoinRootCover S P).hom.IsFiniteLocallyFreeOfDegree P.natDegree := by
  have : Module.Finite Γ(S, ⊤) (AdjoinRoot P) := hP.finite_adjoinRoot
  have : Module.Free Γ(S, ⊤) (AdjoinRoot P) := hP.free_adjoinRoot
  have : Algebra.FinitePresentation Γ(S, ⊤) (AdjoinRoot P) :=
    Algebra.FinitePresentation.quotient (A := Γ(S, ⊤)[X]) (Submodule.fg_span (by simp))
  have := isFinite_adjoinRootCover S P hP
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (AdjoinRoot P)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (AdjoinRoot P)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have : Flat (adjoinRootCover S P).hom :=
    MorphismProperty.pullback_fst (P := @Flat) _ _ inferInstance
  have : LocallyOfFinitePresentation (adjoinRootCover S P).hom :=
    MorphismProperty.pullback_fst (P := @LocallyOfFinitePresentation) _ _ inferInstance
  refine { fiberDegree_eq := fun x ↦ ?_ }
  have : IsFinite (pullback.fst S.toSpecΓ
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (AdjoinRoot P))))) :=
    isFinite_adjoinRootCover S P hP
  have : Nontrivial Γ(S, ⊤) := (S.presheaf.Γgerm x).hom.domain_nontrivial
  refine (Scheme.Hom.fiberDegree_of_isPullback
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (AdjoinRoot P))))
    (IsPullback.of_hasPullback _ _).flip x).trans ?_
  rw [Scheme.Hom.fiberDegree_SpecMap, Ideal.fiberDegree, Module.finrank_baseChange,
    (AdjoinRoot.powerBasis' hP).finrank, AdjoinRoot.powerBasis'_dim]

end AlgebraicGeometry
