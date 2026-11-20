import Langlands.GroupScheme.Torus.CocharacterFieldValue
import Mathlib.FieldTheory.Normal.Basic

/-! # Real torus cocharacters and intermediate fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.GroupScheme

open StarActionFiniteStage cocharacterLattice

variable (F E M : Type u) [Field F] [Field E] [Field M]
  [Algebra F E] [Algebra F M]
  [Algebra E M] [IsScalarTower F E M] [FiniteDimensional F E] [IsGalois F E]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffineHom T.X.hom]

local notation "TE" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap F E)) T
local notation "TM" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap F M)) T

/-- An invariant cocharacter after scalar extension to a field with a compatible
embedding of a Galois splitting field comes from an intermediate field whose
image is fixed by the chosen automorphism. The values at `-1` agree after extension. -/
def TorusIntermediateCocharacterStatement : Prop :=
  ∀ (F E M : Type u) [Field F] [Field E] [Field M]
    [Algebra F E] [Algebra F M]
    [Algebra E M] [IsScalarTower F E M] [FiniteDimensional F E] [IsGalois F E]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffineHom T.X.hom],
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj T).toGrp →
      ∀ (σ : M ≃ₐ[F] M)
        (eta : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F M)).obj T)),
        galoisRepresentation F M T σ eta = eta →
        ∃ (N : IntermediateField F E)
          (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F N)).obj T)),
          (∀ x : N, σ (algebraMap E M x) = algebraMap E M x) ∧
          WeilGm.cocharacterValue F M T (CommGroupScheme.groupHom eta) M (-1) =
            Lie.affineMap T.toGrp ((IsScalarTower.toAlgHom F E M).comp N.val)
              (WeilGm.cocharacterValue F N T (CommGroupScheme.groupHom ν) N (-1))

omit [IsAffineHom T.X.hom] in
private theorem cocharacterValue_neg_one_map (A B : Type u) [Field A] [Field B]
    [Algebra F A] [Algebra F B] [Algebra A B] [IsScalarTower F A B]
    (ξ : (Gm (Spec (CommRingCat.of A))).toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F A)).obj T.toGrp) :
    WeilGm.cocharacterValue F A T ξ B (-1) =
      Lie.affineMap T.toGrp (IsScalarTower.toAlgHom F A B)
        (WeilGm.cocharacterValue F A T ξ A (-1)) := by
  have h := WeilGm.cocharacterValue_naturality F A T ξ (Algebra.ofId A B) (-1)
  have hau : Units.map (Algebra.ofId A B).toMonoidHom (-1 : Aˣ) = (-1 : Bˣ) := by
    apply Units.ext
    change algebraMap A B (-1) = -1
    rw [map_neg, map_one]
  rw [hau] at h
  exact h

omit [IsAffineHom T.X.hom] in
private theorem cocharacterValue_neg_one_of_towerExtension (A B : Type u) [Field A] [Field B]
    [Algebra F A] [Algebra F B] [Algebra A B] [IsScalarTower F A B]
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F A)).obj T))
    (ξ : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F B)).obj T))
    (hξ : towerExtension F A B T ν = ξ) :
    WeilGm.cocharacterValue F B T (CommGroupScheme.groupHom ξ) B (-1) =
      Lie.affineMap T.toGrp (IsScalarTower.toAlgHom F A B)
        (WeilGm.cocharacterValue F A T (CommGroupScheme.groupHom ν) A (-1)) := by
  rw [← hξ, cocharacterValue_towerExtension]
  exact cocharacterValue_neg_one_map F T A B _

private def cocharacterStabilizer (ν : cocharacterLattice TE) : Subgroup (E ≃ₐ[F] E) where
  carrier := {σ | galoisRepresentation F E T σ ν = ν}
  one_mem' := by change galoisRepresentation F E T 1 ν = ν; rw [map_one]; rfl
  mul_mem' {σ τ} hσ hτ := by
    change galoisRepresentation F E T σ ν = ν at hσ
    change galoisRepresentation F E T τ ν = ν at hτ
    change galoisRepresentation F E T (σ * τ) ν = ν
    rw [map_mul, Module.End.mul_apply, hτ, hσ]
  inv_mem' {σ} hσ := by
    change galoisRepresentation F E T σ ν = ν at hσ
    change galoisRepresentation F E T σ⁻¹ ν = ν
    rw [← hσ] at ⊢
    exact (Representation.inv_self_apply _ _ _).trans hσ.symm

omit [Algebra F M] [Algebra E M]
    [IsScalarTower F E M] in
private theorem descend_cocharacter_to_stabilizerField (hTE : IsSplitTorus (TE).toGrp)
    (ν : cocharacterLattice TE) :
    let N := IntermediateField.fixedField (cocharacterStabilizer F E T ν)
    ∃ mu : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F N)).obj T),
      towerExtension F N E T mu = ν := by
  let H := cocharacterStabilizer F E T ν
  let N := IntermediateField.fixedField H
  let TN := (CommGroupScheme.baseChange (algebraBaseMap F N)).obj T
  let e := towerIsoOf (algebraBaseMap F N) (algebraBaseMap N E) T (algebraBaseMap F E)
    Lie.algebraBaseMap_tower
  let ν' := cocharacterLattice.congr e ν
  have hfix (τ : E ≃ₐ[N] E) : galoisRepresentation N E TN τ ν' = ν' := by
    have hτ : τ.restrictScalars F ∈ N.fixingSubgroup := (N.fixingSubgroupEquiv.symm τ).2
    have hτ' : τ.restrictScalars F ∈ H := by
      rwa [IntermediateField.fixingSubgroup_fixedField] at hτ
    have hν : galoisRepresentation F E T (τ.restrictScalars F) ν = ν := hτ'
    have hg := galoisRepresentation_scalarExtension F N E T hTE τ ν
    rw [hν] at hg
    exact hg.symm
  let : IsAffineHom TN.X.hom := inferInstanceAs
    (IsAffineHom (pullback.snd T.X.hom (algebraBaseMap F N)))
  let mu := cocharacterLattice.descend N E TN ν' hfix
  have hmu : cocharacterLattice.baseChange (algebraBaseMap N E) TN mu = ν' :=
    cocharacterLattice.baseChange_descend N E TN ν' hfix
  refine ⟨mu, ?_⟩
  change (cocharacterLattice.congr e).symm
    (cocharacterLattice.baseChange (algebraBaseMap N E) TN mu) = ν
  rw [hmu, show ν' = cocharacterLattice.congr e ν from rfl, AddEquiv.symm_apply_apply]

omit [IsAffineHom T.X.hom] [FiniteDimensional F E] [IsGalois F E] in
private theorem cocharacterValue_neg_one_intermediate (N : IntermediateField F E)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F N)).obj T))
    (νE : cocharacterLattice TE) (νM : cocharacterLattice TM)
    (hν : towerExtension F N E T ν = νE) (hνE : towerExtension F E M T νE = νM) :
    WeilGm.cocharacterValue F M T (CommGroupScheme.groupHom νM) M (-1) =
      Lie.affineMap T.toGrp ((IsScalarTower.toAlgHom F E M).comp N.val)
        (WeilGm.cocharacterValue F N T (CommGroupScheme.groupHom ν) N (-1)) := by
  let value := WeilGm.cocharacterValue F N T (CommGroupScheme.groupHom ν) N (-1)
  let e := IsScalarTower.toAlgHom F E M
  have h1 := cocharacterValue_neg_one_of_towerExtension F T E M νE νM hνE
  have h2 := cocharacterValue_neg_one_of_towerExtension F T N E ν νE hν
  exact h1.trans ((congrArg (Lie.affineMap T.toGrp e) h2).trans
    (Lie.affineMap_comp T.toGrp N.val e value).symm)

private theorem exists_fixed_intermediateEvaluation (hTE : IsSplitTorus (TE).toGrp)
    (σ' : E ≃ₐ[F] E) (τ : M → M)
    (hσ' : ∀ x : E, τ (algebraMap E M x) = algebraMap E M (σ' x))
    (νE : cocharacterLattice TE) (νM : cocharacterLattice TM)
    (hE : galoisRepresentation F E T σ' νE = νE)
    (hνE : towerExtension F E M T νE = νM) :
    ∃ (N : IntermediateField F E)
      (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F N)).obj T)),
      (∀ x : N, τ (algebraMap E M x) = algebraMap E M x) ∧
      WeilGm.cocharacterValue F M T (CommGroupScheme.groupHom νM) M (-1) =
        Lie.affineMap T.toGrp ((IsScalarTower.toAlgHom F E M).comp N.val)
        (WeilGm.cocharacterValue F N T (CommGroupScheme.groupHom ν) N (-1)) := by
  let H := cocharacterStabilizer F E T νE
  let N := IntermediateField.fixedField H
  have hdesc : ∃ ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F N)).obj T),
      towerExtension F N E T ν = νE := descend_cocharacter_to_stabilizerField F E T hTE νE
  obtain ⟨ν, hν⟩ := hdesc
  refine ⟨N, ν, ?_, cocharacterValue_neg_one_intermediate F E M T N ν νE νM hν hνE⟩
  intro x
  have hfix := (IntermediateField.mem_fixedField_iff H x.1).mp x.2 σ' hE
  rw [hσ', hfix]

/-- Descend an invariant cocharacter using a finite Galois splitting field
and compare its evaluation at `-1` through the two field extensions. -/
theorem exists_intermediateCocharacter (hTE : IsSplitTorus (TE).toGrp)
    (σ : M ≃ₐ[F] M) (eta : cocharacterLattice TM)
    (heta : galoisRepresentation F M T σ eta = eta) :
    ∃ (N : IntermediateField F E)
      (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F N)).obj T)),
      (∀ x : N, σ (algebraMap E M x) = algebraMap E M x) ∧
      WeilGm.cocharacterValue F M T (CommGroupScheme.groupHom eta) M (-1) =
        Lie.affineMap T.toGrp ((IsScalarTower.toAlgHom F E M).comp N.val)
          (WeilGm.cocharacterValue F N T (CommGroupScheme.groupHom ν) N (-1)) := by
  let σ' : E ≃ₐ[F] E := σ.restrictNormal E
  have hσ' (x : E) : σ (algebraMap E M x) = algebraMap E M (σ' x) :=
    (AlgEquiv.restrictNormal_commutes σ E x).symm
  have hext := towerExtension_bijective F E M T hTE
  obtain ⟨νE, hνE⟩ := hext.surjective eta
  have hE : galoisRepresentation F E T σ' νE = νE := by
    apply hext.injective
    rw [towerExtension_galois F E M T hTE σ' σ hσ', hνE, heta]
  exact exists_fixed_intermediateEvaluation F E M T hTE σ' σ hσ' νE eta hE hνE

/-- The intermediate-field comparison on the actual cocharacter lattices. -/
theorem torusIntermediateCocharacter : TorusIntermediateCocharacterStatement.{u} := by
  intro F E M _ _ _ _ _ _ _ _ _ T _ hTE σ eta heta
  exact exists_intermediateCocharacter F E M T hTE σ eta heta

end Langlands.GroupScheme
