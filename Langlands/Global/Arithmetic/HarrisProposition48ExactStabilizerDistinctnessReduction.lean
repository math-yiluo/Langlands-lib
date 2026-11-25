import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerDistinctnessStatement
import Langlands.Global.Arithmetic.HarrisProposition48StabilizerComparison
import Langlands.Global.Arithmetic.HarrisUniquePlace
import Langlands.Global.HeckeCharacterTransport
import Langlands.Global.HeckeConjugateInverseUnitary
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.ClassFieldTheory.Local.FiniteArtinTransport
import Langlands.Automorphic.Unramified.WeakInductionTowerChain
import Langlands.Automorphic.Unramified.UniquePlaceCyclicTower
import Langlands.Automorphic.Unramified.InductionBaseChangeHeckeFamily
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.Group

/-!
# Distinct Mackey components at the auxiliary place, from B6

Let `Q` be a Proposition 4.8 problem with Harris's exact-stabilizer condition at the auxiliary
place `Ps.v`, and `D` an intermediate field of `L/E`. Since only one place of `L` lies above
`Ps.v`, `Gal(L/D)` is solvable and `L/D` has a prime cyclic tower. A Mackey constituent of
`a` over `D` starts a unitary chain of weak base changes along this tower (Arthur–Clozel
III.4.2(c) at each step), ending at the Hecke family of the conjugates of
`a(ξ) ∘ N_{L/a(E')}`, provided the transport of attached spectral systems along field
isomorphisms holds. At the place of `L` above `Ps.v`, the components of these families for
two double cosets differ by the exact-stabilizer condition. B6 then separates the local
components of the two constituents.

The module states this reduction for the general and the totally complex form of the target.
-/

noncomputable section

universe u uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open AdelicFunctoriality LocalClassField LocalClassField.FiniteArtinTransport
open Langlands.Automorphic Langlands.Automorphic.Unramified
open scoped NumberField FiniteExtension

section UnitComponents

/-- The unit component of `ξ ∘ e` at `v` is that of `ξ` at the transported place. -/
theorem unitComponent_comap {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] (e : K ≃+* L) (ξ : HeckeCharacter L) (v : FinitePlace K)
    (z : Kˣ) :
    globalUnitComponent (HeckeCharacter.comap e ξ) v z =
      globalUnitComponent ξ (finitePlaceEquiv e.symm v) (Units.map e.toMonoidHom z) := by
  let w := finitePlaceEquiv e.symm v
  have hv : finitePlaceEquiv e w = v := by
    change ((finitePlaceEquiv e.symm).trans (finitePlaceEquiv e)) v = v
    rw [← finitePlaceEquiv_trans, e.self_trans_symm, finitePlaceEquiv_refl, Equiv.refl_apply]
  calc
    _ = globalUnitComponent (HeckeCharacter.comap e ξ) (finitePlaceEquiv e w) z :=
      congrArg (fun q => globalUnitComponent (HeckeCharacter.comap e ξ) q z) hv.symm
    _ = _ := by
      change (HeckeCharacter.comap e ξ).finiteComponent (finitePlaceEquiv e w)
          (Units.map (algebraMap K ((finitePlaceEquiv e w).adicCompletion K)).toMonoidHom z) =
        ξ.finiteComponent w (Units.map (algebraMap L (w.adicCompletion L)).toMonoidHom
          (Units.map e.toMonoidHom z))
      rw [HeckeCharacter.comap_finiteComponent]
      exact congrArg (ξ.finiteComponent w) (Units.ext (finiteCompletionEquiv_coe e w (z : K)))

/-- At a place `u` of `L` that is the only place above `v`, the unit component of
`χ ∘ N_{L/K}` is that of `χ` at `v` composed with the global norm. -/
theorem unitComponent_normComp {K L : Type u} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] (χ : HeckeCharacter K) (v : FinitePlace K)
    (u : FinitePlace L) [u.asIdeal.LiesOver v.asIdeal] (h : HasUniquePlaceAbove L v)
    (z : Lˣ) :
    globalUnitComponent (HeckeCharacter.normComp (L := L) χ) u z =
      globalUnitComponent χ v (normUnits K L z) :=
  (HeckeCharacter.normComp_finiteComponent (L := L) χ v ⟨u, inferInstance⟩
    (Units.map (algebraMap L (u.adicCompletion L)).toMonoidHom z)).trans
    (congrArg (χ.finiteComponent v) (localUnitNorm_globalUnits v u h z))

/-- Norms of units are transitive in a tower. -/
theorem normUnits_normUnits (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional K L] [FiniteDimensional M L] (z : Lˣ) :
    normUnits K M (normUnits M L z) = normUnits K L z :=
  Units.ext (Algebra.norm_norm (R := K) (S := M) (a := (z : L)))

end UnitComponents

namespace Proposition48Problem

variable (Q : Proposition48Problem.{uF})

/-- At a place of `D · a(E')` above `Ps.v`, the unit component of the Mackey character
`a(ξ) ∘ N` evaluated on norms from `L` is the unit component of `ξ` at `Ps.v'` on norms
from `L` of the `a⁻¹`-translate. -/
theorem mackeyCharacter_unitComponent (hQ : HasUniquePlaceAbove Q.L Q.Ps.v)
    (D : IntermediateField Q.E Q.L) (a : Q.L ≃ₐ[Q.E] Q.L)
    (vC : FinitePlace (Q.mackeyField D a)) [vC.asIdeal.LiesOver Q.Ps.v.asIdeal] (z : Q.Lˣ) :
    globalUnitComponent (Q.mackeyCharacter D a) vC (normUnits (Q.mackeyField D a) Q.L z) =
      globalUnitComponent Q.ξ Q.Ps.v'
        (normUnits Q.E' Q.L (Units.map a.symm.toRingEquiv.toMonoidHom z)) := by
  let A := Q.conjugateField a
  let C := Q.mackeyField D a
  let k : Q.E' ≃+* A := (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv
  let vA : FinitePlace A := finitePlaceEquiv k.symm Q.Ps.v'
  let : Algebra A C := (IntermediateField.inclusion (show A ≤ C from le_sup_right)).toAlgebra
  let : IsScalarTower Q.E A C := .of_algebraMap_eq' rfl
  let : IsScalarTower A C Q.L := .of_algebraMap_eq' rfl
  let hA : vA.asIdeal.LiesOver Q.Ps.v.asIdeal := by
    change (finitePlaceEquiv k.symm Q.Ps.v').asIdeal.LiesOver Q.Ps.v.asIdeal
    have hOver := finitePlaceEquiv_liesOver (K := Q.E) (L := A) (RingEquiv.refl Q.E)
      k.symm (Q.conjugateEmbedding a).equivFieldRange.symm.commutes Q.Ps.v Q.Ps.v'
    rw [finitePlaceEquiv_refl, Equiv.refl_apply] at hOver
    exact hOver
  let w := vC.under (𝓞 A)
  let hCw : vC.asIdeal.LiesOver w.asIdeal := ⟨rfl⟩
  have hw : w.asIdeal.LiesOver Q.Ps.v.asIdeal :=
    Ideal.LiesOver.tower_bot vC.asIdeal w.asIdeal Q.Ps.v.asIdeal
  let : Subsingleton (FinitePlacesAbove A Q.Ps.v) := finitePlacesAbove_subsingleton Q.Ps.v hQ
  have hwA : w = vA := congrArg Subtype.val
    (Subsingleton.elim (⟨w, hw⟩ : FinitePlacesAbove A Q.Ps.v) ⟨vA, hA⟩)
  let hCA : vC.asIdeal.LiesOver vA.asIdeal := hwA ▸ hCw
  have hCunique : HasUniquePlaceAbove C vA := by
    let : Subsingleton (FinitePlacesAbove C Q.Ps.v) := finitePlacesAbove_subsingleton Q.Ps.v hQ
    intro q q' hq hq'
    let := hq
    let := hq'
    have hqE := Ideal.LiesOver.trans q.asIdeal vA.asIdeal Q.Ps.v.asIdeal
    have hq'E := Ideal.LiesOver.trans q'.asIdeal vA.asIdeal Q.Ps.v.asIdeal
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨q, hqE⟩ : FinitePlacesAbove C Q.Ps.v) ⟨q', hq'E⟩)
  have hnorm : globalUnitComponent (Q.mackeyCharacter D a) vC (normUnits C Q.L z) =
      globalUnitComponent (Q.conjugateCharacter a) vA (normUnits A C (normUnits C Q.L z)) :=
    unitComponent_normComp (K := A) (L := C) (Q.conjugateCharacter a) vA vC hCunique _
  have hvA : finitePlaceEquiv k vA = Q.Ps.v' := by
    change ((finitePlaceEquiv k.symm).trans (finitePlaceEquiv k)) Q.Ps.v' = Q.Ps.v'
    rw [← finitePlaceEquiv_trans, k.self_trans_symm, finitePlaceEquiv_refl, Equiv.refl_apply]
  have haNorm : Units.map k.symm.toMonoidHom (normUnits A Q.L z) =
      normUnits Q.E' Q.L (Units.map a.symm.toRingEquiv.toMonoidHom z) :=
    (normUnits_map k.symm a.symm.toRingEquiv (RingHom.ext fun x => by
      change algebraMap Q.E' Q.L (k.symm x) = a.symm (x : Q.L)
      apply a.injective
      rw [a.apply_symm_apply]
      exact congrArg (fun x : A => (x : Q.L)) (k.apply_symm_apply x)) z).symm
  rw [hnorm, normUnits_normUnits A C Q.L]
  refine (unitComponent_comap k.symm Q.ξ vA (normUnits A Q.L z)).trans ?_
  rw [RingEquiv.symm_symm, hvA, haNorm]

/-- At the place `u` of `L` above `Ps.v`, the unit component of the conjugate
`a(ξ) ∘ N_{L/D·a(E')} ∘ ρ i` is the unit component of `ξ` at `Ps.v'` on norms from `L` of
the translate by `a⁻¹ ρ i`. -/
theorem conjugateNormFamily_unitComponent (hQ : HasUniquePlaceAbove Q.L Q.Ps.v)
    (D : IntermediateField Q.E Q.L) (a : Q.L ≃ₐ[Q.E] Q.L) {ι : Type*}
    (ρ : ι → Q.L ≃ₐ[D] Q.L) (i : ι) (u : FinitePlace Q.L) [u.asIdeal.LiesOver Q.Ps.v.asIdeal]
    (z : Q.Lˣ) :
    letI : Algebra D (Q.mackeyField D a) :=
      (IntermediateField.inclusion (show D ≤ Q.mackeyField D a from le_sup_left)).toAlgebra
    letI : IsScalarTower D (Q.mackeyField D a) Q.L := .of_algebraMap_eq' rfl
    globalUnitComponent (WeakInduction.conjugateNormFamily (Q.mackeyCharacter D a) ρ i) u z =
      globalUnitComponent Q.ξ Q.Ps.v' (normUnits Q.E' Q.L
        (Units.map a.symm.toRingEquiv.toMonoidHom
          (Units.map (ρ i).toRingEquiv.toMonoidHom z))) := by
  let C := Q.mackeyField D a
  let : Algebra D C := (IntermediateField.inclusion (show D ≤ C from le_sup_left)).toAlgebra
  let : IsScalarTower D C Q.L := .of_algebraMap_eq' rfl
  change globalUnitComponent (HeckeCharacter.comap (ρ i).toRingEquiv
    (HeckeCharacter.normComp (L := Q.L) (Q.mackeyCharacter D a))) u z = _
  rw [unitComponent_comap]
  have hu : finitePlaceEquiv (ρ i).toRingEquiv.symm u = u := by
    have hOver := finitePlaceEquiv_liesOver (RingEquiv.refl Q.E) (ρ i).toRingEquiv.symm
      (fun x => by
        change (ρ i).symm (algebraMap Q.E Q.L x) = algebraMap Q.E Q.L x
        rw [IsScalarTower.algebraMap_apply Q.E D Q.L]
        exact (ρ i).symm.commutes _) Q.Ps.v u
    rw [finitePlaceEquiv_refl, Equiv.refl_apply] at hOver
    exact hQ _ u hOver inferInstance
  rw [hu]
  let vC : FinitePlace C := u.under (𝓞 C)
  let huC : u.asIdeal.LiesOver vC.asIdeal := ⟨rfl⟩
  let hvC : vC.asIdeal.LiesOver Q.Ps.v.asIdeal :=
    Ideal.LiesOver.tower_bot u.asIdeal vC.asIdeal Q.Ps.v.asIdeal
  have hCu : HasUniquePlaceAbove Q.L vC := by
    intro q q' hq hq'
    let := hq
    let := hq'
    exact hQ q q' (Ideal.LiesOver.trans q.asIdeal vC.asIdeal Q.Ps.v.asIdeal)
      (Ideal.LiesOver.trans q'.asIdeal vC.asIdeal Q.Ps.v.asIdeal)
  rw [unitComponent_normComp (K := C) (L := Q.L) _ vC u hCu]
  exact Q.mackeyCharacter_unitComponent hQ D a vC _

/-- The Hecke family of conjugates of a Mackey character is unitary when `ξ` is. -/
theorem isUnitary_conjugateNormFamily (hξ : Q.ξ.IsUnitary) (D : IntermediateField Q.E Q.L)
    (a : Q.L ≃ₐ[Q.E] Q.L) {ι : Type*} (ρ : ι → Q.L ≃ₐ[D] Q.L) (i : ι) :
    letI : Algebra D (Q.mackeyField D a) :=
      (IntermediateField.inclusion (show D ≤ Q.mackeyField D a from le_sup_left)).toAlgebra
    letI : IsScalarTower D (Q.mackeyField D a) Q.L := .of_algebraMap_eq' rfl
    (WeakInduction.conjugateNormFamily (Q.mackeyCharacter D a) ρ i).IsUnitary := by
  let C := Q.mackeyField D a
  let : Algebra D C := (IntermediateField.inclusion (show D ≤ C from le_sup_left)).toAlgebra
  let : IsScalarTower D C Q.L := .of_algebraMap_eq' rfl
  change (HeckeCharacter.comap (ρ i).toRingEquiv
    (HeckeCharacter.normComp (L := Q.L) (Q.mackeyCharacter D a))).IsUnitary
  rw [HeckeCharacter.isUnitary_comap_iff]
  intro x
  exact hξ _

/-- **Part C.** Under the exact-stabilizer condition, for `a`, `a'` in different double cosets
`Gal(L/D) a Gal(L/E') ≠ Gal(L/D) a' Gal(L/E')`, the conjugate families of the two Mackey
characters have different components at the place `u` of `L` above `Ps.v`, for any
families `ρ`, `ρ'` in `Gal(L/D)` of the same length. -/
theorem not_sameFiniteComponentsAt (hQ : HasUniquePlaceAbove Q.L Q.Ps.v)
    (hParent : ∀ τ : Q.L ≃ₐ[Q.E] Q.L,
      (∀ z : Q.Lˣ, globalUnitComponent Q.ξ Q.Ps.v'
          (normUnits Q.E' Q.L (Units.map τ.toRingEquiv.toMonoidHom z)) =
        globalUnitComponent Q.ξ Q.Ps.v' (normUnits Q.E' Q.L z)) →
      ∀ x : Q.E', τ (algebraMap Q.E' Q.L x) = algebraMap Q.E' Q.L x)
    (D : IntermediateField Q.E Q.L) (a a' : Q.L ≃ₐ[Q.E] Q.L)
    (hne : DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup a ≠
      DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup a')
    {n : ℕ} (ρ ρ' : Fin (n + 1) → Q.L ≃ₐ[D] Q.L) (u : FinitePlace Q.L)
    [u.asIdeal.LiesOver Q.Ps.v.asIdeal] :
    letI : Algebra D (Q.mackeyField D a) :=
      (IntermediateField.inclusion (show D ≤ Q.mackeyField D a from le_sup_left)).toAlgebra
    letI : IsScalarTower D (Q.mackeyField D a) Q.L := .of_algebraMap_eq' rfl
    letI : Algebra D (Q.mackeyField D a') :=
      (IntermediateField.inclusion (show D ≤ Q.mackeyField D a' from le_sup_left)).toAlgebra
    letI : IsScalarTower D (Q.mackeyField D a') Q.L := .of_algebraMap_eq' rfl
    ¬ HeckeFamily.SameFiniteComponentsAt
      (WeakInduction.conjugateNormFamily (Q.mackeyCharacter D a) ρ)
      (WeakInduction.conjugateNormFamily (Q.mackeyCharacter D a') ρ') u := by
  let : Algebra D (Q.mackeyField D a) :=
    (IntermediateField.inclusion (show D ≤ Q.mackeyField D a from le_sup_left)).toAlgebra
  let : IsScalarTower D (Q.mackeyField D a) Q.L := .of_algebraMap_eq' rfl
  let : Algebra D (Q.mackeyField D a') :=
    (IntermediateField.inclusion (show D ≤ Q.mackeyField D a' from le_sup_left)).toAlgebra
  let : IsScalarTower D (Q.mackeyField D a') Q.L := .of_algebraMap_eq' rfl
  rintro ⟨e, he⟩
  let Φ : Q.Lˣ → ℂˣ := fun z => globalUnitComponent Q.ξ Q.Ps.v' (normUnits Q.E' Q.L z)
  have h0 (z : Q.Lˣ) :
      Φ (Units.map a.symm.toRingEquiv.toMonoidHom (Units.map (ρ 0).toRingEquiv.toMonoidHom z)) =
        Φ (Units.map a'.symm.toRingEquiv.toMonoidHom
          (Units.map (ρ' (e 0)).toRingEquiv.toMonoidHom z)) := by
    have h := DFunLike.congr_fun (he 0)
      (Units.map (algebraMap Q.L (u.adicCompletion Q.L)).toMonoidHom z)
    change globalUnitComponent (WeakInduction.conjugateNormFamily (Q.mackeyCharacter D a) ρ 0)
        u z = globalUnitComponent
          (WeakInduction.conjugateNormFamily (Q.mackeyCharacter D a') ρ' (e 0)) u z at h
    rw [Q.conjugateNormFamily_unitComponent hQ D a ρ 0 u z,
      Q.conjugateNormFamily_unitComponent hQ D a' ρ' (e 0) u z] at h
    exact h
  let σ : Q.L ≃ₐ[Q.E] Q.L := (ρ 0).restrictScalars Q.E
  let σ' : Q.L ≃ₐ[Q.E] Q.L := (ρ' (e 0)).restrictScalars Q.E
  let γ : Q.L ≃ₐ[Q.E] Q.L := a⁻¹ * σ * σ'⁻¹ * a'
  have hγ (y : Q.Lˣ) : globalUnitComponent Q.ξ Q.Ps.v'
      (normUnits Q.E' Q.L (Units.map γ.toRingEquiv.toMonoidHom y)) =
      globalUnitComponent Q.ξ Q.Ps.v' (normUnits Q.E' Q.L y) := by
    let z : Q.Lˣ := Units.map (ρ' (e 0)).symm.toRingEquiv.toMonoidHom
      (Units.map a'.toRingEquiv.toMonoidHom y)
    have e1 : Units.map γ.toRingEquiv.toMonoidHom y =
        Units.map a.symm.toRingEquiv.toMonoidHom
          (Units.map (ρ 0).toRingEquiv.toMonoidHom z) := by
      ext
      simp [γ, σ, σ', z, AlgEquiv.aut_inv]
    have e2 : Units.map a'.symm.toRingEquiv.toMonoidHom
        (Units.map (ρ' (e 0)).toRingEquiv.toMonoidHom z) = y := by
      ext
      simp [z]
    change Φ _ = Φ y
    rw [e1, h0 z, e2]
  have hfix := hParent γ hγ
  have hD (τ : Q.L ≃ₐ[D] Q.L) : τ.restrictScalars Q.E ∈ D.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact τ.commutes ⟨y, hy⟩
  apply hne
  rw [DoubleCoset.eq]
  refine ⟨σ' * σ⁻¹, mul_mem (hD _) (inv_mem (hD _)), γ, ?_, ?_⟩
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨x, rfl⟩
    change γ ((1 : Q.L ≃ₐ[Q.E] Q.L) (algebraMap Q.E' Q.L x)) =
      (1 : Q.L ≃ₐ[Q.E] Q.L) (algebraMap Q.E' Q.L x)
    simpa using hfix x
  · simp only [γ]
    group

end Proposition48Problem

/-- B6 for one prime cyclic tower `T` from `F` to `K`, all fields in `Type`: the body of
`TowerBaseChangeHeckeComponentStatement.{0, 0, uV, uV}` after `T`. -/
def TowerBaseChangeHeckeComponentAt (F K : Type) [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra F K]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient K)]
    (T : PrimeCyclicBaseChangeTower F K)
    [∀ i, CompactSpace (AdeleQuotient (T.level i))] : Prop :=
  ∀ (D D' : T.IsobaricChain),
    D.IsUnitary → D'.IsUnitary →
    D.IsSuccessiveWeakBaseChange.{0, 0, uV, uV} →
    D'.IsSuccessiveWeakBaseChange.{0, 0, uV, uV} →
    ∀ (r : ℕ) (S S' : CuspidalOperatorRealization F r),
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S' →
      D.StartsAtCuspidal S.isoClass → D'.StartsAtCuspidal S'.isoClass →
      ∀ (μ μ' : Fin (r + 1) → HeckeCharacter K),
        (∀ i, (μ i).IsUnitary) → (∀ i, (μ' i).IsUnitary) →
        D.EndsAtHeckeFamily.{0, 0, uV} μ →
        D'.EndsAtHeckeFamily.{0, 0, uV} μ' →
        ∀ (v : Global.FinitePlace F) (w : FinitePlacesAbove K v),
          (∀ w' : FinitePlacesAbove K v, w' = w) →
          ¬ HeckeFamily.SameFiniteComponentsAt μ μ' w.1 →
          ∀ (P : CuspidalSpectralPresentation.{0, uV} S)
            (P' : CuspidalSpectralPresentation.{0, uV} S'),
            (P.localComponent v).isoClass ≠ (P'.localComponent v).isoClass

/-- B6 gives `TowerBaseChangeHeckeComponentAt` for every tower. -/
theorem towerBaseChangeHeckeComponentAt
    (h : TowerBaseChangeHeckeComponentStatement.{0, 0, uV, uV}) (F K : Type) [Field F]
    [NumberField F] [Field K] [NumberField K] [Algebra F K]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient K)]
    (T : PrimeCyclicBaseChangeTower F K) [∀ i, CompactSpace (AdeleQuotient (T.level i))] :
    TowerBaseChangeHeckeComponentAt.{uV} F K T :=
  h F K T

/-- The totally complex form of B6 gives `TowerBaseChangeHeckeComponentAt` for every tower
over a totally complex base. -/
theorem towerBaseChangeHeckeComponentAt_of_isTotallyComplex
    (h : TowerBaseChangeHeckeComponentTCStatement.{0, 0, uV, uV}) (F K : Type) [Field F]
    [NumberField F] [IsTotallyComplex F] [Field K] [NumberField K] [Algebra F K]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient K)]
    (T : PrimeCyclicBaseChangeTower F K) [∀ i, CompactSpace (AdeleQuotient (T.level i))] :
    TowerBaseChangeHeckeComponentAt.{uV} F K T :=
  h F K T

namespace Proposition48Problem

variable (Q : Proposition48Problem.{uF})

/-- A Mackey constituent of `a` over `D` with unitary central character starts a unitary chain
of successive weak base changes along a prime cyclic tower from `D` to `L`, ending at the
unitary Hecke family of the conjugates of the Mackey character by right coset
representatives of `Gal(L/D · a(E'))` in `Gal(L/D)`. -/
theorem exists_mackeyChain (hP : CuspidalArithmeticSpectralTransportStatement.{0, 0, uV})
    (hξ : Q.ξ.IsUnitary) (D : IntermediateField Q.E Q.L) [IsGalois D Q.L]
    [CompactSpace (AdeleQuotient D)] [CompactSpace (AdeleQuotient Q.L)]
    (Tw : PrimeCyclicBaseChangeTower D Q.L) [∀ i, CompactSpace (AdeleQuotient (Tw.level i))]
    (hBC : ∀ (i : Fin Tw.length) (DF : IsobaricData (Tw.level i.castSucc)), DF.IsUnitary →
      ∃ DE : IsobaricData (Tw.level i.succ), DE.IsUnitary ∧
        letI := Tw.stepAlgebra i
        IsobaricData.IsWeakBaseChangeOf.{0, 0, uV, uV} DE DF)
    (a : Q.L ≃ₐ[Q.E] Q.L) {r : ℕ} (T : CuspidalOperatorRealization D r)
    (hT : ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T)
    (hTa : Q.IsMackeyConstituent.{uF, uV} D a T.isoClass) :
    letI : Algebra D (Q.mackeyField D a) :=
      (IntermediateField.inclusion (show D ≤ Q.mackeyField D a from le_sup_left)).toAlgebra
    letI : IsScalarTower D (Q.mackeyField D a) Q.L := .of_algebraMap_eq' rfl
    ∃ (ρ : Fin (r + 1) → Q.L ≃ₐ[D] Q.L) (Dc : Tw.IsobaricChain), Dc.IsUnitary ∧
      Dc.IsSuccessiveWeakBaseChange.{0, 0, uV, uV} ∧ Dc.StartsAtCuspidal T.isoClass ∧
      (∀ i, (WeakInduction.conjugateNormFamily (Q.mackeyCharacter D a) ρ i).IsUnitary) ∧
      Dc.EndsAtHeckeFamily.{0, 0, uV}
        (WeakInduction.conjugateNormFamily (Q.mackeyCharacter D a) ρ) := by
  let : Algebra D (Q.mackeyField D a) :=
    (IntermediateField.inclusion (show D ≤ Q.mackeyField D a from le_sup_left)).toAlgebra
  let : IsScalarTower D (Q.mackeyField D a) Q.L := .of_algebraMap_eq' rfl
  have hind : T.isoClass.IsWeakAutomorphicInductionOf.{0, 0, uV} (Q.mackeyCharacter D a) := hTa
  obtain ⟨ρ, hρ⟩ := exists_isRightCosetFamily (K := D) (L := Q.L) (M := Q.mackeyField D a)
    (r + 1) hind.rank_eq
  obtain ⟨Dc, h1, h2, h3, h4⟩ :=
    Tw.exists_isobaricChain_endsAtHeckeFamily hP hBC T hT (Q.mackeyCharacter D a) hind ρ hρ
  exact ⟨ρ, Dc, h1, h2, h3, fun i => Q.isUnitary_conjugateNormFamily hξ D a ρ i, h4⟩

/-- **The reduction, with abstract inputs.** Under the exact-stabilizer validity of `Q`, the
transport of attached spectral systems along field isomorphisms, unitary weak base changes
along every step of every prime cyclic tower from `D` to `L`, and B6 for every such tower,
Mackey constituents of different double cosets have different components at every place of
`D` above `Ps.v`. -/
theorem hasDistinctMackeyComponents_of_tower
    (hP : CuspidalArithmeticSpectralTransportStatement.{0, 0, uV})
    (D : IntermediateField Q.E Q.L) (hQ : Q.IsAuxiliaryExactStabilizerValid)
    (hBC : ∀ (Tw : PrimeCyclicBaseChangeTower D Q.L)
      [∀ i, CompactSpace (AdeleQuotient (Tw.level i))]
      (i : Fin Tw.length) (DF : IsobaricData (Tw.level i.castSucc)), DF.IsUnitary →
      ∃ DE : IsobaricData (Tw.level i.succ), DE.IsUnitary ∧
        letI := Tw.stepAlgebra i
        IsobaricData.IsWeakBaseChangeOf.{0, 0, uV, uV} DE DF)
    (hB6 : ∀ (Tw : PrimeCyclicBaseChangeTower D Q.L)
      [∀ i, CompactSpace (AdeleQuotient (Tw.level i))],
      letI := compactSpace_adeleQuotient D
      letI := compactSpace_adeleQuotient Q.L
      TowerBaseChangeHeckeComponentAt.{uV} D Q.L Tw) :
    Q.HasDistinctMackeyComponents.{uF, uV} D := by
  obtain ⟨hrec, -, -, hnormal, -, hcompat, hunique, -, hexact, -, -, hinv, hcomp⟩ := hQ
  let : IsNormalClosure Q.E Q.E' Q.L := hnormal
  let : Normal Q.E Q.L := IsNormalClosure.normal (K := Q.E')
  let : IsGalois Q.E Q.L := ⟨⟩
  have hParent := (Q.Ps.exactWeilStabilizer_iff_global hcompat hunique Q.e hrec
    Q.ξ Q.χs hcomp).mp hexact
  have hξ : Q.ξ.IsUnitary := HeckeConjugateInverse.isUnitary_of_isConjugateInverse Q.ξ hinv
  let : IsGalois D Q.L := IsGalois.tower_top_of_isGalois Q.E D Q.L
  have : Group.IsSolvable (Q.L ≃ₐ[Q.E] Q.L) := isSolvable_of_hasUniquePlaceAbove Q.Ps.v hunique
  have : Group.IsSolvable (Q.L ≃ₐ[D] Q.L) :=
    Group.isSolvable_of_isSolvable_injective (AlgEquiv.restrictScalarsHom_injective Q.E)
  obtain ⟨Tw⟩ := PrimeCyclicBaseChangeTower.nonempty_of_isSolvable D Q.L
  let : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
  let : CompactSpace (AdeleQuotient Q.L) := compactSpace_adeleQuotient Q.L
  let : ∀ i, CompactSpace (AdeleQuotient (Tw.level i)) := fun i => compactSpace_adeleQuotient _
  intro a a' hne r T U hT hU hTa hUa' w P P'
  obtain ⟨ρ, Dc, hDU, hDs, hD0, hμ, hDend⟩ := Q.exists_mackeyChain hP hξ D Tw (hBC Tw) a T hT hTa
  obtain ⟨ρ', Dc', hDU', hDs', hD0', hμ', hDend'⟩ :=
    Q.exists_mackeyChain hP hξ D Tw (hBC Tw) a' U hU hUa'
  obtain ⟨u, hu⟩ := exists_place_above (L := Q.L) w.1
  let : w.1.asIdeal.LiesOver Q.Ps.v.asIdeal := w.2
  let : u.asIdeal.LiesOver Q.Ps.v.asIdeal :=
    Ideal.LiesOver.trans u.asIdeal w.1.asIdeal Q.Ps.v.asIdeal
  have huniq : ∀ w' : FinitePlacesAbove Q.L w.1, w' = ⟨u, hu⟩ := by
    intro w'
    let := w'.2
    exact Subtype.ext (hunique _ _
      (Ideal.LiesOver.trans w'.1.asIdeal w.1.asIdeal Q.Ps.v.asIdeal) inferInstance)
  exact hB6 Tw Dc Dc' hDU hDU' hDs hDs' r T U hT hU hD0 hD0' _ _ hμ hμ' hDend hDend' w.1
    ⟨u, hu⟩ huniq
    (Q.not_sameFiniteComponentsAt hunique (fun τ => (hParent τ).mp) D a a' hne ρ ρ' u) P P'

end Proposition48Problem

/-- The general target reduced to the transport of attached spectral systems along field
isomorphisms (`CuspidalArithmeticSpectralTransportStatement`). -/
def Proposition48ExactStabilizerDistinctnessReductionStatement : Prop :=
  CuspidalArithmeticSpectralTransportStatement.{0, 0, uV} →
    Proposition48ExactStabilizerDistinctnessStatement.{uF, uV}

/-- The totally complex target reduced to the transport of attached spectral systems along
field isomorphisms. -/
def Proposition48ExactStabilizerDistinctnessTCReductionStatement : Prop :=
  CuspidalArithmeticSpectralTransportStatement.{0, 0, uV} →
    Proposition48ExactStabilizerDistinctnessTCStatement.{uF, uV}

/-- **The reduction**, general form: B6 with Arthur–Clozel III.4.2(c) and the transport
of attached spectral systems give distinct Mackey components at the auxiliary place. -/
theorem proposition48ExactStabilizerDistinctnessReduction :
    Proposition48ExactStabilizerDistinctnessReductionStatement.{uF, uV} := by
  intro hP hB6 hBC _ Q D hQ _ _
  exact Q.hasDistinctMackeyComponents_of_tower hP D hQ
    (fun Tw _ => Tw.exists_weakBaseChange_step hBC)
    (fun Tw _ => by
      let := compactSpace_adeleQuotient D
      let := compactSpace_adeleQuotient Q.L
      exact towerBaseChangeHeckeComponentAt hB6 D Q.L Tw)

/-- **The reduction**, totally complex form: every intermediate field of `L/E` is totally
complex, since the CM field `E` is. -/
theorem proposition48ExactStabilizerDistinctnessTCReduction :
    Proposition48ExactStabilizerDistinctnessTCReductionStatement.{uF, uV} := by
  intro hP hB6 hBC _ Q D hQ _ _
  have : IsTotallyComplex D := isTotallyComplex_of_algebra Q.E D
  exact Q.hasDistinctMackeyComponents_of_tower hP D hQ
    (fun Tw _ => Tw.exists_weakBaseChange_step_of_isTotallyComplex hBC)
    (fun Tw _ => by
      let := compactSpace_adeleQuotient D
      let := compactSpace_adeleQuotient Q.L
      exact towerBaseChangeHeckeComponentAt_of_isTotallyComplex hB6 D Q.L Tw)

end Langlands.Global.Harris
