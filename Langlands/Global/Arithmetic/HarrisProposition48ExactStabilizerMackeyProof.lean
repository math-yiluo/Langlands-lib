import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerInheritanceStatement
import Langlands.Global.Arithmetic.HarrisProposition48StabilizerComparison
import Langlands.Global.HeckeCharacterTransport
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.ClassFieldTheory.Local.FiniteArtinTransport
import Mathlib.RingTheory.Norm.Transitivity

/-! # Inheritance of Harris's exact stabilizer for Mackey children -/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open AdelicFunctoriality LocalClassField LocalClassField.FiniteArtinTransport
open scoped NumberField FiniteExtension

private theorem globalUnitComponent_comap {K L : Type*} [Field K] [NumberField K]
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

private theorem mackeyUnitComponent (Q R : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) (a : Gal(Q.L/Q.E))
    (e : R.E ≃+* D) (e' : R.E' ≃+* Q.mackeyField D a)
    (he : ∀ x : R.E, (e' (algebraMap R.E R.E' x) : Q.L) = (e x : Q.L))
    (hξ : R.ξ = HeckeCharacter.comap e' (Q.mackeyCharacter D a))
    (hv : (finitePlaceEquiv e.symm R.Ps.v).asIdeal.LiesOver Q.Ps.v.asIdeal)
    (hQ : HasUniquePlaceAbove Q.L Q.Ps.v) (z : R.E'ˣ) :
    let A := Q.conjugateField a
    let C := Q.mackeyField D a
    let k : Q.E' ≃+* A := (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv
    letI : Algebra A C := (IntermediateField.inclusion
      (show A ≤ C from le_sup_right)).toAlgebra
    globalUnitComponent R.ξ R.Ps.v' z = globalUnitComponent Q.ξ Q.Ps.v'
      (Units.map k.symm.toMonoidHom (normUnits A C (Units.map e'.toMonoidHom z))) := by
  intro A C k
  let vD := finitePlaceEquiv e.symm R.Ps.v
  let vC : FinitePlace C := finitePlaceEquiv e'.symm R.Ps.v'
  let vA : FinitePlace A := finitePlaceEquiv k.symm Q.Ps.v'
  let : Algebra D C := (IntermediateField.inclusion (show D ≤ C from le_sup_left)).toAlgebra
  let : Algebra A C := (IntermediateField.inclusion (show A ≤ C from le_sup_right)).toAlgebra
  let : IsScalarTower Q.E D C := .of_algebraMap_eq' rfl
  let : IsScalarTower Q.E A C := .of_algebraMap_eq' rfl
  let : vD.asIdeal.LiesOver Q.Ps.v.asIdeal := hv
  have heinv (x : D) : e'.symm (algebraMap D C x) = algebraMap R.E R.E' (e.symm x) := by
    apply e'.injective
    rw [e'.apply_symm_apply]
    apply Subtype.ext
    change (x : Q.L) = (e' (algebraMap R.E R.E' (e.symm x)) : Q.L)
    simpa only [e.apply_symm_apply] using (he (e.symm x)).symm
  let : vC.asIdeal.LiesOver vD.asIdeal :=
    finitePlaceEquiv_liesOver e.symm e'.symm heinv R.Ps.v R.Ps.v'
  let : vC.asIdeal.LiesOver Q.Ps.v.asIdeal :=
    Ideal.LiesOver.trans vC.asIdeal vD.asIdeal Q.Ps.v.asIdeal
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
  let zC : Cˣ := Units.map e'.toMonoidHom z
  have hnorm : globalUnitComponent (Q.mackeyCharacter D a) vC zC =
      globalUnitComponent (Q.conjugateCharacter a) vA (normUnits A C zC) := by
    have h := HeckeCharacter.normComp_finiteComponent (K := A) (L := C) (Q.conjugateCharacter a) vA
      ⟨vC, hCA⟩ (Units.map (algebraMap C (vC.adicCompletion C)).toMonoidHom zC)
    exact h.trans (congrArg ((Q.conjugateCharacter a).finiteComponent vA)
      (localUnitNorm_globalUnits (K := A) (L := C) vA vC hCunique zC))
  rw [hξ]
  exact (globalUnitComponent_comap e' _ R.Ps.v' z).trans
    (hnorm.trans (globalUnitComponent_comap k.symm Q.ξ vA (normUnits A C zC) |>.trans (by
      have hvA : finitePlaceEquiv k vA = Q.Ps.v' := by
        change ((finitePlaceEquiv k.symm).trans (finitePlaceEquiv k)) Q.Ps.v' = Q.Ps.v'
        rw [← finitePlaceEquiv_trans, k.self_trans_symm, finitePlaceEquiv_refl, Equiv.refl_apply]
      simp only [RingEquiv.symm_symm, hvA, zC])))

private theorem normUnits_tower (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional K L] [FiniteDimensional M L] (z : Lˣ) :
    normUnits K M (normUnits M L z) = normUnits K L z :=
  Units.ext (Algebra.norm_norm (R := K) (S := M) (a := (z : L)))

private theorem mackeyGlobalStabilizer (Q R : Proposition48Problem.{uF})
    [Normal Q.E Q.L] (D : IntermediateField Q.E Q.L) (a : Gal(Q.L/Q.E))
    (e : R.E ≃+* D) (e' : R.E' ≃+* Q.mackeyField D a) (j : R.L →+* Q.L)
    (he : ∀ x : R.E, (e' (algebraMap R.E R.E' x) : Q.L) = (e x : Q.L))
    (hj : ∀ x : R.E', j (algebraMap R.E' R.L x) = (e' x : Q.L))
    (hξ : R.ξ = HeckeCharacter.comap e' (Q.mackeyCharacter D a))
    (hv : (finitePlaceEquiv e.symm R.Ps.v).asIdeal.LiesOver Q.Ps.v.asIdeal)
    (hQ : HasUniquePlaceAbove Q.L Q.Ps.v)
    (hParent : ∀ τ : Gal(Q.L/Q.E),
      (∀ z : Q.Lˣ, globalUnitComponent Q.ξ Q.Ps.v'
          (normUnits Q.E' Q.L (Units.map τ.toRingEquiv.toMonoidHom z)) =
        globalUnitComponent Q.ξ Q.Ps.v' (normUnits Q.E' Q.L z)) →
      ∀ x : Q.E', τ (algebraMap Q.E' Q.L x) = algebraMap Q.E' Q.L x)
    (σ : Gal(R.L/R.E)) :
    (∀ z : R.Lˣ, globalUnitComponent R.ξ R.Ps.v'
        (normUnits R.E' R.L (Units.map σ.toRingEquiv.toMonoidHom z)) =
      globalUnitComponent R.ξ R.Ps.v' (normUnits R.E' R.L z)) ↔
    ∀ x : R.E', σ (algebraMap R.E' R.L x) = algebraMap R.E' R.L x := by
  constructor
  swap
  · intro hfix z
    let σ' : Gal(R.L/R.E') := { σ.toRingEquiv with commutes' := hfix }
    exact congrArg (globalUnitComponent R.ξ R.Ps.v')
      (Units.ext (Algebra.norm_eq_of_algEquiv σ' (z : R.L)))
  intro hσ
  let A := Q.conjugateField a
  let C := Q.mackeyField D a
  let k := (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv
  let : Algebra A C := (IntermediateField.inclusion (show A ≤ C from le_sup_right)).toAlgebra
  let : IsScalarTower A C Q.L := .of_algebraMap_eq' rfl
  let : Algebra Q.E R.E := (e.symm.toRingHom.comp (algebraMap Q.E D)).toAlgebra
  let : Algebra R.L Q.L := j.toAlgebra
  let : Algebra R.E Q.L := (j.comp (algebraMap R.E R.L)).toAlgebra
  let : Algebra R.E' Q.L := (j.comp (algebraMap R.E' R.L)).toAlgebra
  let : IsScalarTower R.E R.L Q.L := .of_algebraMap_eq' rfl
  let : IsScalarTower R.E' R.L Q.L := .of_algebraMap_eq' rfl
  have hE (x : R.E) : algebraMap R.E Q.L x = (e x : Q.L) := by
    change j (algebraMap R.E R.L x) = _
    rw [IsScalarTower.algebraMap_apply R.E R.E' R.L, hj, he]
  let : IsScalarTower Q.E R.E Q.L := .of_algebraMap_eq fun x => by
    rw [hE]
    change algebraMap Q.E Q.L x = ((e (e.symm (algebraMap Q.E D x)) : D) : Q.L)
    rw [e.apply_symm_apply]
    rfl
  let : Normal R.E Q.L := Normal.tower_top_of_normal Q.E R.E Q.L
  let τ := σ.liftNormal Q.L
  let τE := τ.restrictScalars Q.E
  have hτ (x : R.L) : τE (j x) = j (σ x) := σ.liftNormal_commutes Q.L x
  have hNormLift (z : Q.Lˣ) :
      normUnits R.L Q.L (Units.map τE.toRingEquiv.toMonoidHom z) =
        Units.map σ.toRingEquiv.toMonoidHom (normUnits R.L Q.L z) :=
    normUnits_map σ.toRingEquiv τE.toRingEquiv (RingHom.ext fun x => (hτ x).symm) z
  let parent (z : Q.Lˣ) := globalUnitComponent Q.ξ Q.Ps.v' (normUnits Q.E' Q.L z)
  let child (z : R.Lˣ) := globalUnitComponent R.ξ R.Ps.v' (normUnits R.E' R.L z)
  have hChar (z : Q.Lˣ) : child (normUnits R.L Q.L z) =
      parent (Units.map a.symm.toRingEquiv.toMonoidHom z) := by
    have heNorm : Units.map e'.toMonoidHom (normUnits R.E' Q.L z) = normUnits C Q.L z :=
      (normUnits_map e' (RingEquiv.refl Q.L) (RingHom.ext fun x => (hj x).symm) z).symm
    have haNorm : Units.map k.symm.toMonoidHom (normUnits A Q.L z) =
        normUnits Q.E' Q.L (Units.map a.symm.toRingEquiv.toMonoidHom z) :=
      (normUnits_map k.symm a.symm.toRingEquiv (RingHom.ext fun x => by
        change algebraMap Q.E' Q.L (k.symm x) = a.symm (x : Q.L)
        apply a.injective
        rw [a.apply_symm_apply]
        exact congrArg (fun x : A => (x : Q.L)) (k.apply_symm_apply x)) z).symm
    change globalUnitComponent R.ξ R.Ps.v' (normUnits R.E' R.L (normUnits R.L Q.L z)) =
      globalUnitComponent Q.ξ Q.Ps.v' (normUnits Q.E' Q.L (Units.map a.symm.toRingEquiv.toMonoidHom z))
    rw [normUnits_tower]
    exact (mackeyUnitComponent Q R D a e e' he hξ hv hQ (normUnits R.E' Q.L z)).trans (by
      rw [heNorm, normUnits_tower]
      exact congrArg (globalUnitComponent Q.ξ Q.Ps.v') haNorm)
  have hLift (z : Q.Lˣ) : parent (Units.map a.symm.toRingEquiv.toMonoidHom
      (Units.map τE.toRingEquiv.toMonoidHom z)) = parent (Units.map a.symm.toRingEquiv.toMonoidHom z) := by
    rw [← hChar, ← hChar, hNormLift]
    exact hσ _
  let γ := (a.trans τE).trans a.symm
  have hγ (z : Q.Lˣ) : parent (Units.map γ.toRingEquiv.toMonoidHom z) = parent z := by
    refine (hLift (Units.map a.toRingEquiv.toMonoidHom z)).trans (congrArg parent ?_)
    exact Units.ext (a.symm_apply_apply (z : Q.L))
  have hfix := hParent γ hγ
  have hA : τE ∈ A.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨x, rfl⟩
    change τE (a (algebraMap Q.E' Q.L x)) = a (algebraMap Q.E' Q.L x)
    have hx := congrArg a (hfix x)
    change a (a.symm (τE (a (algebraMap Q.E' Q.L x)))) = a (algebraMap Q.E' Q.L x) at hx
    simpa only [a.apply_symm_apply] using hx
  have hD : τE ∈ D.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hx := τ.commutes (e.symm ⟨y, hy⟩)
    rw [hE, e.apply_symm_apply] at hx
    exact hx
  have hC : τE ∈ C.fixingSubgroup := by
    change τE ∈ (D ⊔ A).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
    exact ⟨hD, hA⟩
  intro x
  apply j.injective
  rw [← hτ, hj]
  rw [IntermediateField.mem_fixingSubgroup_iff] at hC
  exact hC _ (e' x).property

/-- Harris's exact stabilizer condition passes to every valid auxiliary Mackey child. -/
theorem proposition48ExactStabilizerMackeyInheritance :
    Proposition48ExactStabilizerMackeyInheritanceStatement.{uF} := by
  intro Q R b c D a hQ hChild hR
  obtain ⟨hQrec, _, _, hQnormal, _, hQcompat, hQunique, _, hQexact, _, _, _, hQcomponent⟩ := hQ
  obtain ⟨hRrec, hRsplit, hRtower, hRnormal, hRp, hRcompat, hRunique, hRconj,
    _, hRalg, hRregular, hRinverse, hRcomponent⟩ := hR
  obtain ⟨e, e', j, _, he, hj, _, hξ, _, hv⟩ := hChild
  let : IsNormalClosure Q.E Q.E' Q.L := hQnormal
  let : IsNormalClosure R.E R.E' R.L := hRnormal
  let : Normal Q.E Q.L := IsNormalClosure.normal (K := Q.E')
  let : Normal R.E R.L := IsNormalClosure.normal (K := R.E')
  let : IsGalois Q.E Q.L := ⟨⟩
  let : IsGalois R.E R.L := ⟨⟩
  have hParent := (Q.Ps.exactWeilStabilizer_iff_global hQcompat hQunique Q.e hQrec
    Q.ξ Q.χs hQcomponent).mp hQexact
  have hRexact := (R.Ps.exactWeilStabilizer_iff_global hRcompat hRunique R.e hRrec
    R.ξ R.χs hRcomponent).mpr (mackeyGlobalStabilizer Q R D a e e' j he hj hξ hv hQunique
      (fun τ => (hParent τ).mp))
  exact ⟨hRrec, hRsplit, hRtower, hRnormal, hRp, hRcompat, hRunique, hRconj,
    hRexact, hRalg, hRregular, hRinverse, hRcomponent⟩

end Langlands.Global.Harris
