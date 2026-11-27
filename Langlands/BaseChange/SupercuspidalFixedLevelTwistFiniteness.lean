import Langlands.BaseChange.UnramifiedDeterminant
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.Group.GL.UnramifiedCharacterSupplement
import Langlands.Correspondence.SupercuspidalCompactOpenFinitenessProof
import Langlands.Representation.Smooth.RenardCentralCharacterProof

/-! # Supercuspidal unramified twist orbits at a fixed compact open level -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear
open Henniart.AllFieldCompactOpenFiniteness
open Henniart.CompactOpenFiniteness (IsConstituent exists_ne_zero_of_isConstituent)
open CuspidalSupport (exists_twistIntertwiningMap_of_restrictedHom_nonzero
  twistEquivOfNonzeroIntertwiner)

universe v z

variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The supercuspidals of positive rank visible at a compact open level lie in finitely
many determinant-twist orbits, with the central character allowed to vary. -/
def SupercuspidalFixedLevelTwistFinitenessStatement (n : ℕ)
    (K : OpenSubgroup (GeneralLinear (n + 1) E)) : Prop :=
  IsCompact (K : Set (GeneralLinear (n + 1) E)) →
    ∃ S : Finset (SupercuspidalRep.{v,z} (F := E) (n := n + 1)),
      ∀ A : SupercuspidalRep.{v,z} (F := E) (n := n + 1),
        fixedVectors A.obj.representation K.toSubgroup ≠ ⊥ →
        ∃ B ∈ S, ∃ a : ℂˣ,
          Nonempty (A.obj.representation.Equiv
            (twist ((LocalFieldData.ofInstances E).determinantUnramifiedCharacter (n + 1) a)
              B.obj.representation))

variable (n : ℕ)

private theorem supercuspidal_centralCharacter
    (A : SupercuspidalRep.{v,z} (F := E) (n := n + 1)) :
    ∃ χ : Subgroup.center (GeneralLinear (n + 1) E) →* ℂˣ, A.obj.HasCentralCharacter χ := by
  let G := GeneralLinear (n + 1) E
  let : T2Space G := LocalFieldTopology.generalLinear_t2Space E _
  let : LocallyCompactSpace G := LocalFieldTopology.generalLinear_locallyCompactSpace E _
  let : TotallyDisconnectedSpace G :=
    LocalFieldTopology.generalLinear_totallyDisconnectedSpace E _
  let : SigmaCompactSpace G := LocalFieldTopology.generalLinear_sigmaCompactSpace E _
  exact (Renard.Smooth.centralCharacter.{v,z,z} G (Subgroup.center G) le_rfl).1
    A.obj A.obj.representation A.obj.isSmooth A.property.1

private theorem detTwist_of_common_constituent
    (A B : SupercuspidalRep.{v,z} (F := E) (n := n + 1))
    {c : CompactCoefficientClass.{v,z} (unitGroup E n)}
    (hA : IsConstituent (isSmooth_unitRep E n A.obj) c)
    (hB : IsConstituent (isSmooth_unitRep E n B.obj) c) :
    ∃ a : ℂˣ, Nonempty (A.obj.representation.Equiv
      (twist ((LocalFieldData.ofInstances E).determinantUnramifiedCharacter (n + 1) a)
        B.obj.representation)) := by
  let T := LocalFieldData.ofInstances E
  let D := fullBlock n
  let e := D.singleBlockLeviEquivContinuous rfl E
  let H := unitGroup E n
  let : (H ⊔ Subgroup.center (D.Levi E) : Subgroup (D.Levi E)).FiniteIndex :=
    AllField.CuspidalSupport.determinantUnit_sup_center_finiteIndex T D
  have hcomm : commutator (D.Levi E) ≤ H :=
    Abelianization.commutator_subset_ker (AllField.CuspidalSupport.leviDeterminantNorm T D)
  have hz (P : SupercuspidalRep.{v,z} (F := E) (n := n + 1))
      (x : Subgroup.center (D.Levi E)) : ∃ a : ℂ, ∀ w, leviRep E n P.obj.representation x w = a • w := by
    obtain ⟨ω, hω⟩ := supercuspidal_centralCharacter E n P
    let y : Subgroup.center (GeneralLinear (n + 1) E) :=
      ⟨e x.val, leviEmbedding_mem_center E n x.property⟩
    exact ⟨ω y, hω y⟩
  obtain ⟨f, hf⟩ := exists_ne_zero_of_isConstituent _ _ hB hA
  obtain ⟨χ, hχ, f', hf'⟩ := exists_twistIntertwiningMap_of_restrictedHom_nonzero
    (leviRep E n B.obj.representation) (leviRep E n A.obj.representation)
    H hcomm (hz B) (hz A) f hf
  let Eχ := twistEquivOfNonzeroIntertwiner _ _ (isIrreducible_leviRep E n B.obj B.property.1)
    (isIrreducible_leviRep E n A.obj A.property.1) χ f' hf'
  let ψ := χ.comp e.symm.toMonoidHom
  have hψ : IsUnramifiedCharacter ψ := by
    intro K hK k hk
    apply MonoidHom.mem_ker.mp
    apply hχ
    apply (AllField.CuspidalSupport.mem_determinantUnitSubgroup T D _).mpr
    intro i
    let p := (Pi.evalMonoidHom (fun j => GeneralLinear (D.size j) E) i).comp e.symm.toMonoidHom
    exact T.determinantNorm_eq_one_of_mem_compact (D.size i) (K.map p)
      (hK.image ((continuous_apply i).comp e.symm.continuous)) _ ⟨k, hk, rfl⟩
  have hmodel : A.obj.representation.Equiv (twist ψ B.obj.representation) :=
    Representation.Equiv.mk Eχ.symm.toLinearEquiv (fun g => by
      have h := Eχ.symm.isIntertwining' (e.symm g)
      change Eχ.symm.toLinearMap ∘ₗ A.obj.representation (e (e.symm g)) =
        ((χ (e.symm g) : ℂ) • B.obj.representation (e (e.symm g))) ∘ₗ Eχ.symm.toLinearMap at h
      change Eχ.symm.toLinearMap ∘ₗ A.obj.representation g =
        ((χ (e.symm g) : ℂ) • B.obj.representation g) ∘ₗ Eχ.symm.toLinearMap
      simpa only [ContinuousMulEquiv.apply_symm_apply] using h)
  let d := Iwasawa.diagonalUnits (Pi.mulSingle (0 : Fin (n + 1)) T.uniformizerUnit)
  refine ⟨ψ d, ⟨?_⟩⟩
  rw [show T.determinantUnramifiedCharacter (n + 1) (ψ d) = ψ from
    (eq_detOrderCharacter_of_isUnramified E 0 ψ hψ).symm]
  exact hmodel

/-- The finite coefficient stratum of the determinant-unit subgroup detects the
unramified twist orbits of all visible supercuspidals. -/
theorem supercuspidalFixedLevelTwistFiniteness
    (K : OpenSubgroup (GeneralLinear (n + 1) E)) :
    SupercuspidalFixedLevelTwistFinitenessStatement.{v,z} E n K := by
  classical
  intro hK
  let L := unitLevel E n K
  have hL := isCompact_unitLevel E n K hK
  let S := CompactCoefficientClass.fixedStratum.{v,z} L.toSubgroup
  have hfin : S.Finite :=
    AllField.CuspidalSupport.compactCoefficientFixedLevelFiniteness E
      (LocalFieldData.ofInstances E) (n + 1) (Nat.succ_pos n) (fullBlock n) L hL
  let : Finite ↥S := hfin.to_subtype
  let I := {c : S // ∃ A : SupercuspidalRep.{v,z} (F := E) (n := n + 1),
    IsConstituent (isSmooth_unitRep E n A.obj) c.val}
  let : Fintype I := Fintype.ofFinite I
  let R (i : I) := i.property.choose
  refine ⟨Finset.univ.image R, ?_⟩
  intro A hA
  obtain ⟨χ, hχ⟩ := supercuspidal_centralCharacter E n A
  obtain ⟨c, hc, hAc⟩ := Henniart.AllFieldCompactOpenFiniteness.exists_isConstituent
    E n χ A hχ L hL (fixedVectors_unitRep_ne_bot E n A.obj K hA)
  let i : I := ⟨⟨c, hc⟩, A, hAc⟩
  exact ⟨R i, Finset.mem_image_of_mem R (Finset.mem_univ i),
    detTwist_of_common_constituent E n A (R i) hAc i.property.choose_spec⟩

end Langlands.BaseChange
