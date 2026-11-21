import Langlands.Automorphic.Unramified.CyclicTransferStatement
import Langlands.ClassField.Global.FundamentalClassProof
import Langlands.ClassField.Global.IdeleClassBaseImage
import Langlands.ClassField.Global.LocalRelativeWeilMapExistenceProof
import Langlands.ClassField.Global.LocalRelativeWeilTransferProof
import Langlands.ClassField.Global.RelativeWeilTransferReciprocityProof
import Langlands.ClassField.Global.RelativeWeilUnramifiedTransfer
import Langlands.ClassFieldTheory.Local.CommonClosureReciprocityConstruction
import Langlands.ClassFieldTheory.Local.LocalRelativeClassFormationProof
import Langlands.Correspondence.AssemblyLTwistedSupercuspidal
import Langlands.Global.AdelicFunctoriality.IdeleClassNormTowerProof
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Finite local norm kernels of cyclic norm-kernel Hecke characters -/

noncomputable section

universe u uF uE

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicFunctoriality

open NumberField ClassField.Global ClassField.Global.RelativeWeilGroup
open ClassFieldTheory.Local CompletionPadic LocalClassField
open scoped NumberField FiniteExtension

/-- If the class of a one-place idele is a global norm, its coordinate is a local
norm. The relative Weil groups used here have their base and extension in a
common universe. -/
private theorem mem_localNorm_of_finiteClassInclusion_sameUniverse
    {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    (v : FinitePlace F) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]
    (a : (FiniteCompletion F v)ˣ)
    (ha : finiteClassInclusion F v a ∈ (ideleClassNorm (K := F) (L := E)).toMonoidHom.range) :
    a ∈ (FiniteExtension.localUnitNorm v w).toMonoidHom.range := by
  choose I hI using localRelativeClassFormation.{u}
  have hI' : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization :=
    fun p _ => ⟨(hI p).2.1, (hI p).1⟩
  obtain ⟨c, hc⟩ := fundamentalClass_exists I hI'
  obtain ⟨_, hker⟩ := relativeWeilTransferReciprocity I hI' c hc F E
  have hle : (transfer c F E).ker ≤ (projection c F E).ker :=
    hker.le.trans (Abelianization.commutator_subset_ker (projection c F E))
  let e := canonicalStandaloneReciprocity (towerPadicField v w)
  let ev := canonicalStandaloneReciprocity (padicField v)
  obtain ⟨ι, hι⟩ := localRelativeWeilMapExistence I hI' c hc F E v w e
    (canonicalStandaloneReciprocity_geometric _)
  obtain ⟨g, hg⟩ := Correspondence.reciprocityUnits_surjective (padicField v) ev a
  have ht := localTransferReciprocity c F E v w e ι hι ev
    (canonicalStandaloneReciprocity_geometric _) g
  rw [hg] at ht
  have himage : transfer c F E (ι g) ∈ (ideleClassNorm (K := F) (L := E)).toMonoidHom.range := by
    rw [ht]
    exact inv_mem ha
  obtain ⟨x, hx⟩ := himage
  have hproj : g ∈ ((projection c F E).comp ι.toMonoidHom).ker := by
    change projection c F E (ι g) = 1
    have hk : ι g * (inclusion c F E x)⁻¹ ∈ (transfer c F E).ker := by
      change transfer c F E (ι g * (inclusion c F E x)⁻¹) = 1
      change ideleClassNorm (K := F) (L := E) x = transfer c F E (ι g) at hx
      rw [map_mul, map_inv, transfer_inclusion, hx, mul_inv_cancel]
    have hinc : inclusion c F E x ∈ (projection c F E).ker :=
      RelativeWeilGroup.exact c F E ▸ ⟨x, rfl⟩
    change projection c F E (inclusion c F E x) = 1 at hinc
    have heq := hle hk
    change projection c F E (ι g * (inclusion c F E x)⁻¹) = 1 at heq
    simpa only [map_mul, map_inv, hinc, inv_one, mul_one] using heq
  rw [ker_projection_comp_eq hι] at hproj
  obtain ⟨y, rfl⟩ := hproj
  change transfer c F E (ι (completionWeilMap v w y)) = _ at ht
  rw [hι.2.2 y, map_inv, transfer_inclusion,
    ideleClassNorm_ofAdicCompletion v ⟨w, inferInstance⟩] at ht
  exact ⟨_, ofAdicCompletion_injective v (inv_injective ht)⟩

private theorem ideleClassNorm_finiteClassInclusion
    {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : FinitePlace F) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]
    (b : (FiniteCompletion E w)ˣ) :
    ideleClassNorm (K := F) (L := E) (finiteClassInclusion E w b) =
      finiteClassInclusion F v (FiniteExtension.localUnitNorm v w b) := by
  change ideleClassNorm (K := F) (L := E) (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w b) =
    IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (FiniteExtension.localUnitNorm v w b)
  exact ideleClassNorm_ofAdicCompletion (K := F) (L := E) v ⟨w, inferInstance⟩ b

/-- At a finite place of a cyclic number-field extension, the preimage of the
global idele-class norm range is the local norm range at each place above it. -/
def CyclicFiniteLocalNormImageStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    (v : FinitePlace F) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal],
    (ideleClassNorm (K := F) (L := E)).toMonoidHom.range.comap
        (finiteClassInclusion F v).toMonoidHom =
      (FiniteExtension.localUnitNorm v w).toMonoidHom.range

set_option maxHeartbeats 800000 in
theorem cyclicFiniteLocalNormImage : CyclicFiniteLocalNormImageStatement.{uF, uE} := by
  intro F E _ _ _ _ _ _ _ v w _
  ext a
  change finiteClassInclusion F v a ∈ (ideleClassNorm (K := F) (L := E)).toMonoidHom.range ↔
    a ∈ (FiniteExtension.localUnitNorm v w).toMonoidHom.range
  constructor
  · rintro ⟨x, hx⟩
    let B := (⊥ : IntermediateField F E)
    let : IsCyclic (E ≃ₐ[B] E) := (baseImageAutEquiv F E).isCyclic.mp inferInstance
    let q : FinitePlace B := w.under (𝓞 B)
    let : w.asIdeal.LiesOver q.asIdeal := inferInstance
    let : q.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.tower_bot w.asIdeal _ _
    have hglobalDegree : Module.finrank F B = 1 := IntermediateField.finrank_bot
    have hlocalDegree : Module.finrank (FiniteCompletion F v) (FiniteCompletion B q) = 1 :=
      Nat.dvd_one.mp (hglobalDegree ▸ localDegree_dvd v q)
    have hnormInjective : Function.Injective (ideleClassNorm (K := F) (L := B)) := by
      let : Fintype (B ≃ₐ[F] B) := Fintype.ofFinite _
      let : Subsingleton (B ≃ₐ[F] B) := Fintype.card_le_one_iff_subsingleton.mp (by
        rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hglobalDegree])
      have hleft : Function.LeftInverse (ideleClassInclusion (K := F) (L := B))
          (ideleClassNorm (K := F) (L := B)) := by
        intro z
        rw [ideleClassNormGaloisProduct F B, Fintype.prod_subsingleton _ 1, map_one]
        rfl
      exact hleft.injective
    let a' := Units.map (algebraMap (FiniteCompletion F v) (FiniteCompletion B q)).toMonoidHom a
    have ha' : FiniteExtension.localUnitNorm v q a' = a := by
      apply Units.ext
      change Algebra.norm (FiniteCompletion F v) (algebraMap _ (FiniteCompletion B q)
        (a : FiniteCompletion F v)) = (a : FiniteCompletion F v)
      rw [Algebra.norm_algebraMap, hlocalDegree, pow_one]
    have hclass : ideleClassNorm (K := F) (L := B) (finiteClassInclusion B q a') =
        finiteClassInclusion F v a := by
      rw [ideleClassNorm_finiteClassInclusion v q, ha']
    have hmem : finiteClassInclusion B q a' ∈
        (ideleClassNorm (K := B) (L := E)).toMonoidHom.range :=
      ⟨x, hnormInjective ((ideleClassNormTower F B E x).symm.trans (hx.trans hclass.symm))⟩
    obtain ⟨y, hy⟩ := mem_localNorm_of_finiteClassInclusion_sameUniverse q w a' hmem
    change FiniteExtension.localUnitNorm q w y = a' at hy
    refine ⟨y, ofAdicCompletion_injective v ?_⟩
    change finiteClassInclusion F v (FiniteExtension.localUnitNorm v w y) =
      finiteClassInclusion F v a
    calc
      _ = ideleClassNorm (K := F) (L := E) (finiteClassInclusion E w y) :=
        (ideleClassNorm_finiteClassInclusion v w y).symm
      _ = ideleClassNorm (K := F) (L := B)
          (ideleClassNorm (K := B) (L := E) (finiteClassInclusion E w y)) :=
        ideleClassNormTower F B E _
      _ = finiteClassInclusion F v a := by
        rw [ideleClassNorm_finiteClassInclusion q w, hy]
        exact hclass
  · rintro ⟨y, rfl⟩
    exact ⟨finiteClassInclusion E w y, ideleClassNorm_finiteClassInclusion v w y⟩

end Langlands.Global.AdelicFunctoriality

namespace Langlands.Global.HeckeCharacter

open AdelicFunctoriality
open scoped FiniteExtension

/-- A cyclic norm-kernel Hecke character restricts to the actual local norm
kernel at every finite place. -/
theorem finiteComponent_ker_eq_localNorm
    {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    (v : FinitePlace F) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]
    {χ : HeckeCharacter F} (hχ : χ.HasNormKernel E) :
    (χ.finiteComponent v).toMonoidHom.ker =
      (FiniteExtension.localUnitNorm v w).toMonoidHom.range := by
  rw [← cyclicFiniteLocalNormImage F E v w]
  ext a
  exact hχ (finiteClassInclusion F v a)

end Langlands.Global.HeckeCharacter
