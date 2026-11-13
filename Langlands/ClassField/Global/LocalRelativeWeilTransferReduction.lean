import Langlands.ClassField.Global.LocalRelativeWeilTransferStatement
import Langlands.GroupTheory.TransferDoubleCoset
import Langlands.ClassField.Global.IdeleLocalInjectivity
import Langlands.ClassField.Global.IdeleGaloisDescentProof
import Langlands.ClassField.Global.IdeleArchimedean
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.ClassField.Global.IdeleClassPlaceProduct
import Langlands.ClassFieldTheory.Local.WeilTransferReciprocityStatement
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionStatement

/-! # Reduction of local transfer reciprocity to the local transfer square

For a local map `ι : W_{F_z} → W_{E/F}` at `w | z`, the transfer `W_{E/F} → C_F` of
`ι g` is computed from the local transfer `W_{F_z} → W_{E_w}^{ab}` read through the
reciprocity candidate of `E_w`. -/

noncomputable section

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.GroupTheory.Transfer FundamentalClass

universe u

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
  (z : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver z.asIdeal]

section LocalRestriction

/-- The closure `\bar{F_z}` as an `E_w`-algebra through `completionClosureEmbedding`. -/
abbrev closureAlgebra : Algebra (w.adicCompletion E) (AlgebraicClosure (z.adicCompletion F)) :=
  (completionClosureEmbedding z w).toAlgebra

omit [IsGalois F E] in
theorem closureAlgebra_isScalarTower :
    letI := closureAlgebra z w
    IsScalarTower (z.adicCompletion F) (w.adicCompletion E)
      (AlgebraicClosure (z.adicCompletion F)) :=
  letI := closureAlgebra z w
  IsScalarTower.of_algebraMap_eq fun x => (completionClosureEmbedding_algebraMap z w x).symm

/-- The restriction to `E_w` of the Galois image of an element of `W_{F_z}`. -/
def localRestriction (g : Weil.Local.localWeilGroup (padicField z)) :
    w.adicCompletion E ≃ₐ[z.adicCompletion F] w.adicCompletion E :=
  letI := closureAlgebra z w
  haveI := closureAlgebra_isScalarTower z w
  haveI := isGalois_adicCompletion z w
  AlgEquiv.restrictNormal (Weil.Local.localProjection (padicField z) g) (w.adicCompletion E)

theorem completionClosureEmbedding_localRestriction
    (g : Weil.Local.localWeilGroup (padicField z)) (y : w.adicCompletion E) :
    completionClosureEmbedding z w (localRestriction z w g y) =
      AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) g)
        (completionClosureEmbedding z w y) := by
  let := closureAlgebra z w
  have := closureAlgebra_isScalarTower z w
  have := isGalois_adicCompletion z w
  exact AlgEquiv.restrictNormal_commutes _ (w.adicCompletion E) y

variable {z w}

/-- The Galois part of a local map: the image of `ι g` in `Gal(E/F)` is the image of the
restriction of `g` to `E_w`. -/
theorem projection_eq_decompositionHom
    {e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w)}
    {ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E}
    (hι : IsLocalRelativeWeilMap z w e ι) (g : Weil.Local.localWeilGroup (padicField z)) :
    projection c F E (ι g) = decompositionHom z w (localRestriction z w g) := by
  apply AlgEquiv.ext
  intro a
  apply (algebraMap E (w.adicCompletion E)).injective
  apply (completionClosureEmbedding z w).injective
  rw [algebraMap_decompositionHom, completionClosureEmbedding_localRestriction, hι.2.1 g a]

end LocalRestriction

section Preimage

variable {z w}
variable {e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w)}
  {ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E}

/-- The elements of `W_{F_z}` sent into `C_E` by a local map are exactly the image of
`W_{E_w}`. -/
theorem comap_ideleClassSubgroup_eq (hι : IsLocalRelativeWeilMap z w e ι) :
    (ideleClassSubgroup c F E).comap ι.toMonoidHom =
      (completionWeilMap z w).toMonoidHom.range := by
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · intro hx
    have h1 : projection c F E (ι x) = 1 := by
      rw [ideleClassSubgroup, exact] at hx
      exact hx
    rw [projection_eq_decompositionHom hι, ← map_one (decompositionHom z w)] at h1
    have h2 := decompositionHom_injective z w h1
    rw [completionWeilMap, Weil.Local.extensionWeilMap_range, Subgroup.mem_comap,
      Weil.Local.extensionGaloisMap_range]
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr ?_
    intro y hy
    obtain ⟨b, rfl⟩ := (Weil.Local.mem_extensionIntermediateField _ _ _ y).mp hy
    have h3 := completionClosureEmbedding_localRestriction z w x b
    rw [h2, AlgEquiv.one_apply] at h3
    exact h3.symm
  · rintro ⟨y, rfl⟩
    change ι (completionWeilMap z w y) ∈ ideleClassSubgroup c F E
    rw [hι.2.2 y]
    exact inv_mem ⟨_, rfl⟩

/-- The kernel of `W_{F_z} → W_{E/F} → Gal(E/F)` is the image of `W_{E_w}`. -/
theorem ker_projection_comp_eq (hι : IsLocalRelativeWeilMap z w e ι) :
    ((projection c F E).comp ι.toMonoidHom).ker = (completionWeilMap z w).toMonoidHom.range := by
  rw [← comap_ideleClassSubgroup_eq hι, ideleClassSubgroup, exact, MonoidHom.comap_ker]

end Preimage

section Image

/-- The decomposition group `D_w ⊆ Gal(E/F)` has order `[E_w : F_z]`. -/
theorem card_range_decompositionHom :
    Nat.card (decompositionHom z w).range =
      Weil.Local.extensionDegree (padicField z) (towerPadicField z w)
        (completionPadicAlgHom z w) := by
  have := isGalois_adicCompletion z w
  rw [← Nat.card_congr (MonoidHom.ofInjective (decompositionHom_injective z w)).toEquiv,
    IsGalois.card_aut_eq_finrank]
  rfl

variable {z w}
variable {e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w)}
  {ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E}

/-- The image of `W_{F_z}` in `Gal(E/F)` is the decomposition group `D_w`. -/
theorem range_projection_comp_eq (hι : IsLocalRelativeWeilMap z w e ι) :
    ((projection c F E).comp ι.toMonoidHom).range = (decompositionHom z w).range := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨g, rfl⟩
    exact ⟨localRestriction z w g, (projection_eq_decompositionHom hι g).symm⟩
  · rw [← Subgroup.index_ker ((projection c F E).comp ι.toMonoidHom), ker_projection_comp_eq hι, card_range_decompositionHom,
      completionWeilMap, Weil.Local.extensionWeilMap_range_index]

end Image

section Transfer

/-- The transfer of a homomorphism restricted along an equality of subgroups is unchanged. -/
theorem transfer_comp_inclusion_of_eq {G A : Type*} [Group G] [CommGroup A]
    {K R : Subgroup G} (h : K = R) [K.FiniteIndex] [R.FiniteIndex] (ϕ : R →* A) (g : G) :
    MonoidHom.transfer (ϕ.comp (Subgroup.inclusion h.le)) g = MonoidHom.transfer ϕ g := by
  subst h
  rfl

/-- Local reciprocity of `E_w` on the image of `W_{E_w}` in `W_{F_z}`: the homomorphism
whose transfer appears in the local transfer square. -/
def rangeReciprocity (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w)) :
    (completionWeilMap z w).toMonoidHom.range →* (w.adicCompletion E)ˣ :=
  letI := (towerPadicField z w).canonicalTopologicalData.topology
  (LocalFactor.RankOne.reciprocityUnits (towerPadicField z w) e).toMonoidHom.comp
    (InductionAlong.rangeInverse (completionWeilMap z w).toMonoidHom
      (Weil.Local.extensionWeilMap_injective _ _ _))

omit [IsGalois F E] in
theorem rangeReciprocity_apply
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w))
    (y : Weil.Local.localWeilGroup (towerPadicField z w))
    (hy : (completionWeilMap z w).toMonoidHom y ∈ (completionWeilMap z w).toMonoidHom.range) :
    rangeReciprocity z w e ⟨(completionWeilMap z w).toMonoidHom y, hy⟩ =
      LocalFactor.RankOne.reciprocityUnits (towerPadicField z w) e y := by
  let :=(towerPadicField z w).canonicalTopologicalData.topology
  change (LocalFactor.RankOne.reciprocityUnits (towerPadicField z w) e).toMonoidHom
    (InductionAlong.rangeInverse (completionWeilMap z w).toMonoidHom
      (Weil.Local.extensionWeilMap_injective _ _ _) ⟨_, y, rfl⟩) = _
  rw [InductionAlong.rangeInverse_apply]
  rfl

section

attribute [local instance] relativeIdeleClassAction relativeGaloisTopology

variable (c F E) in
/-- The identification of the idele-class subgroup of `W_{E/F}` with `C_E`, as the
homomorphism used in `ideleTransfer`. -/
abbrev ideleClassSubgroupHom : ideleClassSubgroup c F E →* IdeleClassGroup (𝓞 E) E :=
  (ideleClassSubgroupEquiv c F E).toMulEquiv.toMonoidHom

end

variable (F E) in
/-- `a ↦ σ(a)⁻¹` from `E_wˣ` to `C_E`, through the idele class supported at `w`. -/
def conjugateInvClass (σ : E ≃ₐ[F] E) : (w.adicCompletion E)ˣ →* IdeleClassGroup (𝓞 E) E where
  toFun a := (relativeIdeleClassAut F E σ (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w a))⁻¹
  map_one' := by rw [map_one, map_one, inv_one]
  map_mul' a b := by
    rw [map_mul, map_mul]
    exact mul_inv (relativeIdeleClassAut F E σ (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w a))
      (relativeIdeleClassAut F E σ (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w b))

omit [NumberField F] [IsGalois F E] in
theorem conjugateInvClass_apply (σ : E ≃ₐ[F] E) (a : (w.adicCompletion E)ˣ) :
    conjugateInvClass F E w σ a =
      (relativeIdeleClassAut F E σ (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w a))⁻¹ :=
  rfl

variable {z w}
variable {e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w)}
  {ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E}

/-- On the preimage of `C_E`, the homomorphism `ψ ∘ conjInv v ∘ ι` is local reciprocity of
`E_w` followed by `a ↦ σ(a)⁻¹` with `σ` the image of `v⁻¹` in `Gal(E/F)`. -/
theorem comp_conjInv_comp_subgroupComap (hι : IsLocalRelativeWeilMap z w e ι)
    (v : RelativeWeilGroup c F E) :
    ((ideleClassSubgroupHom c F E).comp (conjInv v)).comp
        (ι.toMonoidHom.subgroupComap (ideleClassSubgroup c F E)) =
      ((conjugateInvClass F E w (projection c F E v⁻¹)).comp (rangeReciprocity z w e)).comp
        (Subgroup.inclusion (comap_ideleClassSubgroup_eq hι).le) := by
  refine MonoidHom.ext fun ⟨k, hk⟩ => ?_
  have hk' : k ∈ (completionWeilMap z w).toMonoidHom.range := comap_ideleClassSubgroup_eq hι ▸ hk
  obtain ⟨y, rfl⟩ := hk'
  set r := LocalFactor.RankOne.reciprocityUnits (towerPadicField z w) e y
  have hx : conjInv v (ι.toMonoidHom.subgroupComap (ideleClassSubgroup c F E) ⟨_, hk⟩) =
      ⟨inclusion c F E (conjugateInvClass F E w (projection c F E v⁻¹) r), _, rfl⟩ := by
    apply Subtype.ext
    rw [coe_conjInv]
    change v⁻¹ * ι (completionWeilMap z w y) * v = _
    rw [hι.2.2 y]
    calc v⁻¹ * (inclusion c F E (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w r))⁻¹ * v
        = (v⁻¹ * inclusion c F E (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w r) * v⁻¹⁻¹)⁻¹ := by
          group
      _ = (inclusion c F E (ideleClassEquiv (projection c F E v⁻¹).toRingEquiv
            (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w r)))⁻¹ := by
          rw [conjugation]
      _ = inclusion c F E (ideleClassEquiv (projection c F E v⁻¹).toRingEquiv
            (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w r))⁻¹ :=
          (map_inv (inclusion c F E) _).symm
      _ = inclusion c F E (conjugateInvClass F E w (projection c F E v⁻¹) r) := rfl
  simp only [MonoidHom.comp_apply]
  rw [hx]
  refine (ideleClassSubgroupEquiv_inclusion c F E _).trans ?_
  exact congrArg (conjugateInvClass F E w (projection c F E v⁻¹))
    (rangeReciprocity_apply z w e y _).symm

/-- The transfer of the conjugated homomorphism of `comp_conjInv_comp_subgroupComap`. -/
theorem transfer_comp_conjInv_comp_subgroupComap (hι : IsLocalRelativeWeilMap z w e ι)
    (v : RelativeWeilGroup c F E) (y : Weil.Local.localWeilGroup (padicField z)) :
    MonoidHom.transfer (((ideleClassSubgroupHom c F E).comp
        (conjInv v)).comp (ι.toMonoidHom.subgroupComap (ideleClassSubgroup c F E))) y =
      conjugateInvClass F E w (projection c F E v⁻¹)
        (MonoidHom.transfer (rangeReciprocity z w e) y) := by
  rw [comp_conjInv_comp_subgroupComap hι v,
    transfer_comp_inclusion_of_eq (comap_ideleClassSubgroup_eq hι), transfer_comp]

/-- Reduction of local transfer reciprocity: if the local transfer of `E_w`-reciprocity at
`y` is the image of `a ∈ F_zˣ` in `E_wˣ`, then the transfer `W_{E/F} → C_E` of `ι y` is the
inverse of the image of `a` under `F_zˣ → C_F → C_E`. -/
theorem ideleTransfer_eq_of_transfer_rangeReciprocity (hι : IsLocalRelativeWeilMap z w e ι)
    (a : (z.adicCompletion F)ˣ) (y : Weil.Local.localWeilGroup (padicField z))
    (hy : MonoidHom.transfer (rangeReciprocity z w e) y =
      Units.map (FiniteExtension.completionMap z w).toMonoidHom a) :
    ideleTransfer c F E (ι y) =
      (ideleClassInclusion (IdeleClassGroup.ofAdicCompletion (𝓞 F) F z a))⁻¹ := by
  classical
  let _ : Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom z w).range) := Fintype.ofFinite _
  let σ : (E ≃ₐ[F] E) ⧸ (decompositionHom z w).range → E ≃ₐ[F] E := fun i => Quotient.out i
  have ht : ∀ i, ∃ t, projection c F E t = (σ i)⁻¹ := fun i => projection_surjective c F E _
  choose t ht using ht
  have hH : ∀ x, x ∈ ideleClassSubgroup c F E ↔ projection c F E x = 1 := by
    intro x
    rw [ideleClassSubgroup, exact, MonoidHom.mem_ker]
  have hD := range_projection_comp_eq hι
  have hcover : ∀ g, ∃ i l, ∃ h ∈ ideleClassSubgroup c F E,
      g = ι.toMonoidHom l * t i * h := by
    intro g
    let i : (E ≃ₐ[F] E) ⧸ (decompositionHom z w).range := QuotientGroup.mk (projection c F E g)⁻¹
    have hi : (σ i)⁻¹ * (projection c F E g)⁻¹ ∈ (decompositionHom z w).range :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' i)
    have hi' : projection c F E g * σ i ∈ ((projection c F E).comp ι.toMonoidHom).range := by
      rw [hD]
      have := inv_mem hi
      rwa [mul_inv_rev, inv_inv, inv_inv] at this
    obtain ⟨l, hl⟩ := hi'
    refine ⟨i, l, (ι.toMonoidHom l * t i)⁻¹ * g, ?_, by group⟩
    rw [hH, map_mul, map_inv, map_mul, ht i]
    change (projection c F E (ι l) * (σ i)⁻¹)⁻¹ * projection c F E g = 1
    rw [show projection c F E (ι l) = projection c F E g * σ i from hl]
    group
  have hdisj : ∀ i j l, ∀ h ∈ ideleClassSubgroup c F E,
      t j = ι.toMonoidHom l * t i * h → i = j := by
    intro i j l h hh hj
    have h1 := congrArg (projection c F E) hj
    rw [map_mul, map_mul, ht, ht, (hH h).mp hh, mul_one] at h1
    have h2 : projection c F E (ι.toMonoidHom l) ∈ (decompositionHom z w).range := by
      rw [← hD]
      exact ⟨l, rfl⟩
    rw [← QuotientGroup.out_eq' i, ← QuotientGroup.out_eq' j]
    refine QuotientGroup.eq.mpr ?_
    have h3 : (σ i)⁻¹ * σ j = (projection c F E (ι.toMonoidHom l))⁻¹ := by
      rw [← inv_inv (σ j), h1]
      group
    change (σ i)⁻¹ * σ j ∈ (decompositionHom z w).range
    rw [h3]
    exact inv_mem h2
  have hσ : ∀ τ : E ≃ₐ[F] E, ∃! i, (σ i)⁻¹ * τ ∈ (decompositionHom z w).range := by
    intro τ
    refine ⟨QuotientGroup.mk τ, QuotientGroup.eq.mp (QuotientGroup.out_eq' _), fun j hj => ?_⟩
    rw [← QuotientGroup.out_eq' j]
    exact QuotientGroup.eq.mpr hj
  rw [ideleTransfer_apply]
  refine (transfer_comp_eq_prod_of_normal (H := ideleClassSubgroup c F E)
    (ψ := ι.toMonoidHom) (t := t) _ hcover hdisj y).trans ?_
  calc _ = ∏ i, (relativeIdeleClassAut F E (σ i) (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w
          (Units.map (FiniteExtension.completionMap z w).toMonoidHom a)))⁻¹ := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [transfer_comp_conjInv_comp_subgroupComap hι, hy, map_inv (projection c F E), ht,
          inv_inv]
        rfl
    _ = _ := by
        rw [Finset.prod_inv_distrib, prod_relativeIdeleClassAut_ofAdicCompletion_of_coset z w σ hσ a]

end Transfer

/-- Local transfer reciprocity follows from the local transfer square for embeddings of
p-adic fields. -/
theorem localTransferReciprocity_of_square
    (hsq : LocalClassField.ExtensionWeilTransferReciprocityStatement.{u, u}) :
    LocalTransferReciprocityStatement.{u} := by
  intro c F E _ _ _ _ _ _ z w _ e ι hι ez hez g
  refine (eq_transfer_of_ideleClassInclusion_eq c F E ?_).symm
  rw [map_inv]
  refine (ideleTransfer_eq_of_transfer_rangeReciprocity hι _ g ?_).symm
  exact hsq (residuePrime z) (padicField z) (towerPadicField z w) (completionPadicAlgHom z w)
    ez e hez hι.1 g

end Langlands.ClassField.Global.RelativeWeilGroup
