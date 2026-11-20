import Langlands.Global.Arithmetic.HarrisMackeyGeneralPosition
import Langlands.ClassFieldTheory.Local.CommonClosureReciprocityConstruction
import Langlands.ClassFieldTheory.Local.Norms
import Langlands.ClassFieldTheory.Local.ReciprocitySystemUniquenessProof

/-! # Normalized reciprocity in the child's algebraic closure -/

noncomputable section

universe uF

namespace Langlands.Global.GeneralPosition

open LocalFactor.CommonClosure LocalClassField Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T U : Extension F)
  (C : Extension (T.asPadicField (p := p)))

local notation "TP" => T.asPadicField (p := p)
local notation "UP" => U.asPadicField (p := p)

private abbrev childPadic : PadicField.{uF} p := @FiniteIntermediateExtension.asPadicField
  (TP).Carrier (TP).field p _ (TP).algebra (TP).finiteDimensional C

local notation "CP" => childPadic F T C
local notation "j" => intermediateWeilMap F T
local notation "k" => intermediateClosureEquiv F T

variable (f : C.field ≃+* U.field)
  (hf : ∀ x : C.field, (f x : AlgebraicClosure F.Carrier) =
    intermediateClosureEquiv F T (x : AlgebraicClosure T.field))

include hf in
/-- Membership in the two copies of the inducing field agrees in the actual closures. -/
theorem mem_embeddedField (x : AlgebraicClosure T.field) :
    k x ∈ U.field ↔ x ∈ C.field := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := f.surjective ⟨k x, h⟩
    have hy' : k (y : AlgebraicClosure T.field) = k x :=
      (hf y).symm.trans (congrArg Subtype.val hy)
    exact (k).injective hy' ▸ y.2
  · intro h
    exact hf ⟨x, h⟩ ▸ (f ⟨x, h⟩).2

include hf in
/-- The inducing Weil subgroup is carried into the actual parent Weil group. -/
theorem embeddedWeil_mem (w : localWeilGroup TP) :
    w ∈ weilSubgroup TP C ↔ j w ∈ weilSubgroup F U := by
  change localProjection TP w ∈ C.field.fixingSubgroup ↔
    localProjection F (j w) ∈ U.field.fixingSubgroup
  rw [localProjection_intermediateWeilMap]
  refine (IntermediateField.mem_fixingSubgroup_iff C.field _).trans
    (Iff.trans ?_ (IntermediateField.mem_fixingSubgroup_iff U.field _).symm)
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := (k).surjective y
    exact (intermediateClosureEquiv_galoisMap F T (localProjection TP w) x).trans
      (congrArg k (h x ((mem_embeddedField F T U C f hf x).mp hy)))
  · intro h x hx
    apply (k).injective
    exact (intermediateClosureEquiv_galoisMap F T (localProjection TP w) x).symm.trans
      (h _ ((mem_embeddedField F T U C f hf x).mpr hx))

private theorem eq_constructed (e : ReciprocityFamily F) (he : NormalizedReciprocity F e) :
    e = LocalClassField.CommonClosure.constructedReciprocityFamily F :=
  ReciprocitySystemUniqueness.eq_of_norm_normalization F.canonicalTopologicalData he.1.1
    (LocalClassField.CommonClosure.constructedReciprocityFamily_norm F) he.2
    (LocalClassField.CommonClosure.constructedReciprocityFamily_normalization F _)
    (ReciprocitySystemUniqueness.weilGaloisAbelianProjection_injective F)

private def embeddedPadicEquiv :
    letI := (CP).algebra
    letI := (UP).algebra
    C.field ≃ₐ[Padic p] U.field := by
  letI := (CP).algebra
  letI := (UP).algebra
  refine AlgEquiv.ofRingEquiv (f := f) fun x => Subtype.ext ?_
  rw [hf]
  exact intermediateClosureEquiv_algebraMap F T (algebraMap (Padic p) T.field x)

include hf in
set_option maxHeartbeats 600000 in
/-- Normalized reciprocity commutes with the given inclusion of closure coordinates. -/
theorem reciprocityUnits_embedded (eF : ReciprocityFamily F) (hF : NormalizedReciprocity F eF)
    (eT : ReciprocityFamily TP) (hT : NormalizedReciprocity TP eT)
    (w : weilSubgroup TP C) (v : weilSubgroup F U) (hv : (v : localWeilGroup F) = j w) :
    reciprocityUnits F eF U v = Units.map f.toMonoidHom (reciprocityUnits TP eT C w) := by
  rw [eq_constructed F eF hF, eq_constructed TP eT hT]
  let : Algebra (Padic p) C.field := (CP).algebra
  let : Algebra (Padic p) U.field := (UP).algebra
  let g := (embeddedPadicEquiv F T U C f hf).symm
  let eC := intermediateClosureEquiv TP C
  let eU := intermediateClosureEquiv F U
  let θ : AlgebraicClosure U.field ≃+* AlgebraicClosure C.field :=
    (eU.toRingEquiv.trans (k).symm.toRingEquiv).trans eC.symm.toRingEquiv
  have hθ' (x : AlgebraicClosure U.field) : k (eC (θ x)) = eU x := by
    change k (eC (eC.symm ((k).symm (eU x)))) = _
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have hθ (x : U.field) : θ (algebraMap U.field _ x) = algebraMap C.field _ (g x) := by
    apply eC.injective
    apply (k).injective
    have hg : (g x : C.field) = f.symm x := rfl
    calc
      k (eC (θ (algebraMap U.field _ x))) = eU (algebraMap U.field _ x) := hθ' _
      _ = (x : AlgebraicClosure F.Carrier) := intermediateClosureEquiv_algebraMap F U x
      _ = (f (f.symm x) : AlgebraicClosure F.Carrier) :=
        (congrArg Subtype.val (f.apply_symm_apply x)).symm
      _ = k (g x : AlgebraicClosure T.field) :=
        (hf (f.symm x)).trans (congrArg (fun z : C.field => k (z : AlgebraicClosure T.field)) hg.symm)
      _ = k (eC (algebraMap C.field _ (g x))) :=
        (congrArg k (intermediateClosureEquiv_algebraMap TP C (g x))).symm
  let c₀ (y : localWeilGroup CP) : weilSubgroup F U :=
    ⟨j (intermediateWeilEquiv TP C y), (embeddedWeil_mem F T U C f hf _).mp
      (intermediateWeilEquiv TP C y).2⟩
  let c (y : localWeilGroup CP) : localWeilGroup UP := (intermediateWeilEquiv F U).symm (c₀ y)
  have hc (y : localWeilGroup CP) (x : AlgebraicClosure U.field) :
      θ (AlgEquiv.toAlgHom (localProjection UP (c y)) x) =
        AlgEquiv.toAlgHom (localProjection CP y) (θ x) := by
    apply eC.injective
    apply (k).injective
    have hp : intermediateGaloisMap F U (localProjection UP (c y)) =
        intermediateGaloisMap F T (intermediateGaloisMap TP C (localProjection CP y)) := by
      rw [show intermediateGaloisMap F U (localProjection UP (c y)) =
        localProjection F (c₀ y) from intermediateWeilEquiv_symm_projection F U _]
      change localProjection F (j (intermediateWeilEquiv TP C y)) = _
      rw [localProjection_intermediateWeilMap, intermediateWeilEquiv_projection]
    calc
      k (eC (θ (AlgEquiv.toAlgHom (localProjection UP (c y)) x))) =
          eU (AlgEquiv.toAlgHom (localProjection UP (c y)) x) := hθ' _
      _ = AlgEquiv.toAlgHom (intermediateGaloisMap F U (localProjection UP (c y))) (eU x) :=
        (intermediateClosureEquiv_galoisMap F U _ x).symm
      _ = AlgEquiv.toAlgHom
          (intermediateGaloisMap F T (intermediateGaloisMap TP C (localProjection CP y)))
            (k (eC (θ x))) := by rw [hp, hθ']
      _ = k (AlgEquiv.toAlgHom (intermediateGaloisMap TP C (localProjection CP y)) (eC (θ x))) :=
        intermediateClosureEquiv_galoisMap F T _ _
      _ = k (eC (AlgEquiv.toAlgHom (localProjection CP y) (θ x))) :=
        congrArg k (intermediateClosureEquiv_galoisMap TP C _ _)
  let y := (intermediateWeilEquiv TP C).symm w
  have hy : c₀ y = v := by
    apply Subtype.ext
    change j (intermediateWeilEquiv TP C ((intermediateWeilEquiv TP C).symm w)) = v.val
    rw [ContinuousMulEquiv.apply_symm_apply, hv]
  have h := CommonClosureTransport.reciprocityUnits_compatible_closure_equiv UP CP g θ hθ c hc
    (canonicalStandaloneReciprocity UP) (canonicalStandaloneReciprocity_geometric UP)
    (canonicalStandaloneReciprocity CP) (canonicalStandaloneReciprocity_geometric CP) y
  change LocalFactor.RankOne.reciprocityUnits UP (canonicalStandaloneReciprocity UP)
    ((intermediateWeilEquiv F U).symm (c₀ y)) = _ at h
  rw [hy] at h
  exact h

private def continuousUnitsEquiv (A B : PadicField.{uF} p)
    (g : A.Carrier ≃ₐ[Padic p] B.Carrier) :
    letI := A.canonicalTopologicalData.topology
    letI := B.canonicalTopologicalData.topology
    A.Carrierˣ →ₜ* B.Carrierˣ := by
  letI := A.canonicalTopologicalData.topology
  letI := B.canonicalTopologicalData.topology
  letI := A.canonicalTopologicalData.moduleTopology
  letI := B.canonicalTopologicalData.moduleTopology
  have := IsModuleTopology.toContinuousAdd (Padic p) B.Carrier
  exact ⟨Units.map g.toRingEquiv.toMonoidHom,
    (IsModuleTopology.continuous_of_linearMap g.toLinearMap).units_map _⟩

section MackeyCharacter

open scoped Pointwise

variable (E : Extension F) (a : localWeilGroup F)

local notation "τ" => localProjection F a
local notation "B" => E.conj (localProjection F a)

set_option maxHeartbeats 600000 in
/-- The actual local norm-pullback of the conjugate character on the new inducing field. -/
def mackeyFieldCharacter (h : (B).field ≤ U.field) (χ : FieldCharacter F E) :
    FieldCharacter TP C := by
  let BP := (B).asPadicField (p := p)
  let EP := E.asPadicField (p := p)
  letI : Algebra (Padic p) (B).field := BP.algebra
  letI : Algebra (Padic p) U.field := (UP).algebra
  letI : Algebra (Padic p) E.field := EP.algebra
  letI := (fieldData TP C).topology
  letI := (fieldData F U).topology
  letI := (fieldData F B).topology
  letI := (fieldData F E).topology
  letI : Algebra (B).field U.field := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower (Padic p) (B).field U.field := IsScalarTower.of_algebraMap_eq' rfl
  let gConj := (CommonClosureTransport.intermediateConjugationEquiv F E τ).symm
  let i := continuousUnitsEquiv CP UP (embeddedPadicEquiv F T U C f hf)
  let c := continuousUnitsEquiv BP EP gConj
  exact χ.comp (c.comp ((localNorm (fieldData F B) (fieldData F U)).comp i))

set_option maxHeartbeats 600000 in
/-- The two transports and the norm in the local character are the prescribed field maps. -/
theorem mackeyFieldCharacter_apply (h : (B).field ≤ U.field) (χ : FieldCharacter F E)
    (x : C.fieldˣ) :
    mackeyFieldCharacter F T U C f hf E a h χ x =
      χ (Units.mapEquiv
        (IntermediateField.equivMap E.field (localProjection F a).toAlgHom).symm.toMulEquiv
        ((B).unitsNorm U h (Units.mapEquiv f.toMulEquiv x))) :=
  rfl

private theorem weil_mem_conjField (v : localWeilGroup F) :
    v ∈ weilSubgroup F B ↔ v ∈ conjugate (weilSubgroup F E) a := by
  let s : Gal(AlgebraicClosure F.Carrier/F.Carrier) := τ
  let q : Gal(AlgebraicClosure F.Carrier/F.Carrier) := localProjection F v
  change q ∈ (E.field.map s.toAlgHom).fixingSubgroup ↔ _
  rw [IsGalois.map_fixingSubgroup E.field s, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    mem_conjugate_iff]
  let r : Gal(AlgebraicClosure F.Carrier/F.Carrier) := localProjection F (a⁻¹ * v * a)
  change (MulAut.conj s)⁻¹ • q ∈ E.field.fixingSubgroup ↔ r ∈ E.field.fixingSubgroup
  rw [← map_inv MulAut.conj, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  have hr : r = s⁻¹ * q * s := by
    simp only [r, s, q, map_mul, map_inv]
    rfl
  rw [hr]

include hf in
/-- Fixing the embedded compositum is the Mackey intersection condition. -/
theorem embeddedWeil_mem_conjugate (hU : U.field = T.field ⊔ (B).field)
    (w : localWeilGroup TP) :
    w ∈ weilSubgroup TP C ↔ j w ∈ conjugate (weilSubgroup F E) a := by
  have hw : j w ∈ weilSubgroup F T := (intermediateWeilEquiv F T w).2
  let q : Gal(AlgebraicClosure F.Carrier/F.Carrier) := localProjection F (j w)
  change q ∈ T.field.fixingSubgroup at hw
  rw [embeddedWeil_mem F T U C f hf, ← weil_mem_conjField F E a]
  change q ∈ U.field.fixingSubgroup ↔ q ∈ (B).field.fixingSubgroup
  rw [hU, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
  exact and_iff_right hw

private theorem reciprocityUnits_mackeyNorm (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (h : (B).field ≤ U.field)
    (v : weilSubgroup F U) (z : weilSubgroup F E)
    (hz : (z : localWeilGroup F) = a⁻¹ * (v : localWeilGroup F) * a) :
    Units.mapEquiv (IntermediateField.equivMap E.field (localProjection F a).toAlgHom).symm.toMulEquiv
      ((B).unitsNorm U h (reciprocityUnits F e U v)) =
        reciprocityUnits F e E z := by
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let i := (B).weilInclusion U h (localResidueDegree F)
  let c := E.weilConjugation (localResidueDegree F) a
  have hc : c z = i v := by
    apply Subtype.ext
    change a * (z : localWeilGroup F) * a⁻¹ = (v : localWeilGroup F)
    simp [hz, mul_assoc]
  have hn : reciprocityUnits F e B (i v) =
      (B).unitsNorm U h (reciprocityUnits F e U v) :=
    DFunLike.congr_fun (he.1.1 B U h) (abelianizationProjection _ v)
  have hec : reciprocityUnits F e B (c z) =
      E.unitsConjugation τ (reciprocityUnits F e E z) :=
    DFunLike.congr_fun (he.1.2.2.1 a E) (abelianizationProjection _ z)
  rw [← hn, ← hc, hec]
  apply Units.ext
  exact (IntermediateField.equivMap E.field (localProjection F a).toAlgHom).symm_apply_apply _

include hf in
/-- The finite-component norm formula gives the exact Mackey character on the child Weil group. -/
theorem weilCharacter_mackey (e : ReciprocityFamily F) (he : NormalizedReciprocity F e)
    (eT : ReciprocityFamily TP) (heT : NormalizedReciprocity TP eT)
    (χ : FieldCharacter F E) (χT : FieldCharacter TP C)
    (h : (B).field ≤ U.field)
    (hχ : ∀ x : C.fieldˣ,
      χT x = χ (Units.mapEquiv
        (IntermediateField.equivMap E.field (localProjection F a).toAlgHom).symm.toMulEquiv
          ((B).unitsNorm U h (Units.map f.toMonoidHom x))))
    (w : weilSubgroup TP C) (z : weilSubgroup F E)
    (hz : (z : localWeilGroup F) = a⁻¹ * j w * a) :
    weilCharacter TP eT C χT w = weilCharacter F e E χ z := by
  let v : weilSubgroup F U := ⟨j w, (embeddedWeil_mem F T U C f hf w).mp w.2⟩
  change χT (reciprocityUnits TP eT C w) = χ (reciprocityUnits F e E z)
  rw [hχ, ← reciprocityUnits_embedded F T U C f hf e he eT heT w v rfl,
    reciprocityUnits_mackeyNorm F U E a e he h v z hz]

end MackeyCharacter

end Langlands.Global.GeneralPosition
