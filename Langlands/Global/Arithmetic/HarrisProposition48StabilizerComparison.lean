import Langlands.Global.Arithmetic.HarrisUniquePlace
import Langlands.Global.AdelicFunctoriality.FinitePlaceDegreeTransfer
import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Langlands.LocalFactor.CommonClosureSurjectivity
import Langlands.Weil.Local.AssemblyProof
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Reading the auxiliary stabilizer on the number field -/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open AdelicFunctoriality GeneralPosition LocalFactor.CommonClosure LocalClassField Weil.Local
open scoped NumberField FiniteExtension

/-- Evaluate a finite component only on units coming from the number field. -/
def globalUnitComponent {K : Type*} [Field K] [NumberField K]
    (ξ : HeckeCharacter K) (v : FinitePlace K) : Kˣ →* ℂˣ :=
  ξ.finiteComponent v |>.toMonoidHom.comp (Units.map (algebraMap K (v.adicCompletion K)))

section NumberFields

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
/-- Transport lying over through a commuting square of field isomorphisms. -/
theorem finitePlaceEquiv_liesOver {K' L' : Type*}
    [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']
    (e : K ≃+* K') (f : L ≃+* L')
    (he : ∀ x, f (algebraMap K L x) = algebraMap K' L' (e x))
    (v : FinitePlace K') (w : FinitePlace L') [hw : w.asIdeal.LiesOver v.asIdeal] :
    (finitePlaceEquiv f w).asIdeal.LiesOver (finitePlaceEquiv e v).asIdeal := by
  refine ⟨?_⟩
  ext x
  have hx : RingOfIntegers.mapRingEquiv f (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap (𝓞 K') (𝓞 L') (RingOfIntegers.mapRingEquiv e x) :=
    RingOfIntegers.ext (he (x : K))
  rw [Ideal.mem_under, finitePlaceEquiv_mem, finitePlaceEquiv_mem, hx, ← Ideal.mem_under,
    Ideal.LiesOver.over (P := w.asIdeal) (p := v.asIdeal)]

/-- A single completed coordinate computes the global norm at a place with one place above it. -/
theorem localUnitNorm_globalUnits (v : FinitePlace K) (w : FinitePlace L)
    [hw : w.asIdeal.LiesOver v.asIdeal] (h : HasUniquePlaceAbove L v) (z : Lˣ) :
    FiniteExtension.localUnitNorm v w (Units.map (algebraMap L (w.adicCompletion L)) z) =
      Units.map (algebraMap K (v.adicCompletion K)) (normUnits K L z) := by
  classical
  let : Unique (FinitePlacesAbove L v) :=
    { default := ⟨w, hw⟩
      uniq r := Subtype.ext (h r.1 w r.2 hw) }
  apply Units.ext
  have he := congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v)
    (adeleNorm_principal (K := K) (z : L))
  change (∏ q : FinitePlacesAbove L v,
      FiniteExtension.localNorm v q.1 (algebraMap L (q.1.adicCompletion L) (z : L))) =
        algebraMap K (v.adicCompletion K) (Algebra.norm K (z : L)) at he
  rw [Fintype.prod_unique] at he
  exact he

private theorem denseRange_completionUnits (w : FinitePlace L) :
    DenseRange (Units.map (algebraMap L (w.adicCompletion L)).toMonoidHom) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨x, y, hy, hxy⟩ := (denseRange_algebraMap L w).exists_mem_open
    (Units.isOpenEmbedding_val.isOpenMap U hU) (hne.image Units.val)
  have hx : x ≠ 0 := fun h => y.ne_zero (by rw [hxy, h, map_zero])
  exact ⟨y, hy, Units.mk0 x hx, Units.ext hxy.symm⟩

private theorem finitePlaceEquiv_aut (v : FinitePlace K) (w : FinitePlace L)
    [w.asIdeal.LiesOver v.asIdeal] (h : HasUniquePlaceAbove L v) (a : L ≃ₐ[K] L) :
    finitePlaceEquiv a.toRingEquiv w = w := by
  have hw := finitePlaceEquiv_liesOver (RingEquiv.refl K) a.toRingEquiv a.commutes v w
  simpa using h _ w (by simpa using hw) inferInstance

private def completionCongr {w w' : FinitePlace L} (h : w = w') :
    w.adicCompletion L ≃+* w'.adicCompletion L := by
  subst w'
  exact RingEquiv.refl _

private theorem completionCongr_global {w w' : FinitePlace L} (h : w = w') (x : L) :
    completionCongr h (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w'.adicCompletion L) x := by
  cases h
  rfl

private theorem continuous_completionCongr {w w' : FinitePlace L} (h : w = w') :
    Continuous (completionCongr h) := by
  cases h
  exact continuous_id

private def completionAut (v : FinitePlace K) (w : FinitePlace L)
    [w.asIdeal.LiesOver v.asIdeal] (h : HasUniquePlaceAbove L v) (a : L ≃ₐ[K] L) :
    w.adicCompletion L ≃+* w.adicCompletion L :=
  (completionCongr (finitePlaceEquiv_aut v w h a).symm).trans
    (finiteCompletionEquiv a.toRingEquiv w)

private theorem completionAut_global (v : FinitePlace K) (w : FinitePlace L)
    [w.asIdeal.LiesOver v.asIdeal] (h : HasUniquePlaceAbove L v) (a : L ≃ₐ[K] L) (x : L) :
    completionAut v w h a (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) (a x) := by
  simp only [completionAut, RingEquiv.trans_apply, completionCongr_global,
    finiteCompletionEquiv_coe]
  rfl

private theorem continuous_completionAut (v : FinitePlace K) (w : FinitePlace L)
    [w.asIdeal.LiesOver v.asIdeal] (h : HasUniquePlaceAbove L v) (a : L ≃ₐ[K] L) :
    Continuous (completionAut v w h a) := by
  exact (continuous_finiteCompletionEquiv a.toRingEquiv w).comp
    (continuous_completionCongr _)

private theorem completionAut_base (v : FinitePlace K) (w : FinitePlace L)
    [w.asIdeal.LiesOver v.asIdeal] (h : HasUniquePlaceAbove L v) (a : L ≃ₐ[K] L)
    (x : v.adicCompletion K) :
    completionAut v w h a (FiniteExtension.completionMap v w x) =
      FiniteExtension.completionMap v w x := by
  apply congrFun ((denseRange_algebraMap K v).equalizer
    ((continuous_completionAut v w h a).comp (FiniteExtension.continuous_completionMap v w))
    (FiniteExtension.continuous_completionMap v w) ?_) x
  funext x
  simp only [Function.comp_apply, FiniteExtension.completionMap_coe, completionAut_global,
    AlgEquiv.commutes]

end NumberFields

section Weil

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : Extension F)

private theorem reciprocityUnits_sameField
    (e : ReciprocityFamily F) (A B : Extension F) (h : A.field = B.field)
    (x : weilSubgroup F A) (y : weilSubgroup F B)
    (hxy : (x : localWeilGroup F) = (y : localWeilGroup F)) :
    ((reciprocityUnits F e A x : A.field) : AlgebraicClosure F.Carrier) =
      ((reciprocityUnits F e B y : B.field) : AlgebraicClosure F.Carrier) := by
  obtain rfl : A = B := Subtype.ext h
  obtain rfl : x = y := Subtype.ext hxy
  rfl

private theorem reciprocityUnits_conj
    (e : ReciprocityFamily F) (he : NormalizedReciprocity F e)
    (M : Extension F) [Normal F.Carrier M.field] [(weilSubgroup F M).Normal]
    (g : localWeilGroup F) (x : weilSubgroup F M) :
    reciprocityUnits F e M ((MulAut.conjNormal g) x) =
      Units.map ((localProjection F g).restrictNormal M.field).toRingEquiv.toMonoidHom
        (reciprocityUnits F e M x) := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let σ : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
    localProjection F g
  have hM : (M.conj σ).field = M.field :=
    IntermediateField.normal_iff_forall_map_eq'.mp inferInstance σ
  have hc : reciprocityUnits F e (M.conj σ)
      (M.weilConjugation (localResidueDegree F) g x) =
        M.unitsConjugation σ (reciprocityUnits F e M x) :=
    DFunLike.congr_fun (he.1.2.2.1 g M) (abelianizationProjection _ x)
  apply Units.ext
  apply Subtype.ext
  calc
    _ = ((reciprocityUnits F e (M.conj σ)
        (M.weilConjugation (localResidueDegree F) g x) : (M.conj σ).field) :
          AlgebraicClosure F.Carrier) :=
      reciprocityUnits_sameField F e M (M.conj σ) hM.symm _ _ rfl
    _ = σ ((reciprocityUnits F e M x : M.field) : AlgebraicClosure F.Carrier) := by rw [hc]; rfl
    _ = _ := (AlgEquiv.restrictNormal_commutes σ M.field _).symm

private instance normalClosure_isGalois : IsGalois F.Carrier (galoisClosure F E).field := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  change IsGalois F.Carrier (IntermediateField.normalClosure F.Carrier E.field
    (AlgebraicClosure F.Carrier))
  infer_instance

private def weilRestriction (g : localWeilGroup F) :
    Gal((galoisClosure F E).field/F.Carrier) :=
  (localProjection F g).restrictNormal (galoisClosure F E).field

private theorem weilRestriction_surjective : Function.Surjective (weilRestriction F E) :=
  denseRange_discrete.mp <|
    (AlgEquiv.restrictNormalHom_surjective (K₁ := (galoisClosure F E).field)
      (AlgebraicClosure F.Carrier)).denseRange.comp (localProjection_denseRange F)
      (InfiniteGalois.restrictNormalHom_continuous (galoisClosure F E).field)

private theorem closureRestriction_norm (e : ReciprocityFamily F) (he : NormalizedReciprocity F e)
    (χ : FieldCharacter F E) (x : weilSubgroup F (galoisClosure F E)) :
    closureRestriction F E (weilCharacter F e E χ) x =
      χ (E.unitsNorm (galoisClosure F E) (le_galoisClosure F E)
        (reciprocityUnits F e (galoisClosure F E) x)) := by
  let := (fieldData F E).topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact congrArg χ (DFunLike.congr_fun (he.1.1 E (galoisClosure F E) (le_galoisClosure F E))
    (abelianizationProjection _ x))

private theorem weilRestriction_fixes_iff (g : localWeilGroup F) :
    (∀ y : E.field, weilRestriction F E g (IntermediateField.inclusion
      (le_galoisClosure F E) y) = IntermediateField.inclusion (le_galoisClosure F E) y) ↔
      g ∈ weilSubgroup F E := by
  let M := galoisClosure F E
  let i := IntermediateField.inclusion (le_galoisClosure F E)
  let σ : Gal(AlgebraicClosure F.Carrier/F.Carrier) := localProjection F g
  change (∀ y, σ.restrictNormal M.field (i y) = i y) ↔ σ ∈ E.field.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    exact (AlgEquiv.restrictNormal_commutes σ M.field (i ⟨x, hx⟩)).symm.trans
      (congrArg (fun y : M.field => (y : AlgebraicClosure F.Carrier)) (h ⟨x, hx⟩))
  · intro h y
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes σ M.field (i y)).trans (h y y.property)

end Weil

namespace PlaceDatum

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {F' : Extension F}
variable {E E' L : Type*} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]
variable (P : PlaceDatum F F' E E' L) (hP : P.IsCompatible)

private def middleCompletionEquiv : P.v'.adicCompletion E' ≃+* F'.field := by
  let f : P.v'.adicCompletion E' →+* AlgebraicClosure F.Carrier :=
    (galoisClosure F F').field.val.toRingHom.comp
      (P.isoTilde.toRingHom.comp (FiniteExtension.completionMap P.v' P.vTilde))
  have hf : Set.range f = (F'.field : Set (AlgebraicClosure F.Carrier)) := hP.2
  let b := f.codRestrict F'.field (fun x => by
    change f x ∈ (F'.field : Set (AlgebraicClosure F.Carrier))
    rw [← hf]
    exact Set.mem_range_self x)
  refine RingEquiv.ofBijective b ⟨b.injective, ?_⟩
  intro y
  have hy : (y : AlgebraicClosure F.Carrier) ∈ Set.range f := hf.symm ▸ y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

private theorem middleCompletionEquiv_apply (x : P.v'.adicCompletion E') :
    ((P.middleCompletionEquiv hP x : F'.field) : AlgebraicClosure F.Carrier) =
      P.isoTilde (FiniteExtension.completionMap P.v' P.vTilde x) :=
  rfl

include hP in
private theorem characterNorm_completed (ξ : HeckeCharacter E') (χ : FieldCharacter F F')
    (hχ : P.HasComponent ξ χ) (z : (P.vTilde.adicCompletion L)ˣ) :
    χ (F'.unitsNorm (galoisClosure F F') (le_galoisClosure F F')
      (Units.map P.isoTilde.toMonoidHom z)) =
      ξ.finiteComponent P.v' (FiniteExtension.localUnitNorm P.v' P.vTilde z) := by
  let M := galoisClosure F F'
  let h := le_galoisClosure F F'
  let : Algebra F'.field M.field := (IntermediateField.inclusion h).toAlgebra
  let b := P.middleCompletionEquiv hP
  let n := FiniteExtension.localUnitNorm P.v' P.vTilde z
  have hn : Units.map b.toMonoidHom n =
      F'.unitsNorm M h (Units.map P.isoTilde.toMonoidHom z) := by
    apply Units.ext
    change b (Algebra.norm (P.v'.adicCompletion E') (z : P.vTilde.adicCompletion L)) =
      Algebra.norm F'.field (P.isoTilde (z : P.vTilde.adicCompletion L))
    rw [Algebra.norm_eq_of_equiv_equiv b P.isoTilde (x := (z : P.vTilde.adicCompletion L))]
    · exact b.apply_symm_apply _
    · exact RingHom.ext fun x => Subtype.ext (P.middleCompletionEquiv_apply hP x)
  rw [← hn]
  exact (hχ n _ (P.middleCompletionEquiv_apply hP (n : P.v'.adicCompletion E'))).symm

private def completedAut (h : HasUniquePlaceAbove L P.v) (a : Gal(L/E)) :
    Gal((galoisClosure F F').field/F.Carrier) :=
  { (P.isoTilde.symm.trans (completionAut P.v P.vTilde h a)).trans P.isoTilde with
    commutes' := fun x => by
      obtain ⟨y, rfl⟩ := P.iso.surjective x
      rw [← hP.1 y]
      change P.isoTilde (completionAut P.v P.vTilde h a
        (P.isoTilde.symm (P.isoTilde (FiniteExtension.completionMap P.v P.vTilde y)))) =
        P.isoTilde (FiniteExtension.completionMap P.v P.vTilde y)
      rw [P.isoTilde.symm_apply_apply, completionAut_base] }

private theorem completedAut_apply (h : HasUniquePlaceAbove L P.v) (a : Gal(L/E))
    (x : P.vTilde.adicCompletion L) :
    P.completedAut hP h a (P.isoTilde x) =
      P.isoTilde (completionAut P.v P.vTilde h a x) := by
  change P.isoTilde (completionAut P.v P.vTilde h a (P.isoTilde.symm (P.isoTilde x))) = _
  rw [P.isoTilde.symm_apply_apply]

private theorem completedAut_surjective [IsGalois E L] (h : HasUniquePlaceAbove L P.v) :
    Function.Surjective (P.completedAut hP h) := by
  classical
  let : Unique (FinitePlacesAbove L P.v) :=
    { default := ⟨P.vTilde, P.liesOver_vTilde⟩
      uniq r := Subtype.ext (h r.1 P.vTilde r.2 P.liesOver_vTilde) }
  refine ((Nat.bijective_iff_injective_and_card (P.completedAut hP h)).mpr ⟨?_, ?_⟩).2
  · intro a b hab
    ext x
    have hx := DFunLike.congr_fun hab (P.isoTilde (algebraMap L (P.vTilde.adicCompletion L) x))
    rw [P.completedAut_apply, P.completedAut_apply, completionAut_global,
      completionAut_global] at hx
    exact (algebraMap L (P.vTilde.adicCompletion L)).injective (P.isoTilde.injective hx)
  · rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
    have hdeg := finiteLocalDegree_sum (L := L) P.v
    rw [Fintype.sum_unique] at hdeg
    exact hdeg.symm.trans (Algebra.finrank_eq_of_equiv_equiv P.iso P.isoTilde
      (RingHom.ext fun x => (hP.1 x).symm))

private theorem completedAut_fixes_iff [IsScalarTower E E' L]
    (h : HasUniquePlaceAbove L P.v) (a : Gal(L/E)) :
    (∀ y : F'.field, P.completedAut hP h a (IntermediateField.inclusion
      (le_galoisClosure F F') y) = IntermediateField.inclusion (le_galoisClosure F F') y) ↔
      ∀ x : E', a (algebraMap E' L x) = algebraMap E' L x := by
  have hincl (y : P.v'.adicCompletion E') :
      IntermediateField.inclusion (le_galoisClosure F F') (P.middleCompletionEquiv hP y) =
        P.isoTilde (FiniteExtension.completionMap P.v' P.vTilde y) :=
    Subtype.ext (P.middleCompletionEquiv_apply hP y)
  constructor
  · intro hfix x
    have hx := hfix (P.middleCompletionEquiv hP (algebraMap E' (P.v'.adicCompletion E') x))
    rw [hincl, P.completedAut_apply, FiniteExtension.completionMap_coe,
      completionAut_global] at hx
    exact (algebraMap L (P.vTilde.adicCompletion L)).injective (P.isoTilde.injective hx)
  · intro hfix y
    obtain ⟨x, rfl⟩ := (P.middleCompletionEquiv hP).surjective y
    rw [hincl, P.completedAut_apply]
    apply congrArg P.isoTilde
    apply congrFun ((denseRange_algebraMap E' P.v').equalizer
      ((continuous_completionAut P.v P.vTilde h a).comp
        (FiniteExtension.continuous_completionMap P.v' P.vTilde))
      (FiniteExtension.continuous_completionMap P.v' P.vTilde) ?_) x
    funext y
    simp only [Function.comp_apply, FiniteExtension.completionMap_coe, completionAut_global, hfix]

include hP in
private theorem stabilizes_iff_global [IsScalarTower E E' L]
    (h : HasUniquePlaceAbove L P.v) (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (ξ : HeckeCharacter E') (χ : FieldCharacter F F')
    (hχ : P.HasComponent ξ χ) (g : localWeilGroup F) (a : Gal(L/E))
    (ha : weilRestriction F F' g⁻¹ = P.completedAut hP h a) :
    (closureRestriction F F' (weilCharacter F e F' χ)).comp
        (MulAut.conjNormal g⁻¹).toMonoidHom = closureRestriction F F' (weilCharacter F e F' χ) ↔
      ∀ z : Lˣ, globalUnitComponent ξ P.v'
          (normUnits E' L (Units.map a.toRingEquiv.toMonoidHom z)) =
        globalUnitComponent ξ P.v' (normUnits E' L z) := by
  let M := galoisClosure F F'
  let ρ := (ξ.finiteComponent P.v').comp (FiniteExtension.localUnitNorm P.v' P.vTilde)
  let act := Units.map (completionAut P.v P.vTilde h a).toMonoidHom
  let i := Units.map (algebraMap L (P.vTilde.adicCompletion L)).toMonoidHom
  let t := Units.map P.isoTilde.toMonoidHom
  let ψ := closureRestriction F F' (weilCharacter F e F' χ)
  have hact (z : (P.vTilde.adicCompletion L)ˣ) :
      Units.map (weilRestriction F F' g⁻¹).toRingEquiv.toMonoidHom (t z) = t (act z) := by
    apply Units.ext
    rw [ha]
    exact P.completedAut_apply hP h a (z : P.vTilde.adicCompletion L)
  have htest (x : weilSubgroup F M) (z : (P.vTilde.adicCompletion L)ˣ)
      (hx : reciprocityUnits F e M x = t z) :
      ψ ((MulAut.conjNormal g⁻¹) x) = ρ (act z) ∧ ψ x = ρ z := by
    change closureRestriction F F' (weilCharacter F e F' χ) ((MulAut.conjNormal g⁻¹) x) = _ ∧
      closureRestriction F F' (weilCharacter F e F' χ) x = _
    rw [closureRestriction_norm F F' e he, closureRestriction_norm F F' e he]
    change χ (F'.unitsNorm M (le_galoisClosure F F') (reciprocityUnits F e M
      ((MulAut.conjNormal g⁻¹) x))) = _ ∧
      χ (F'.unitsNorm M (le_galoisClosure F F') (reciprocityUnits F e M x)) = _
    rw [reciprocityUnits_conj F e he M g⁻¹ x, hx]
    change χ (F'.unitsNorm M (le_galoisClosure F F')
      (Units.map (weilRestriction F F' g⁻¹).toRingEquiv.toMonoidHom (t z))) = _ ∧
      χ (F'.unitsNorm M (le_galoisClosure F F') (t z)) = _
    rw [hact, P.characterNorm_completed hP ξ χ hχ (act z),
      P.characterNorm_completed hP ξ χ hχ z]
    exact ⟨rfl, rfl⟩
  have hcompleted : ψ.comp (MulAut.conjNormal g⁻¹).toMonoidHom = ψ ↔
      ∀ z, ρ (act z) = ρ z := by
    constructor
    · intro hψ z
      obtain ⟨x, hx⟩ := reciprocityUnits_surjective F e M (t z)
      obtain ⟨h₁, h₂⟩ := htest x z hx
      exact h₁.symm.trans ((DFunLike.congr_fun hψ x).trans h₂)
    · intro hρ
      apply MonoidHom.ext
      intro x
      obtain ⟨z, hz⟩ := (Units.mapEquiv P.isoTilde.toMulEquiv).surjective
        (reciprocityUnits F e M x)
      obtain ⟨h₁, h₂⟩ := htest x z hz.symm
      exact h₁.trans ((hρ z).trans h₂.symm)
  have hcomp (z : Lˣ) :
      ρ (i z) = globalUnitComponent ξ P.v' (normUnits E' L z) := by
    have h' : HasUniquePlaceAbove L P.v' := by
      intro w w' hw hw'
      let := hw
      let := hw'
      exact h w w' (Ideal.LiesOver.trans w.asIdeal P.v'.asIdeal P.v.asIdeal)
        (Ideal.LiesOver.trans w'.asIdeal P.v'.asIdeal P.v.asIdeal)
    exact congrArg (ξ.finiteComponent P.v') (localUnitNorm_globalUnits P.v' P.vTilde h' z)
  have hglobal (z : Lˣ) : act (i z) = i (Units.map a.toRingEquiv.toMonoidHom z) :=
    Units.ext (completionAut_global P.v P.vTilde h a (z : L))
  refine hcompleted.trans ⟨?_, ?_⟩
  · intro hρ z
    simpa only [hglobal, hcomp] using hρ (i z)
  · intro hχz z
    apply congrFun ((denseRange_completionUnits P.vTilde).equalizer
      (ρ.continuous.comp (continuous_completionAut P.v P.vTilde h a).units_map)
      ρ.continuous ?_) z
    funext y
    change ρ (act (i y)) = ρ (i y)
    rw [hglobal, hcomp, hcomp]
    exact hχz y

include hP in
/-- At a unique auxiliary place, exact Weil stabilization is equivalent to testing the
global norm character against automorphisms of the number-field normal closure. -/
theorem exactWeilStabilizer_iff_global [IsScalarTower E E' L] [IsGalois E L]
    (h : HasUniquePlaceAbove L P.v) (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (ξ : HeckeCharacter E') (χ : FieldCharacter F F')
    (hχ : P.HasComponent ξ χ) :
    HasExactWeilStabilizer F F' (weilCharacter F e F' χ) ↔
      ∀ a : Gal(L/E),
        (∀ z : Lˣ, globalUnitComponent ξ P.v'
            (normUnits E' L (Units.map a.toRingEquiv.toMonoidHom z)) =
          globalUnitComponent ξ P.v' (normUnits E' L z)) ↔
        ∀ x : E', a (algebraMap E' L x) = algebraMap E' L x := by
  have hfix (g : localWeilGroup F) (a : Gal(L/E))
      (ha : weilRestriction F F' g⁻¹ = P.completedAut hP h a) :
      (∀ x : E', a (algebraMap E' L x) = algebraMap E' L x) ↔ g ∈ weilSubgroup F F' := by
    rw [← P.completedAut_fixes_iff hP h a, ← ha, weilRestriction_fixes_iff]
    exact (weilSubgroup F F').inv_mem_iff
  constructor
  · intro hWeil a
    obtain ⟨g, hg⟩ := weilRestriction_surjective F F' (P.completedAut hP h a)
    have ha : weilRestriction F F' g⁻¹⁻¹ = P.completedAut hP h a := by
      rw [inv_inv]
      exact hg
    exact (P.stabilizes_iff_global hP h e he ξ χ hχ g⁻¹ a ha).symm.trans
      ((hWeil g⁻¹).trans (hfix g⁻¹ a ha).symm)
  · intro hGal g
    obtain ⟨a, ha⟩ := P.completedAut_surjective hP h (weilRestriction F F' g⁻¹)
    exact (P.stabilizes_iff_global hP h e he ξ χ hχ g a ha.symm).trans
      ((hGal a).trans (hfix g a ha.symm))

end PlaceDatum

end Langlands.Global.Harris
