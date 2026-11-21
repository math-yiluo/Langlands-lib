import Langlands.Automorphic.TranslatedBlockConstantTerm
import Langlands.Automorphic.BlockShapeLeviSliceCompactFinite

/-! # The Levi restriction of a translated period is another actual Levi restriction -/

noncomputable section

universe u

open NumberField
open scoped Classical BigOperators Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GeneralLinear
  Langlands.Archimedean.Kostant Langlands.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : OperatorRealization F n)

local instance translatedLeviImageRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedLeviImageContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedLeviImageFiniteSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedLeviImageFormsAddCommGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance translatedLeviImageStableAddCommGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedLeviImageRealizationAddCommGroup : AddCommGroup S.Space := Submodule.addCommGroup _

local notation "I" => Fin B.length
local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "Cen" => (Fin B.length → Ideles F)
local notation "R" => mixedEmbedding.mixedSpace F
local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "β" => blockConstantTermScalarAction F B
local notation "φ" => realizedBlockConstantTerm F B S
local notation "E" => translatedFunctionSum β φ
local notation "ev" => translatedFunctionEmbedding β φ
local notation "ρ" => blockLeviScalarAction F B
local notation "Lemb" => B.leviEmbedding (Adeles F)

/-- Restrict the original period of a realized form to the actual Levi. -/
def realizedBlockLeviRestriction : S.Space →ₗ[ℂ] (M → ℂ) :=
  (blockLeviTermRestriction F B).comp
    ((automorphicSubrepresentation F n).toSubmodule.subtype.comp S.formInclusion.toLinearMap)

local notation "q" => realizedBlockLeviRestriction F B S

/-- Insert a scalar idele in a single block of the actual Levi. -/
theorem blockLeviScalars_mulSingle (i : I) (z : Ideles F) :
    blockLeviScalars F B (Pi.mulSingle i z) =
      Pi.mulSingle i (AdelicGL.scalar F (B.size i) z) := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [blockLeviScalars_apply, Pi.mulSingle_eq_same]
  · simp only [blockLeviScalars_apply, Pi.mulSingle_eq_of_ne h, map_one]

private theorem leviEmbedding_infinite (m : M) :
    AdelicGL.infinite F n (Lemb m) =
      B.leviEmbedding (InfiniteAdeles F) (AdelicBlockParabolic.leviInfinite F B m) :=
  congrArg Subtype.val (AdelicBlockParabolic.infinite_leviInParabolic F B m)

private theorem leviEmbedding_finite (m : M) :
    AdelicGL.finite F n (Lemb m) =
      B.leviEmbedding (FiniteAdeles F) (AdelicBlockParabolic.leviFinite F B m) :=
  congrArg Subtype.val (AdelicBlockParabolic.finite_leviInParabolic F B m)

/-- The insertion of an archimedean block commutes with passage to the full adeles. -/
theorem blockShapeLeviEmbedding_singleInfinite (i : I) (a : InfiniteAdelicGL F (B.size i)) :
    Lemb (Pi.mulSingle i (AdelicGL.ofInfinite F (B.size i) a)) =
      AdelicGL.ofInfinite F n (B.leviEmbedding (InfiniteAdeles F) (Pi.mulSingle i a)) := by
  let m : M := Pi.mulSingle i (AdelicGL.ofInfinite F (B.size i) a)
  apply AdelicGL.ext_infinite_finite F n
  · have h : AdelicBlockParabolic.leviInfinite F B m = Pi.mulSingle i a := by
      funext j
      change AdelicGL.infinite F (B.size j) (m j) = _
      by_cases hj : j = i
      · subst j
        simp only [m, Pi.mulSingle_eq_same, AdelicGL.infinite_ofInfinite]
      · simp only [m, Pi.mulSingle_eq_of_ne hj, map_one]
    rw [leviEmbedding_infinite F B m, h, AdelicGL.infinite_ofInfinite]
  · have h : AdelicBlockParabolic.leviFinite F B m = 1 := by
      funext j
      change AdelicGL.finite F (B.size j) (m j) = 1
      by_cases hj : j = i
      · subst j
        simp only [m, Pi.mulSingle_eq_same, AdelicGL.finite_ofInfinite]
      · simp only [m, Pi.mulSingle_eq_of_ne hj, map_one]
    rw [leviEmbedding_finite F B m, h, map_one, AdelicGL.finite_ofInfinite]

omit [NumberField F] in
private theorem sign_mem_compact (d : ℕ) (s : RP → Bool) :
    Matrix.GeneralLinearGroup.scalar (Fin d) (mixedUnitToInfinite F (mixedRealSignUnit F s)) ∈
      standardInfiniteCompact F d := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let b := Matrix.GeneralLinearGroup.scalar (Fin d) (mixedUnitToInfinite F (mixedRealSignUnit F s))
  have h : archimedeanGLCoordinates F d b = Matrix.GeneralLinearGroup.scalar (Fin d) (mixedRealSignUnit F s) := by
    change Matrix.GeneralLinearGroup.map e.toRingHom b = _
    rw [show b = Matrix.GeneralLinearGroup.scalar (Fin d) _ from rfl,
      Matrix.GeneralLinearGroup.map_scalar]
    congr 1
    apply Units.ext
    exact e.apply_symm_apply _
  refine (mem_standardInfiniteCompact_iff F d b).mpr ⟨?_, ?_⟩
  · intro v
    have hv : realMatrix F d (archimedeanGLCoordinates F d b) v =
        if s v then (-1 : Matrix (Fin d) (Fin d) ℝ) else 1 := by
      rw [h]
      apply Matrix.ext
      intro a b
      change (Matrix.scalar (Fin d) ((mixedRealSignUnit F s : Rˣ) : R) a b).1 v = _
      rw [Matrix.scalar_apply, Matrix.diagonal_apply]
      by_cases ha : a = b <;> cases hs : s v <;>
        simp [ha, hs, Matrix.one_apply, show ((mixedRealSignUnit F s : Rˣ) : R).1 v =
          (if s v then -1 else 1) from rfl]
    rw [hv]
    split_ifs <;> simp [Matrix.mem_unitaryGroup_iff]
  · intro v
    have hv : complexMatrix F d (archimedeanGLCoordinates F d b) v = 1 := by
      rw [h]
      apply Matrix.ext
      intro a b
      change (Matrix.scalar (Fin d) ((mixedRealSignUnit F s : Rˣ) : R) a b).2 v = _
      rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
      split_ifs <;> rfl
    rw [hv]
    exact (Matrix.unitaryGroup (Fin d) ℂ).one_mem

private theorem scalarRestriction_eq_of_rightAction (f : S.Space) (z : Cen) (b : AdelicGL F n)
    (hb : Lemb (blockLeviScalars F B z) = b) (f' : S.Space)
    (hf : S.ambient f' = finiteSmoothRightAction F n b (S.ambient f)) :
    ρ z (q f) = q f' := by
  funext m
  change blockShapeLeviSlice F B (S.ambient f) 1 (m * blockLeviScalars F B z) =
    blockShapeLeviSlice F B (S.ambient f') 1 m
  rw [hf, blockShapeLeviSlice_rightAction, one_mul]
  simp only [blockShapeLeviSlice, map_mul, hb, mul_one]

private def preservesRealizedLeviImage : Submonoid Cen where
  carrier := {z | ∀ f : S.Space, ρ z (q f) ∈ LinearMap.range (q)}
  one_mem' := fun f => by
    rw [map_one, Module.End.one_apply]
    exact LinearMap.mem_range_self _ _
  mul_mem' {a b} ha hb := fun f => by
    obtain ⟨g, hg⟩ := hb f
    change ρ (a * b) (q f) ∈ LinearMap.range (q)
    rw [map_mul, Module.End.mul_apply, ← hg]
    exact ha g

local notation "J" => preservesRealizedLeviImage F B S

private theorem finiteSingle_preserves (i : I) (z : FiniteIdeles F) :
    Pi.mulSingle i (finiteIdelesInclusion F z) ∈ J := by
  intro f
  let a : Cen := Pi.mulSingle i (finiteIdelesInclusion F z)
  let m := blockLeviScalars F B a
  let d := AdelicGL.finite F n (Lemb m)
  have hInf : AdelicBlockParabolic.leviInfinite F B m = 1 := by
    funext j
    change AdelicGL.infinite F (B.size j) (AdelicGL.scalar F (B.size j) (a j)) = 1
    by_cases hj : j = i
    · subst j
      simp only [a, Pi.mulSingle_eq_same, AdelicGL.infinite_scalar_finiteIdelesInclusion]
    · simp only [a, Pi.mulSingle_eq_of_ne hj, map_one]
  have hb : Lemb m = AdelicGL.ofFinite F n d := by
    apply AdelicGL.ext_infinite_finite F n
    · rw [leviEmbedding_infinite, hInf, map_one, AdelicGL.infinite_ofFinite]
    · rw [AdelicGL.finite_ofFinite]
  exact ⟨S.finiteRepresentation d f,
    (scalarRestriction_eq_of_rightAction F B S f a _ hb _ rfl).symm⟩

private theorem signSingle_preserves (i : I) (s : RP → Bool) :
    Pi.mulSingle i (infiniteIdelesInclusion F (mixedUnitToInfinite F (mixedRealSignUnit F s))) ∈ J := by
  intro f
  let x := mixedUnitToInfinite F (mixedRealSignUnit F s)
  let a : Cen := Pi.mulSingle i (infiniteIdelesInclusion F x)
  let k : standardInfiniteCompact F (B.size i) :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin (B.size i)) x, sign_mem_compact F (B.size i) s⟩
  let b := blockShapeInfiniteCompactEmbedding B F i k
  have hb : Lemb (blockLeviScalars F B a) = AdelicGL.ofInfinite F n b.val := by
    rw [show a = Pi.mulSingle i (infiniteIdelesInclusion F x) from rfl,
      blockLeviScalars_mulSingle, AdelicGL.scalar_infiniteIdelesInclusion,
      blockShapeLeviEmbedding_singleInfinite]
    rfl
  exact ⟨S.compactRepresentation b f,
    (scalarRestriction_eq_of_rightAction F B S f a _ hb _ rfl).symm⟩

set_option maxHeartbeats 500000 in
private theorem expSingle_preserves (i : I) (x : R) :
    Pi.mulSingle i (infiniteIdelesInclusion F (mixedUnitToInfinite F (banachExpUnit x))) ∈ J := by
  intro f
  let a : Cen := Pi.mulSingle i (infiniteIdelesInclusion F (mixedUnitToInfinite F (banachExpUnit x)))
  let X := scalarDirection F (B.size i) x
  let Z := scalarDirectionCenter F (B.size i) x
  let ψ := blockLeviCenterOrbitMap F B (S.ambient f)
  have hf : IsCenterFinite F n (finiteSmoothInclusion F n (S.ambient f)) :=
    (S.isAutomorphicForm_ambient f).2.2.1
  have he : blockLeviScalars F B a = blockLeviOneParameter F B i X 1 := by
    rw [show a = _ from rfl, blockLeviScalars_mulSingle, AdelicGL.scalar_infiniteIdelesInclusion]
    simp only [blockLeviOneParameter, X, infiniteOneParameter_scalarDirection, one_smul]
  have hm : (q f) ∈ LinearMap.range ψ := blockLeviTermRestriction_mem_centerOrbit F B (S.ambient f)
  have h := blockLeviCenterOrbit_range_mul_oneParameter F B i (S.ambient f) hf X Z rfl ⟨q f, hm⟩ 1
  change (fun m => q f (m * blockLeviOneParameter F B i X 1)) ∈ LinearMap.range ψ at h
  rw [← he] at h
  obtain ⟨z, hz⟩ := h
  let e := LieEnvelopingEquiv.enveloping (complexLieProductMatrixCoordinates F n)
  let j := LieEnvelopingEquiv.map (AlgHom.toLieHom (blockMatrixInclusion B (ι := ComplexLieMatrixPlace F)))
  let f' := S.envelopingAction (e.symm (j z.val)) f
  exact ⟨f', hz⟩

private theorem single_preserves (i : I) (z : Ideles F) : Pi.mulSingle i z ∈ J := by
  let j := MonoidHom.mulSingle (fun _ : I => Ideles F) i
  let e := ideleProductEquiv F
  let u := (e z).1
  let b := (e z).2
  obtain ⟨s, x, h⟩ := exists_sign_mul_expUnit F ((mixedUnitToInfinite F).symm u)
  have hu : u = mixedUnitToInfinite F (mixedRealSignUnit F s) * mixedUnitToInfinite F (banachExpUnit x) := by
    have hh := congrArg (mixedUnitToInfinite F) h
    rwa [MulEquiv.apply_symm_apply, map_mul] at hh
  have hz : z = infiniteIdelesInclusion F u * finiteIdelesInclusion F b := by
    apply e.injective
    rw [map_mul]
    change e z = e (e.symm (u, 1)) * e (e.symm (1, b))
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact Prod.ext (mul_one _).symm (one_mul _).symm
  change j z ∈ J
  rw [hz, hu, map_mul, map_mul, map_mul]
  exact (J).mul_mem ((J).mul_mem (signSingle_preserves F B S i s) (expSingle_preserves F B S i x))
    (finiteSingle_preserves F B S i b)

private theorem blockScalar_preserves (z : Cen) : z ∈ J := by
  rw [← Finset.univ_prod_mulSingle z]
  exact (J).prod_mem fun i _ => single_preserves F B S i (z i)

set_option maxHeartbeats 650000 in
/-- Every translated-period Levi restriction is the restriction of a single actual form
in the original realization. -/
theorem translatedBlockLeviRestriction_mem_range (v : TranslatedBlockConstantTerms F B S) :
    translatedBlockLeviRestriction F B S v ∈ LinearMap.range (q) := by
  let L : (AdelicGL F n → ℂ) →ₗ[ℂ] (M → ℂ) :=
    { toFun h m := h (Lemb m)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  obtain ⟨w, rfl⟩ := (LinearMap.ker E).mkQ_surjective v
  change L (E w) ∈ LinearMap.range (q)
  induction w using Finsupp.induction_linear with
  | zero => simp only [map_zero, Submodule.zero_mem]
  | add a b ha hb => simpa only [map_add] using (LinearMap.range (q)).add_mem ha hb
  | single z f =>
    rw [translatedFunctionSum_single]
    have he : L (β z (φ f)) = ρ z (q f) := by
      funext m
      change blockShapeConstantTerm B F (S.ambient f) (Lemb (blockLeviScalars F B z) * Lemb m) =
        blockShapeConstantTerm B F (S.ambient f) (Lemb (m * blockLeviScalars F B z) * 1)
      rw [mul_one, ← (blockLeviScalars_commute F B z m).eq, map_mul]
    rw [he]
    exact blockScalar_preserves F B S z f

end Langlands.Automorphic
