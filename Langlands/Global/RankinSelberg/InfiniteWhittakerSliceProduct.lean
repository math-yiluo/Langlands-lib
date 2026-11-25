import Langlands.Global.RankinSelberg.InfiniteWhittakerResidualNonzero

/-! # Product of the actual infinite Whittaker slices -/

noncomputable section
open NumberField
open scoped Classical TensorProduct CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u uQ uI uA uB

namespace Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice

open Langlands.Automorphic InfinitePlaceFamily
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open Langlands.Global.CuspidalPairFunctionalEquation
open FiniteWhittakerTensor FiniteWhittakerSemilocal FiniteWhittakerDual InfiniteWhittakerResidual

private theorem eq_product_of_update {I : Type uI} [Fintype I] [DecidableEq I] {A : I → Type uA}
    (C : (∀ i, A i) → ℂ) (f : ∀ i, A i → ℂ) (b₀ : ∀ i, A i)
    (h₀ : ∀ i, f i (b₀ i) = 1)
    (hslice : ∀ i b, ∃ c : ℂ, ∀ x, C (Function.update b i x) = c * f i x)
    (b : ∀ i, A i) :
    C b = C b₀ * ∏ i, f i (b i) := by
  have step (i : I) (a : ∀ i, A i) (x : A i) :
      C (Function.update a i x) = C (Function.update a i (b₀ i)) * f i x := by
    obtain ⟨c, hc⟩ := hslice i a
    rw [hc x, hc (b₀ i), h₀, mul_one]
  let a (E : Finset I) (i : I) : A i := if i ∈ E then b i else b₀ i
  have hprod (E : Finset I) : C (a E) = C b₀ * ∏ i ∈ E, f i (b i) := by
    induction E using Finset.induction_on with
    | empty => simp [a]
    | @insert i E hi ih =>
      have hinsert : a (insert i E) = Function.update (a E) i (b i) := by
        funext j
        by_cases h : j = i
        · subst j
          simp [a]
        · simp [a, h]
      have hreset : Function.update (a E) i (b₀ i) = a E := by simp [a, hi]
      rw [hinsert, step, hreset, ih, Finset.prod_insert hi]
      ac_rfl
  simpa only [a, Finset.mem_univ, ite_true] using hprod Finset.univ

private theorem map_update {I : Type uI} [DecidableEq I] {A : I → Type uA} {B : I → Type uB}
    (f : ∀ i, A i → B i) (a : ∀ i, A i) (i : I) (x : A i) :
    (fun j => f j (Function.update a i x j)) = Function.update (fun j => f j (a j)) i (f i x) := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne h]

private theorem update_value_eq {I : Type uI} [DecidableEq I] {A : I → Type uA}
    (a : ∀ i, A i) (i : I) : Function.update a i (a i) = a :=
  Function.update_eq_self_iff.mpr rfl

private theorem eq_product_of_paired_updates {I : Type uI} [Fintype I] [DecidableEq I]
    {A : I → Type uA} {B : I → Type uB}
    (C : (∀ i, A i) → (∀ i, B i) → ℂ) (f : ∀ i, A i → B i → ℂ)
    (a₀ : ∀ i, A i) (b₀ : ∀ i, B i) (h₀ : ∀ i, f i (a₀ i) (b₀ i) = 1)
    (hslice : ∀ i a b, ∃ c : ℂ, ∀ x y,
      C (Function.update a i x) (Function.update b i y) = c * f i x y)
    (a : ∀ i, A i) (b : ∀ i, B i) :
    C a b = C a₀ b₀ * ∏ i, f i (a i) (b i) := by
  let L (p : ∀ i, A i × B i) := C (fun i => (p i).1) (fun i => (p i).2)
  have hL (i : I) (p : ∀ i, A i × B i) :
      ∃ c : ℂ, ∀ q : A i × B i, L (Function.update p i q) = c * f i q.1 q.2 := by
    obtain ⟨c, hc⟩ := hslice i (fun j => (p j).1) (fun j => (p j).2)
    refine ⟨c, fun q => ?_⟩
    exact (congrArg₂ C (map_update (fun _ => Prod.fst) p i q)
      (map_update (fun _ => Prod.snd) p i q)).trans (hc q.1 q.2)
  exact eq_product_of_update L (fun i p => f i p.1 p.2) (fun i => (a₀ i, b₀ i)) h₀ hL
    (fun i => (a i, b i))

variable {F : Type u} [Field F] [NumberField F]

local instance (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- The local general linear group at the indexed real or complex place. -/
abbrev PlaceGroup (n : ℕ) : Index F → Type
  | .inl _ => Langlands.GeneralLinear n ℝ
  | .inr _ => Langlands.GeneralLinear n ℂ

instance placeGroupOne (n : ℕ) (i : Index F) : One (PlaceGroup n i) := by
  cases i <;> exact inferInstance

abbrev PlaceTuple (n : ℕ) := ∀ i : Index F, PlaceGroup n i

/-- The tuple of infinite components of an actual adelic point. -/
def placeComponents (n : ℕ) (g : Points F n) : ∀ i : Index F, PlaceGroup n i
  | .inl v => realComponent F n v g
  | .inr w => complexComponent F n w g

/-- Assemble all the infinite components with identity finite component. -/
def placeTuplePoint (n : ℕ) (g : ∀ i : Index F, PlaceGroup n i) : Points F n :=
  adelicPoint F n (placeGL F n (fun v => g (.inl v), fun w => g (.inr w))) 1

private theorem placeTuplePoint_update_real (n : ℕ) (v : {v : InfinitePlace F // v.IsReal})
    (g : Langlands.GeneralLinear n ℝ) :
    placeTuplePoint n (Function.update (1 : PlaceTuple (F := F) n) (.inl v) g) =
      realPlacePoint F n v g := by
  apply congrArg (fun p => adelicPoint F n (placeGL F n p) 1)
  apply Prod.ext
  · funext w
    change Function.update (1 : PlaceTuple (F := F) n) (.inl v) g (.inl w) =
      (Pi.mulSingle v g : UnipotentClass.RealGL F n) w
    by_cases h : w = v
    · subst w
      rw [Function.update_self, Pi.mulSingle_eq_same]
    · rw [Function.update_of_ne (Sum.inl_injective.ne h), Pi.mulSingle_eq_of_ne h]
      rfl
  · funext w
    change Function.update (1 : PlaceTuple (F := F) n) (.inl v) g (.inr w) = 1
    rw [Function.update_of_ne (by simp)]
    rfl

private theorem placeTuplePoint_update_complex (n : ℕ) (w : {w : InfinitePlace F // w.IsComplex})
    (g : Langlands.GeneralLinear n ℂ) :
    placeTuplePoint n (Function.update (1 : PlaceTuple (F := F) n) (.inr w) g) =
      complexPlacePoint F n w g := by
  apply congrArg (fun p => adelicPoint F n (placeGL F n p) 1)
  apply Prod.ext
  · funext v
    change Function.update (1 : PlaceTuple (F := F) n) (.inr w) g (.inl v) = 1
    rw [Function.update_of_ne (by simp)]
    rfl
  · funext v
    change Function.update (1 : PlaceTuple (F := F) n) (.inr w) g (.inr v) =
      (Pi.mulSingle w g : UnipotentClass.ComplexGL F n) v
    by_cases h : v = w
    · subst v
      rw [Function.update_self, Pi.mulSingle_eq_same]
    · rw [Function.update_of_ne (Sum.inr_injective.ne h), Pi.mulSingle_eq_of_ne h]
      rfl

private theorem infinitePoint_eq_placeTuplePoint {r : ℕ}
    (S : Finset (FinitePlace F)) (g : Points F (r + 1)) :
    infinitePoint S g = placeTuplePoint (r + 1) (placeComponents (r + 1) g) := by
  let n := r + 1
  let z := (UnipotentClass.adelicSplit F n S).symm g
  have hR (v : {v : InfinitePlace F // v.IsReal}) : realComponent F n v g = z.1.1 v := by
    simpa only [z, ContinuousMulEquiv.apply_symm_apply] using
      UnipotentClass.realComponent_adelicSplit F n S z v
  have hC (w : {w : InfinitePlace F // w.IsComplex}) : complexComponent F n w g = z.1.2 w := by
    simpa only [z, ContinuousMulEquiv.apply_symm_apply] using
      UnipotentClass.complexComponent_adelicSplit F n S z w
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  rw [infinitePoint, UnipotentClass.adelicEquiv_adelicSplit]
  change AdelicGL.pair F n ((UnipotentClass.archSplit F n).symm z.1)
      ((Langlands.Global.FiniteAdelicGL.splitAtPlaces F n (· ∈ S)).symm 1) =
    GeneralLinearGroupPoints.adelicEquiv F n
      (adelicPoint F n (placeGL F n (fun v => realComponent F n v g, fun w => complexComponent F n w g)) 1)
  rw [map_one, adelicPoint, MulEquiv.apply_symm_apply, funext hR, funext hC]
  apply congrArg (fun a => AdelicGL.pair F n a 1)
  apply Units.ext
  ext i j
  rw [UnipotentClass.archSplit_symm_apply]
  rfl

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} {T : CuspidalOperatorRealization F r}

local instance : AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F (r + 1)) := Submodule.addCommGroup _
local instance (T : CuspidalOperatorRealization F r) : AddCommGroup T.Space := Submodule.addCommGroup _
local instance (T : CuspidalOperatorRealization F r) (i : Index F) :
    AddCommGroup (T.placeDensityModels.subspace i) := Submodule.addCommGroup _

variable (P : CuspidalSpectralPresentation.{u, uQ} T)
  (hP : HasIrreducibleAdmissibleComponents P) (χ : AddChar (Adeles F) ℂ)

abbrev FiniteTensor :=
  Langlands.RestrictedTensor.Space ℂ (fun v => P.localFactor v) P.tensorExceptional P.reference

/-- The actual global Whittaker coefficient at an infinite tuple on an indicated pure
tensor, with arbitrary finite tensor vector. -/
def tensorWhittaker (a : FiniteTensor P)
    (b : ∀ i : Index F, T.placeDensityModels.subspace i)
    (g : ∀ i : Index F, PlaceGroup (r + 1) i) : ℂ :=
  cuspWhittaker F T χ (P.allPlaceTensorEquiv hP (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b))
    (placeTuplePoint (r + 1) g)

/-- A comparison of the one-place coefficient maps with normalized local models.
Other archimedean arguments and the finite factor may be frozen arbitrarily. -/
structure ModelData where
  model : ∀ i : Index F, (T.placeDensityModels.subspace i : Type u) →ₗ[ℂ] (PlaceGroup (r + 1) i → ℂ)
  normalized : ∀ i, ∃ b, model i b 1 = 1
  slice : ∀ (a : FiniteTensor P) (i : Index F)
    (b : ∀ j : Index F, T.placeDensityModels.subspace j) (g : ∀ j : Index F, PlaceGroup (r + 1) j),
    ∃ c : ℂ, ∀ v : T.placeDensityModels.subspace i, ∀ h : PlaceGroup (r + 1) i,
      tensorWhittaker P hP χ a (Function.update b i v) (Function.update g i h) = c * model i v h

variable {P hP χ} (D : ModelData P hP χ)

private theorem tensorWhittaker_eq_product (a : FiniteTensor P)
    (b₀ : ∀ i : Index F, T.placeDensityModels.subspace i)
    (h₀ : ∀ i, D.model i (b₀ i) 1 = 1)
    (b : ∀ i : Index F, T.placeDensityModels.subspace i) (g : ∀ i : Index F, PlaceGroup (r + 1) i) :
    tensorWhittaker P hP χ a b g =
      tensorWhittaker P hP χ a b₀ 1 * ∏ i : Index F, D.model i (b i) (g i) := by
  exact eq_product_of_paired_updates (tensorWhittaker P hP χ a)
    (fun i v h => D.model i v h) b₀ 1 h₀ (D.slice a) b g

set_option maxHeartbeats 4000000 in
/-- For the chosen normalized finite reference vectors the infinite product has a
single nonzero normalization, independent of the prescribed infinite vectors and points. -/
theorem exists_normalized_product
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1))
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v : S, (ℓ v).val (a₀ v) = 1)
    (Dψ : ModelData P hP ψ.complex) :
    ∃ (b₀ : ∀ i : Index F, T.placeDensityModels.subspace i) (κ : ℂ),
      κ ≠ 0 ∧ (∀ i, Dψ.model i (b₀ i) 1 = 1) ∧
      κ = tensorWhittaker P hP ψ.complex (P.finitePure S hPS a₀) b₀ 1 ∧
      ∀ b g, infiniteResidual S P hP hPS ψ.complex a₀ (PiTensorProduct.tprod ℂ b) g =
        κ * ∏ i : Index F, Dψ.model i (b i) (placeComponents (r + 1) g i) := by
  choose b₀ h₀ using Dψ.normalized
  let κ := tensorWhittaker P hP ψ.complex (P.finitePure S hPS a₀) b₀ 1
  have hprod (b : ∀ i : Index F, T.placeDensityModels.subspace i) (g : Points F (r + 1)) :
      infiniteResidual S P hP hPS ψ.complex a₀ (PiTensorProduct.tprod ℂ b) g =
        κ * ∏ i : Index F, Dψ.model i (b i) (placeComponents (r + 1) g i) := by
    let x : T.Space := P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b)
    have heq := congrArg (cuspWhittaker F T ψ.complex x) (infinitePoint_eq_placeTuplePoint S g)
    exact heq.trans (tensorWhittaker_eq_product Dψ (P.finitePure S hPS a₀) b₀ h₀ b
      (placeComponents (r + 1) g))
  have ha (v : S) : a₀ v ≠ 0 := by
    intro hv
    exact zero_ne_one (by simpa only [hv, map_zero] using ha₀ v)
  have hb (i : Index F) : b₀ i ≠ 0 := by
    intro hi
    exact zero_ne_one (by simpa only [hi, map_zero, Pi.zero_apply] using h₀ i)
  have hx := P.allPlaceTensorEquiv_pure_ne_zero hP (P.finitePure S hPS a₀) b₀
    (P.finitePure_ne_zero S hPS a₀ ha) hb
  obtain ⟨g, _, hg⟩ := exists_infiniteResidual_ne_zero_of_global P S hPS ψ hψ hS hP
    ψv hψv ℓ a₀ ha₀ (PiTensorProduct.tprod ℂ b₀) hx
  refine ⟨b₀, κ, ?_, h₀, rfl, hprod⟩
  intro hκ
  exact hg ((hprod b₀ g).trans (by rw [hκ, zero_mul]))

private def restrictionLinear (χ : AddChar (Adeles F) ℂ)
    (hχ : IsStandardAdditiveCharacter F χ) (i : Index F) : T.Space →ₗ[ℂ] (PlaceGroup (r + 1) i → ℂ) :=
  LinearMap.pi fun g => UnramifiedWhittaker.whittakerFunctional F χ hχ T
    (placeTuplePoint (r + 1) (Function.update (1 : PlaceTuple (F := F) (r + 1)) i g))

set_option maxHeartbeats 4000000 in
private theorem restriction_mem_model_range (hχ : IsStandardAdditiveCharacter F χ)
    (i : Index F) (x : T.Space) :
    restrictionLinear (T := T) χ hχ i x ∈ LinearMap.range (D.model i) := by
  let e := P.allPlaceTensorEquiv hP
  let L := (restrictionLinear (T := T) χ hχ i).comp e.toLinearMap
  let M := LinearMap.range (D.model i)
  have hpure (a : FiniteTensor P) (b : ∀ j : Index F, T.placeDensityModels.subspace j) :
      L (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) ∈ M := by
    let comparison := D.slice a i b (1 : PlaceTuple (F := F) (r + 1))
    let c : ℂ := Classical.choose comparison
    have hc := Classical.choose_spec comparison
    have he := update_value_eq b i
    have hvalue : D.model i (c • b i) = L (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) := by
      funext g
      change D.model i (c • b i) g = tensorWhittaker P hP χ a b
        (Function.update (1 : PlaceTuple (F := F) (r + 1)) i g)
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (he ▸ hc (b i) g).symm
    exact LinearMap.mem_range.mpr ⟨c • b i, hvalue⟩
  have htmul (a : FiniteTensor P) (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) :
      L (a ⊗ₜ[ℂ] t) ∈ M := by
    refine t.induction_on (fun c b => ?_) (fun v w hv hw => ?_)
    · simpa only [TensorProduct.tmul_smul, map_smul] using M.smul_mem c (hpure a b)
    · simpa only [TensorProduct.tmul_add, map_add] using M.add_mem hv hw
  have hall (z : FiniteTensor P ⊗[ℂ] (⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))) :
      L z ∈ M := by
    exact TensorProduct.inductionOn (motive := fun w => L w ∈ M) z htmul
      (fun v w hv hw => by rw [map_add]; exact M.add_mem hv hw)
  have hz : e (e.symm x) = x := e.apply_symm_apply x
  have hm := hall (e.symm x)
  change restrictionLinear (T := T) χ hχ i (e (e.symm x)) ∈ M at hm
  exact hz ▸ hm

omit [CompactSpace (AdeleQuotient F)] in
private theorem finitePoint_eq (n : ℕ) (a : FiniteAdelicGL F n) :
    finitePoint F n a = (GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.ofFinite F n a) := by
  unfold finitePoint adelicPoint
  rw [map_one]
  rfl

/-- A real-place restriction of any global vector is a coefficient in the supplied
model for that place. The finite offset is absorbed by genuine finite translation. -/
theorem exists_model_real (hχ : IsStandardAdditiveCharacter F χ)
    (v : {v : InfinitePlace F // v.IsReal}) (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (hW : IsRealPlaceWhittaker F T χ v W) :
    ∃ b : T.placeDensityModels.subspace (.inl v), D.model (.inl v) b = W := by
  obtain ⟨x, d, rfl⟩ := hW
  let y := T.realization.finiteRepresentation d x
  obtain ⟨b, hb⟩ := restriction_mem_model_range D hχ (.inl v) y
  refine ⟨b, hb.trans (funext fun g => ?_)⟩
  change cuspWhittaker F T χ y
    (placeTuplePoint (r + 1) (Function.update (1 : PlaceTuple (F := F) (r + 1)) (.inl v) g)) =
      cuspWhittaker F T χ x (realPlacePoint F (r + 1) v g * finitePoint F (r + 1) d)
  rw [placeTuplePoint_update_real, finitePoint_eq]
  exact UnramifiedWhittaker.cuspWhittaker_finiteRepresentation F χ T d x _

/-- A complex-place restriction of any global vector is a coefficient in the supplied
model for that place. The finite offset is absorbed by genuine finite translation. -/
theorem exists_model_complex (hχ : IsStandardAdditiveCharacter F χ)
    (v : {v : InfinitePlace F // v.IsComplex}) (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (hW : IsComplexPlaceWhittaker F T χ v W) :
    ∃ b : T.placeDensityModels.subspace (.inr v), D.model (.inr v) b = W := by
  obtain ⟨x, d, rfl⟩ := hW
  let y := T.realization.finiteRepresentation d x
  obtain ⟨b, hb⟩ := restriction_mem_model_range D hχ (.inr v) y
  refine ⟨b, hb.trans (funext fun g => ?_)⟩
  change cuspWhittaker F T χ y
    (placeTuplePoint (r + 1) (Function.update (1 : PlaceTuple (F := F) (r + 1)) (.inr v) g)) =
      cuspWhittaker F T χ x (complexPlacePoint F (r + 1) v g * finitePoint F (r + 1) d)
  rw [placeTuplePoint_update_complex, finitePoint_eq]
  exact UnramifiedWhittaker.cuspWhittaker_finiteRepresentation F χ T d x _

end Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice
