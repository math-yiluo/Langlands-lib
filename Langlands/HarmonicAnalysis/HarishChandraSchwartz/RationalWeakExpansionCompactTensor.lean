import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCompactDual
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCMapEvaluation

/-! # The actual compact c-family as a tensor product -/

noncomputable section

set_option maxHeartbeats 700000
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped CategoryTheory.MonObj NNReal TensorProduct

namespace Langlands.Plancherel

open Aubert.General Induction

universe uG uV uI

section ProductChart

variable {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H] [SecondCountableTopology H]
  {P M U : Subgroup H} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (d : IsSemidirectDecomposition P M U) (K : OpenSubgroup H)
  (hU : IsClosed (U : Set H)) (hP : IsClosed (P : Set H)) (hK : IsCompact (K : Set H))
  (hPK : ∀ x : H, ∃ p : P, ∃ k : K, x = (p : H) * (k : H))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous d.projection)
  (A : SmoothRep.{0, uG, uV} ℂ M) (z : unramifiedCharacters ν)

omit [LocallyCompactSpace H] [NonarchimedeanGroup H] [SecondCountableTopology H] in
include hK hPK in
private theorem compactTensorQuotient : CompactSpace (LeftQuotient P) :=
  compactSpace_leftQuotient_of_compact_representatives P hK (fun g =>
    let ⟨p, k, h⟩ := hPK g
    ⟨p, p.property, k, k.property, h⟩)

private def normalizedTensorWithCompactQuotient (B : SmoothRep.{0, uG, uV} ℂ M) :
    ((normalizedInductionFunctor d hU).obj B) ⊗[ℂ]
      ((normalizedInductionFunctor d hU).obj B.contragredient) ≃ₗ[ℂ] productInducedCoefficientObject d hU B :=
  letI := compactTensorQuotient K hK hPK
  (normalizedProductInductionTensorEquiv d d hU hU B B.contragredient).toLinearEquiv

local notation "Twisted" => A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)
local notation "κ" => unramifiedNormalizedInductionCompactEquiv d K hU hP hK hPK ν hν hr z A
local notation "κᵛ" => normalizedDualCompactEquiv ν d K hU hP hK hPK hν hr A z
local notation "ρ" => productInducedCompactEquiv ν d K hP hK hν hr hU hPK z A
local notation "J" => normalizedTensorWithCompactQuotient d K hU hK hPK Twisted

private theorem compactProductChart_apply_lifts
    (f : (normalizedInductionFunctor d hU).obj Twisted)
    (g : (normalizedInductionFunctor d hU).obj (Twisted).contragredient) :
    normalizedCompactProductChart ν d K hU hP hK hPK hν hr A z (κ f ⊗ₜ[ℂ] κᵛ g) =
      ρ (J (f ⊗ₜ[ℂ] g)) := by
  change ρ (J (TensorProduct.congr (κ).toLinearEquiv.symm (κᵛ).symm (κ f ⊗ₜ[ℂ] κᵛ g))) = _
  rw [TensorProduct.congr_tmul]
  exact congrArg (fun t => ρ (J t))
    (congrArg₂ (fun v w => v ⊗ₜ[ℂ] w)
      ((κ).toLinearEquiv.symm_apply_apply f) ((κᵛ).symm_apply_apply g))

private theorem compactProductChart_of_tensor
    (E : ((normalizedInductionFunctor d hU).obj Twisted) ⊗[ℂ]
        ((normalizedInductionFunctor d hU).obj (Twisted).contragredient) ≃ₗ[ℂ]
      productInducedCoefficientObject d hU Twisted) (hE : E = J)
    (f : (normalizedInductionFunctor d hU).obj Twisted)
    (g : (normalizedInductionFunctor d hU).obj (Twisted).contragredient) :
    normalizedCompactProductChart ν d K hU hP hK hPK hν hr A z (κ f ⊗ₜ[ℂ] κᵛ g) =
      ρ (E (f ⊗ₜ[ℂ] g)) := by
  rw [hE]
  exact compactProductChart_apply_lifts ν d K hU hP hK hPK hν hr A z f g

private theorem compactProductChart_of_transport
    {B₁ : SmoothRep.{0, uG, uV} ℂ M} (e : B₁.representation.Equiv (Twisted).representation)
    (E : ((normalizedInductionFunctor d hU).obj B₁) ⊗[ℂ]
        ((normalizedInductionFunctor d hU).obj B₁.contragredient) ≃ₗ[ℂ]
      productInducedCoefficientObject d hU B₁)
    (hE : E = normalizedTensorWithCompactQuotient d K hU hK hPK B₁)
    (f : (normalizedInductionFunctor d hU).obj B₁)
    (g : (normalizedInductionFunctor d hU).obj B₁.contragredient) :
    ρ (productInducedCoefficientTransport d hU e (E (f ⊗ₜ[ℂ] g))) =
      normalizedCompactProductChart ν d K hU hP hK hPK hν hr A z
        (κ (normalizedInductionEquivOfEquiv d hU e f) ⊗ₜ[ℂ]
          κᵛ (normalizedInductionEquivOfEquiv d hU (A := B₁.contragredient) (B := (Twisted).contragredient)
            (smoothContragredientEquiv e.symm) g)) := by
  let := compactTensorQuotient K hK hPK
  let v := normalizedInductionEquivOfEquiv d hU e f
  let w := normalizedInductionEquivOfEquiv d hU (A := B₁.contragredient) (B := (Twisted).contragredient)
    (smoothContragredientEquiv e.symm) g
  have h := productInducedCoefficientTransport_tensor d hU e f g
  rw [hE]
  exact (congrArg (fun t => ρ t) h).trans
    (compactProductChart_apply_lifts ν d K hU hP hK hPK hν hr A z v w).symm

end ProductChart

section LinearMaps

variable {V W X Y S T : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]

private theorem tensorBetweenEquivs_apply (e : V ⊗[ℂ] W ≃ₗ[ℂ] S) (f : X ⊗[ℂ] Y ≃ₗ[ℂ] T)
    (a : V →ₗ[ℂ] X) (b : W →ₗ[ℂ] Y) (c : ℂ) (v : V) (w : W) :
    (c • (f.toLinearMap ∘ₗ TensorProduct.map a b ∘ₗ e.symm.toLinearMap)) (e (v ⊗ₜ[ℂ] w)) =
      c • f (a v ⊗ₜ[ℂ] b w) := by
  change c • f (TensorProduct.map a b (e.symm (e (v ⊗ₜ[ℂ] w)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul]

private theorem compactMap_apply_lift (e : V ≃ₗ[ℂ] S) (f : T ≃ₗ[ℂ] W)
    (A : V →ₗ[ℂ] T) (v : V) :
    (f.toLinearMap ∘ₗ A ∘ₗ e.symm.toLinearMap) (e v) = f (A v) :=
  congrArg (fun y => f (A y)) (e.symm_apply_apply v)

private theorem tensorBeforeChart_apply (e : V ⊗[ℂ] W ≃ₗ[ℂ] S) (f : X ⊗[ℂ] Y →ₗ[ℂ] T)
    (a : V →ₗ[ℂ] X) (b : W →ₗ[ℂ] Y) (v : V) (w : W) :
    (f ∘ₗ TensorProduct.map a b ∘ₗ e.symm.toLinearMap) (e (v ⊗ₜ[ℂ] w)) = f (a v ⊗ₜ[ℂ] b w) := by
  change f (TensorProduct.map a b (e.symm (e (v ⊗ₜ[ℂ] w)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul]

omit [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] in
private theorem equal_on_lifted_tensorChart (e : V ⊗[ℂ] W ≃ₗ[ℂ] S)
    (f : X → V) (g : Y → W) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (a b : S →ₗ[ℂ] T) (h : ∀ v w, a (e (f v ⊗ₜ[ℂ] g w)) = b (e (f v ⊗ₜ[ℂ] g w))) : a = b := by
  have he : a ∘ₗ e.toLinearMap = b ∘ₗ e.toLinearMap := by
    apply TensorProduct.ext'
    intro v w
    obtain ⟨v, rfl⟩ := hf v
    obtain ⟨w, rfl⟩ := hg w
    exact h v w
  apply LinearMap.ext
  intro s
  obtain ⟨t, rfl⟩ := e.surjective s
  exact congrArg (fun q : V ⊗[ℂ] W →ₗ[ℂ] T => q t) he

end LinearMaps
section TransportTensor

variable {V W X Y S T U V' W' : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

private theorem compactTensor_map_apply
    (s : V ⊗[ℂ] W ≃ₗ[ℂ] S) (t : X ⊗[ℂ] Y ≃ₗ[ℂ] T)
    (a : V →ₗ[ℂ] X) (b : W →ₗ[ℂ] Y) (e : T →ₗ[ℂ] U) (c : ℂ)
    (κ : S ≃ₗ[ℂ] V') (ρ : U ≃ₗ[ℂ] W')
    (J : S →ₗ[ℂ] T) (J' : S →ₗ[ℂ] U) (Jc : V' →ₗ[ℂ] W')
    (hJ : J = c • (t.toLinearMap ∘ₗ TensorProduct.map a b ∘ₗ s.symm.toLinearMap)) (hJ' : J' = e ∘ₗ J)
    (hJc : Jc = ρ.toLinearMap ∘ₗ J' ∘ₗ κ.symm.toLinearMap)
    (v : V) (w : W) (xc : V') (yc : W')
    (hx : xc = κ (s (v ⊗ₜ[ℂ] w))) (hy : ρ (e (t (a v ⊗ₜ[ℂ] b w))) = yc) :
    Jc xc = c • yc := by
  rw [hx, hJc, compactMap_apply_lift, hJ', LinearMap.comp_apply, hJ,
    tensorBetweenEquivs_apply, map_smul, map_smul, hy]

end TransportTensor

section FixedTensorCharts

variable {V W X Y Y' S T V' W' : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Y'] [Module ℂ Y'] [AddCommGroup S] [Module ℂ S]
  [AddCommGroup T] [Module ℂ T]

private theorem replaceTensorOutputs (e : X ⊗[ℂ] Y' ≃ₗ[ℂ] T) (c : ℂ)
    {a a' : X} {b b' : Y'} {v : T} (h : v = c • e (a ⊗ₜ[ℂ] b)) (ha : a = a') (hb : b = b') :
    v = c • e (a' ⊗ₜ[ℂ] b') :=
  h.trans (congrArg (fun t => c • e t) (congrArg₂ (fun x y => x ⊗ₜ[ℂ] y) ha hb))

private theorem equal_operator_on_tensor_charts
    (s s' : V ⊗[ℂ] W ≃ₗ[ℂ] S) (t t' : X ⊗[ℂ] Y' ≃ₗ[ℂ] T)
    (f : V' → V) (g : W' → W) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (A : S →ₗ[ℂ] T) (a : V →ₗ[ℂ] X) (b : W →ₗ[ℂ] Y) (d : Y → Y') (U : X ⊗[ℂ] Y →ₗ[ℂ] T) (c : ℂ)
    (hs : s = s') (ht : t = t') (hU : ∀ v w, U (v ⊗ₜ[ℂ] w) = c • t' (v ⊗ₜ[ℂ] d w))
    (h : ∀ v w, A (s' (f v ⊗ₜ[ℂ] g w)) = c • t (a (f v) ⊗ₜ[ℂ] d (b (g w)))) :
    A = U ∘ₗ TensorProduct.map a b ∘ₗ s.symm.toLinearMap := by
  refine equal_on_lifted_tensorChart s f g hf hg A _ (fun v w => ?_)
  rw [tensorBeforeChart_apply, hU, ← ht]
  exact (congrArg (fun e : V ⊗[ℂ] W ≃ₗ[ℂ] S => A (e (f v ⊗ₜ[ℂ] g w))) hs).trans (h v w)

end FixedTensorCharts

end Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.WeakExpansion


universe u uV

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

attribute [local instance] cFamilyAmbientAffine cFamilyLeviAffineHom cFamilyLeviAffine cFamilyLeviFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)

set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul
set_option hygiene false in
local notation "eM" => leviRationalPointHomeomorph i ν I
set_option hygiene false in
local notation "Φ" => unramifiedCharactersHomeomorph eM ν₀

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "L" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "dM" => isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)
set_option hygiene false in
local notation "uM" => isClosed_standardUnipotentPoints i ν (rootSet i ν I)
set_option hygiene false in
local notation "pM" => isClosed_standardParabolicPoints_rootSet hG hi hν I
set_option hygiene false in
local notation "fM" => factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
set_option hygiene false in
local notation "rM" => continuous_projection_standard hG hi hν (rootSet_subset i ν I) _
set_option hygiene false in
local notation "cM" => continuous_leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "dL" => decomposition χs
set_option hygiene false in
local notation "uL" => radical_isClosed χs
set_option hygiene false in
local notation "pL" => parabolic_isClosed χs
set_option hygiene false in
local notation "rL" => projection_continuous χs
set_option hygiene false in
local notation "cL" => DynamicInducedOrbit.leviNormCharacters_continuous χs
set_option hygiene false in
local notation "νL" => leviNormCharacters χs
set_option hygiene false in
local notation "σ" => lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn
set_option hygiene false in
local notation "α₊" => outerCentralizer_pos hG hi hν I' hζ'
set_option hygiene false in
local notation "α₋" => outerCentralizer_neg hG hi hν I' hζ'
set_option hygiene false in
local notation "X" => unramifiedCharacters ν₀
set_option hygiene false in
local notation "Y" => unramifiedCharacters νM
set_option hygiene false in
local notation "χL" => unramifiedCharacters νL
set_option hygiene false in
local notation "λγ" => ((RationalDynamicSource.gammaReal (CommGroupScheme.groupHom ζ' ≫ i) K hK : ℂ)⁻¹)

variable (A : SmoothRep.{0, u, uV} ℂ 𝐌)

set_option hygiene false in
local notation "Aₛ" => SmoothRep.pullback (eₛ).symm A
set_option hygiene false in
local notation "B(" z ")" => A.twist (z).val.toMonoidHom (unramifiedCharacter_isOpen_ker νM z)
set_option hygiene false in
local notation "Bᵛ(" z ")" => A.contragredient.twist (z).val.toMonoidHom (unramifiedCharacter_isOpen_ker νM z)
set_option hygiene false in
local notation "Bₛ(" z ")" => SmoothRep.pullback (eₛ).symm (B(z))
set_option hygiene false in
local notation "Bₛ'(" z ")" => (Aₛ).twist (z).val.toMonoidHom (unramifiedCharacter_isOpen_ker νL z)
set_option hygiene false in
local notation "kₛ(" z ")" => twistPullbackEquiv hG hi hν I I' hζ n hn A z
set_option hygiene false in
local notation "kᵛₛ(" z ")" => twistPullbackEquiv hG hi hν I I' hζ n hn A.contragredient z
set_option hygiene false in
local notation "D" => cDomain hG hi hν I I' hζ hζ' n hn K hK A
set_option hygiene false in
local notation "D₊" => cFactorConvergenceRegion hG hi hν I I' hζ n hn ζ' α₊ K hK A
set_option hygiene false in
local notation "D₋" => cFactorConvergenceRegion hG hi hν I I' hζ n hn (-ζ') α₋ K hK A.contragredient

variable (K' : OpenSubgroup (rationalPoints L)) (hK' : IsCompact (K' : Set (rationalPoints L)))
  (hPK' : ∀ g : rationalPoints L, ∃ p : DynamicOppositeStandardIntertwining.parabolic χs,
    ∃ k : K', g = (p : rationalPoints L) * (k : rationalPoints L))

set_option hygiene false in
local notation "CS" => CompactInductionPicture dM K A
set_option hygiene false in
local notation "CSᵛ" => CompactInductionPicture dM K A.contragredient
set_option hygiene false in
local notation "CT" => CompactInductionPicture dL K' (Aₛ)
set_option hygiene false in
local notation "CTᵛ" => CompactInductionPicture dL K' (SmoothRep.pullback (eₛ).symm A.contragredient)
set_option hygiene false in
local notation "chartS" => normalizedCompactProductChart νM dM K uM pM hK fM cM rM A
set_option hygiene false in
local notation "chartT" => normalizedCompactProductChart νL dL K' uL pL hK' hPK' cL rL (Aₛ)
set_option hygiene false in
local notation "dbase" => SmoothRep.equivOfIso (contragredientPullbackIso (eₛ).symm A).symm

set_option hygiene false in
local notation "κS(" z ")" => unramifiedNormalizedInductionCompactEquiv dM K uM pM hK fM νM cM rM z A
set_option hygiene false in
local notation "κSᵛ(" z ")" => normalizedDualCompactEquiv νM dM K uM pM hK fM cM rM A z
set_option hygiene false in
local notation "κT(" z ")" => unramifiedNormalizedInductionCompactEquiv dL K' uL pL hK' hPK' νL cL rL z (Aₛ)
set_option hygiene false in
local notation "κTᵛ(" z ")" => normalizedDualCompactEquiv νL dL K' uL pL hK' hPK' cL rL (Aₛ) z
set_option hygiene false in
local notation "ρS(" z ")" => productInducedCompactEquiv νM dM K pM hK cM rM uM fM z A
set_option hygiene false in
local notation "ρT(" z ")" => productInducedCompactEquiv νL dL K' pL hK' cL rL uL hPK' z (Aₛ)
set_option hygiene false in
local notation "JS(" z ")" => (cMapSourceTensor hG hi hν I K hK hPK (B(z))).toLinearEquiv
set_option hygiene false in
local notation "JT₀(" z ")" => (cMapTargetTensor hG hi hν I I' hζ n hn hK' hPK' (B(z))).toLinearEquiv
set_option hygiene false in
local notation "JT(" z ")" => normalizedTensorWithCompactQuotient dL K' uL hK' hPK' (Bₛ'(z))

set_option hygiene false in
local notation "F₊(" z ")" => cFactor hG hi hν I I' hζ n hn ζ' α₊ K hK hCST (B((z).val)) (z).property.1
set_option hygiene false in
local notation "FD(" z ")" => cDualFactor hG hi hν I I' hζ hζ' n hn K hK hCST (B((z).val)) (z).property.2
set_option hygiene false in
local notation "kT(" z ")" => normalizedInductionEquivOfEquiv dL uL (kₛ(z))
set_option hygiene false in
local notation "kTᵛ(" z ")" => normalizedInductionEquivOfEquiv dL uL (smoothContragredientEquiv (kₛ(z)).symm)
set_option hygiene false in
local notation "CMAP(" z ")" => cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' (B((z).val)) (z).property
set_option hygiene false in
local notation "CFAM(" z ")" => cFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A z
set_option hygiene false in
local notation "CFC(" z ")" => cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A z

private theorem cMapSourceTensor_eq_chart (z : Y) :
    JS(z) = normalizedTensorWithCompactQuotient dM K uM hK fM (B(z)) := by
  simp only [cMapSourceTensor, normalizedTensorWithCompactQuotient]

private theorem cMapTargetTensor_eq_chart (z : Y) :
    JT₀(z) = normalizedTensorWithCompactQuotient dL K' uL hK' hPK' (Bₛ(z)) := by
  simp only [cMapTargetTensor, normalizedTensorWithCompactQuotient]

set_option maxHeartbeats 210000 in
set_option linter.defProp false in
private def cCompactTensorSourceValue_eq (z : D)
    (f : (normalizedInductionFunctor dM uM).obj (B(z.val)))
    (g : (normalizedInductionFunctor dM uM).obj (B(z.val)).contragredient) :=
  let ht := cMapSourceTensor_eq_chart hG hi hν I K hK hPK A z.val
  compactProductChart_of_tensor νM dM K uM pM hK fM cM rM A z.val (JS(z.val)) ht f g

set_option maxHeartbeats 210000 in
set_option linter.defProp false in
private def cCompactTensorTargetValue_eq (z : D)
    (f : (normalizedInductionFunctor dM uM).obj (B(z.val)))
    (g : (normalizedInductionFunctor dM uM).obj (B(z.val)).contragredient) :=
  let e : (Bₛ(z.val)).representation.Equiv (Bₛ'(σ z.val)).representation := kₛ(z.val)
  let v : (normalizedInductionFunctor dL uL).obj (Bₛ(z.val)) := F₊(z) f
  let w : (normalizedInductionFunctor dL uL).obj (Bₛ(z.val)).contragredient := FD(z) g
  let ht := cMapTargetTensor_eq_chart hG hi hν I I' hζ n hn A K' hK' hPK' z.val
  compactProductChart_of_transport νL dL K' uL pL hK' hPK' cL rL (Aₛ)
    (σ z.val) (B₁ := Bₛ(z.val)) e (JT₀(z.val)) ht v w

set_option maxHeartbeats 210000 in
set_option linter.defProp false in
private def cCompactFamily_on_pure_tensor (z : D)
    (f : (normalizedInductionFunctor dM uM).obj (B(z.val)))
    (g : (normalizedInductionFunctor dM uM).obj (B(z.val)).contragredient) :=
  let s := JS(z.val)
  let t := JT₀(z.val)
  let a := F₊(z)
  let b := FD(z)
  let e := productInducedCoefficientTransport dL uL (kₛ(z.val))
  let hJ := cMap_eq_tensor hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' (B(z.val)) z.property
  let hJ' := cFamily_eq_transport hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A z
  let hJc := cCompactFamily_eq_composite hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A z
  let hx := cCompactTensorSourceValue_eq hG hi hν I I' hζ hζ' n hn K hK hPK A z f g
  let hy := cCompactTensorTargetValue_eq hG hi hν I I' hζ hζ' n hn K hK hCST A K' hK' hPK' z f g
  compactTensor_map_apply (V' := ProductInducedCompactPicture dM K A)
    (W' := ProductInducedCompactPicture dL K' (Aₛ))
    s t a b e.toLinearMap λγ (ρS(z.val)).toLinearEquiv (ρT(σ z.val)).toLinearEquiv
    (CMAP(z)) (CFAM(z)) (CFC(z)) hJ hJ' hJc f g _ _ hx hy

set_option hygiene false in
local notation "δ" => compactInductionPictureEquiv dL K' dbase
set_option hygiene false in
local notation "Fplus" => cFactorOnCompact hG hi hν I I' hζ n hn ζ' α₊ K hK hPK hCST A K' hK' hPK'
set_option hygiene false in
local notation "Fminus" => cFactorOnCompact hG hi hν I I' hζ n hn (-ζ') α₋ K hK hPK hCST A.contragredient K' hK' hPK'
set_option hygiene false in
local notation "dconv" => cFactorDualConvergence hG hi hν I I' hζ hζ' n hn K hK A
set_option hygiene false in
local notation "FS" => cCompactSourceChart hG hi hν I K hK hPK A
set_option hygiene false in
local notation "FT" => cCompactTargetMap hG hi hν I I' hζ (ζ' := ζ') n hn K hK A K' hK' hPK'

set_option linter.defProp false in
private def cSignedCompact_on_tensor (x : X) (hx : Φ x ∈ D)
    (f : (normalizedInductionFunctor dM uM).obj (B(Φ x)))
    (g : (normalizedInductionFunctor dM uM).obj (B(Φ x)).contragredient) :=
  let r := chartT (σ (Φ x))
  let he := cCompactFamily_on_pure_tensor hG hi hν I I' hζ hζ' n hn K hK hCST hPK A K' hK' hPK'
    ⟨Φ x, hx⟩ f g
  let ha := cFactorPlus_on_lift hG hi hν I I' hζ hζ' n hn K hK hCST hPK A K' hK' hPK' x hx f
  let hb := cFactorMinus_on_lift hG hi hν I I' hζ hζ' n hn K hK hCST hPK A K' hK' hPK' x hx g
  replaceTensorOutputs r λγ he ha.symm hb.symm

set_option maxHeartbeats 220000 in
set_option linter.defProp false in
private def cCompactFamilyTensor_proof (x : X) (hx : Φ x ∈ D) :=
  let z : D := ⟨Φ x, hx⟩
  let e := FS
  let t := FT
  let a := Fplus ⟨x, hx.1⟩
  let b := Fminus ⟨x⁻¹, dconv x hx⟩
  let r := chartT (σ (Φ x))
  let hS := normalizedCompactProductChart_eq νM dM K uM pM hK fM cM rM A 1 (Φ x)
  let hT := normalizedCompactProductChart_eq νL dL K' uL pL hK' hPK' cL rL (Aₛ) (σ (Φ x)) 1
  let ht := cCompactTargetMap_tmul hG hi hν I I' hζ (ζ' := ζ') n hn K hK A K' hK' hPK'
  let he := cSignedCompact_on_tensor hG hi hν I I' hζ hζ' n hn K hK hCST hPK A K' hK' hPK' x hx
  let s₁ := κS(Φ x)
  let s₂ := κSᵛ(Φ x)
  let d := δ
  equal_operator_on_tensor_charts e (chartS (Φ x)) r (chartT 1)
    (fun v => s₁ v) (fun w => s₂ w) s₁.surjective s₂.surjective (CFC(z)) a b (fun w => d w) t λγ hS hT ht
    (fun v w => by
      have hh := he v w
      refine Eq.trans (α := ProductInducedCompactPicture dL K' (Aₛ)) ?_ (Eq.trans hh ?_)
      · simp only [z, s₁, s₂, Subtype.coe_mk]
      · simp only [a, b, r, d, s₁, s₂])

/-- The published compact c-map is the tensor of the actual signed compact factors,
read through the fixed source and target maps. The negative factor uses the inverse parameter. -/
theorem cCompactFamily_eq_tensor (x : X) (hx : Φ x ∈ D) :
    CFC((⟨Φ x, hx⟩ : D)) = FT ∘ₗ TensorProduct.map (Fplus ⟨x, hx.1⟩)
      (Fminus ⟨x⁻¹, dconv x hx⟩) ∘ₗ (FS).symm.toLinearMap :=
  cCompactFamilyTensor_proof hG hi hν I I' hζ hζ' n hn K hK hCST hPK A K' hK' hPK' x hx

end Langlands.HarishChandraSchwartz.WeakExpansion
