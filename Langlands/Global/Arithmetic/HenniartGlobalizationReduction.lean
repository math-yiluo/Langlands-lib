import Langlands.Global.Arithmetic.HenniartGeneratorRealization
import Langlands.Global.Arithmetic.HenniartCommonBaseRealizationProof
import Langlands.LocalFactor.CommonClosureFactoringBrauer
import Langlands.ClassField.Global.FamilyGaloisOverfield
import Langlands.ClassField.Global.LocalRelativeWeilMapExistenceProof
import Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentationProof
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Henniart's relative globalization from Harris's Proposition 4.8 and its local inputs

Henniart (2000), Théorème 3.1 and §§3.3–3.7, in the relative form
`HenniartGlobalizationStatement`, assuming the Library statements that are still open:
Tate's local restriction formula for induced reciprocity representations, local transfer
reciprocity, the central character comparison, the associated supercuspidal induction and
the existence of normalized local reciprocity families. The implication is the proposition
`HenniartGlobalizationReductionStatement`, proved as `henniartGlobalization_reduction`.
-/

noncomputable section

set_option autoImplicit false

universe uK uQ uW uP

namespace Langlands.Global

open NumberField Langlands.Weil.Local Langlands.Global.CompletionPadic
open Langlands.ClassField.Global Langlands.ClassField.Global.RelativeWeilGroup
open Langlands.LocalFactor.CommonClosure Langlands.VirtualRepresentation
open Langlands.VirtualRepresentation.RelativeGlobal Langlands.Automorphic
open GeneralPosition

/-- A finite extension `M` of a p-adic field has only finitely many finite subextensions. -/
theorem finite_extension_le {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (M : Extension K) :
    Finite {F' : Extension K // F'.field ≤ M.field} := by
  have : CharZero K.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) K.Carrier).injective
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K.Carrier M.field
  have : Finite (IntermediateField K.Carrier M.field) :=
    Field.finite_intermediateField_of_exists_primitive_element K.Carrier M.field ⟨α, hα⟩
  refine Finite.of_injective
    (fun F' : {F' : Extension K // F'.field ≤ M.field} => IntermediateField.restrict F'.2) ?_
  intro a b hab
  have := congrArg IntermediateField.lift hab
  simp only [IntermediateField.lift_restrict] at this
  exact Subtype.ext (Subtype.ext this)

/-- A character of a subgroup `H` that is trivial on `H ∩ N`, for a normal subgroup `N` of
finite index, takes values of modulus one. -/
theorem norm_eq_one_of_trivial_on_finiteIndex {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [N.FiniteIndex] {H : Subgroup G} (η : H →* ℂˣ) (hη : ∀ a : H, (a : G) ∈ N → η a = 1)
    (a : H) : ‖(η a : ℂ)‖ = 1 := by
  have hmem := (N.subgroupOf H).pow_index_mem a
  have h1 : η (a ^ (N.subgroupOf H).index) = 1 := hη _ hmem
  rw [map_pow] at h1
  have h2 : ‖(η a : ℂ)‖ ^ (N.subgroupOf H).index = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Subgroup.FiniteIndex.index_ne_zero).mp h2

/-- One Brauer generator at the common place `v₀`: if a paired-place configuration for `F'`
has place `v₀` and its isomorphism `E_{v₀} ≅ K` agrees with `ι₀` on `E`, then for every
extension `L` of `E_{v₀}` whose Weil group corresponds to `W_{F'}` and every modulus-one
character `η` of `W_L`, the induction `Ind_{W_L} η` is the realization of an element of the
Weil image of witnessed pairs at `v₀`. -/
theorem exists_weilImage_realizeExact_generator
    (hHarris : Harris.Proposition48Statement.{uK, 0, 0, 0, uP})
    (hccre : LocalClassField.CommonClosureReciprocityExistence.{uK})
    (hlir : LocalInducedRestrictionStatement.{uW, 0})
    (hacc : AssociatedCentralCharacterStatement.{0, uW, uP})
    (hasi : AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP})
    (htransfer : LocalTransferReciprocityStatement.{0})
    {c : FundamentalClass.ClassFamily.{0}} (hc : IsArithmeticClassFamily c)
    {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    {F₀ : Type} [Field F₀] [NumberField F₀] [IsCMField F₀] [CompactSpace (AdeleQuotient F₀)]
    (v₀ : FinitePlace F₀) (ι₀ : FiniteCompletion F₀ v₀ ≃+* K.Carrier)
    (hι₀ : letI := K.canonicalTopology; Continuous ι₀)
    (hι₀s : letI := K.canonicalTopology; Continuous ι₀.symm)
    (h : residuePrime v₀ = p)
    (F' : Extension K) {E' Lg : Type} [Field E'] [Field Lg] [NumberField E'] [NumberField Lg]
    [IsCMField E'] [IsCMField Lg] [Algebra F₀ E'] [Algebra F₀ Lg] [Algebra E' Lg]
    (K₀ : IntermediateField ℚ F₀) (P Ps : Harris.PlaceDatum K F' F₀ E' Lg)
    (φ : FiniteCompletion E' P.v' ≃+* F'.field) (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
    (θ : (Lg ≃ₐ[F₀] Lg) ≃*
      ((galoisClosure K F').field ≃ₐ[K.Carrier] (galoisClosure K F').field))
    (hconf : Harris.IsPairedPlaceConfiguration K₀ P Ps φ φs θ) (hPv : P.v = v₀)
    (hPiso : ∀ x : F₀, P.iso (algebraMap F₀ (FiniteCompletion F₀ P.v) x) =
      ι₀ (algebraMap F₀ (FiniteCompletion F₀ v₀) x))
    {𝔼 : Type} [Field 𝔼] [NumberField 𝔼] [Algebra F₀ 𝔼] [Algebra E' 𝔼]
    [IsScalarTower F₀ E' 𝔼] [IsGalois F₀ 𝔼]
    (L : Extension (padicField v₀))
    (hL : ∀ y : localWeilGroup K,
      completionWeilTransport v₀ h K (completionAlgEquivOfContinuous v₀ K h ι₀ hι₀s) y ∈
          weilSubgroup (padicField v₀) L ↔
        y ∈ weilSubgroup K F')
    (η : weilSubgroup (padicField v₀) L →ₜ* ℂˣ) (hη : ∀ a, ‖(η a : ℂ)‖ = 1) :
    ∃ y ∈ weilImage.{0, uW, uP} F₀ 𝔼 c v₀,
      haveI := weilSubgroup_finiteIndex (padicField v₀) L
      LocalWeil.realizeExact (padicField v₀) (LocalWeil.includeUnitary (padicField v₀) y) =
        ExactGrothendieckGroup.continuousInduce (weilSubgroup (padicField v₀) L)
          (weilSubgroup_open _ L) (ExactGrothendieckGroup.characterClass.{0, uW} η) := by
  subst hPv
  have hcont : letI := K.canonicalTopology; Continuous P.iso := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hQ, -⟩ := hconf
    exact (hQ P (List.mem_cons_self ..)).2.1
  have hext := completion_ringHom_ext P.v K ι₀.toRingHom P.iso.toRingHom hι₀ hcont
    (fun x => (hPiso x).symm)
  have hf : letI := (padicFieldAt P.v h).algebra
      ∀ x : FiniteCompletion F₀ P.v,
        (completionAlgEquivOfContinuous P.v K h ι₀ hι₀s).symm x = P.iso x := by
    intro x
    rw [completionAlgEquivOfContinuous_symm_apply]
    exact congrArg (fun g : FiniteCompletion F₀ P.v →+* K.Carrier => g x) hext
  exact exists_weilImage_realizeExact_continuousInduce hHarris hccre
    localRelativeWeilMapExistence hlir cuspidalAllLocalIrreduciblePresentationExistence hacc
    hasi htransfer hc K F' K₀ P Ps φ φs θ hconf h _ hf L hL η hη

/-- **Henniart (2000), Théorème 3.1, relative form, from its open inputs.** Harris (1998),
Proposition 4.8 implies `RelativeGaloisGlobalization`, provided Tate's local restriction
formula, local transfer reciprocity, the central character comparison, the associated
supercuspidal induction and the existence of normalized local reciprocity families. -/
theorem henniartGlobalization_of_inputs
    (hccre : LocalClassField.CommonClosureReciprocityExistence.{uK})
    (hlir : LocalInducedRestrictionStatement.{uW, 0})
    (hacc : AssociatedCentralCharacterStatement.{0, uW, uP})
    (hasi : AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP})
    (htransfer : LocalTransferReciprocityStatement.{0}) :
    HenniartGlobalizationStatement.{uK, uQ, uW, uP} := by
  intro hHarris c hc p _ K Q _ _ q
  have : CharZero K.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) K.Carrier).injective
  have : IsGalois K.Carrier (AlgebraicClosure K.Carrier) := ⟨⟩
  -- An open normal subgroup `U` of the Galois group whose Weil preimage lies in the
  -- closure of the kernel of `q`, and its fixed field `M`.
  obtain ⟨U, hUn, hUo, hUN⟩ := exists_open_normal_le K (factoringKernelClosure K q)
    (factoringKernelClosure_isOpen K q)
  have := hUn
  let Uc : ClosedSubgroup (Field.absoluteGaloisGroup K.Carrier) :=
    ⟨U, U.isClosed_of_isOpen hUo⟩
  have hM : (IntermediateField.fixedField U).fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField Uc
  have : FiniteDimensional K.Carrier (IntermediateField.fixedField U) :=
    (InfiniteGalois.isOpen_iff_finite _).mp (by rw [hM]; exact hUo)
  let M : Extension K := ⟨IntermediateField.fixedField U, inferInstance⟩
  -- The common CM base `F₀`, its place `v₀`, `ι₀ : F₀_{v₀} ≅ K`, and a paired-place
  -- configuration of every subextension `F'` of `M`.
  obtain ⟨F₀, _, _, _, v₀, ι₀, hι₀, hι₀s, hconfs⟩ := henniartCommonBaseRealization p K M
  choose E' Lg iE' iLg nE' nLg cE' cLg aE' aLg aE'Lg K₀ P Ps φ φs θ hconf hPv hPiso
    using hconfs
  have h : residuePrime v₀ = p := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hplaces, -⟩ := hconf M le_rfl
    have hmem := (hplaces (P M le_rfl).v (List.mem_cons_self ..)).1
    rw [hPv M le_rfl] at hmem
    exact residuePrime_eq_of_natCast_mem v₀ hmem
  subst h
  let f := completionAlgEquivOfContinuous v₀ K rfl ι₀ hι₀s
  -- A Galois extension `𝔼` of `F₀` containing every `E'`.
  have : Finite {F' : Extension K // F'.field ≤ M.field} := finite_extension_le K M
  let 𝔼 := familyGaloisOverfield F₀
    (fun i : {F' : Extension K // F'.field ≤ M.field} => E' i.1 i.2)
  refine ⟨F₀, 𝔼.carrier, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, v₀, rfl, f, ?_⟩
  intro _ x hx
  let T := completionWeilTransportEquiv v₀ rfl K f
  -- Brauer induction above `T(W_M)`, transported along `T`.
  obtain ⟨z, hz, hzx⟩ := realizeExact_includeUnitary_mem_map_span.{uK, 0, uW, uQ} K q (padicField v₀) T x hx
  have hspan : Submodule.span ℤ (inducedCharacterClassesAbove.{0, uW} (padicField v₀)
      ((factoringKernelClosure K q).comap
        (T.symm : localWeilGroup (padicField v₀) →* localWeilGroup K))) ≤
      (weilImage.{0, uW, uP} F₀ 𝔼.carrier c v₀).map
        ((LocalWeil.realizeExact (padicField v₀)).comp
          (LocalWeil.includeUnitary (padicField v₀))) := by
    rw [Submodule.span_le]
    rintro _ ⟨L, hNL, η, hηN, rfl⟩
    -- The subextension `F'` of `M` whose Weil group corresponds to `W_L`.
    obtain ⟨F', hF'M, hF'⟩ := exists_extension_eq K U hUo
      ((weilSubgroup (padicField v₀) L).comap
        (T : localWeilGroup K →* localWeilGroup (padicField v₀)))
      (fun w hw => by
        rw [Subgroup.mem_comap]
        apply hNL
        rw [Subgroup.mem_comap]
        simpa using hUN w hw)
    have hL : ∀ y : localWeilGroup K,
        completionWeilTransport v₀ rfl K f y ∈ weilSubgroup (padicField v₀) L ↔
          y ∈ weilSubgroup K F' := by
      intro y
      rw [hF']
      exact Iff.rfl
    have hη : ∀ a, ‖(η a : ℂ)‖ = 1 :=
      norm_eq_one_of_trivial_on_finiteIndex _ η.toMonoidHom hηN
    let := 𝔼.algebraMember ⟨F', hF'M⟩
    have := 𝔼.tower ⟨F', hF'M⟩
    obtain ⟨y, hy, hyη⟩ := exists_weilImage_realizeExact_generator hHarris hccre hlir hacc
      hasi htransfer hc K v₀ ι₀ hι₀ hι₀s rfl F' (K₀ F' hF'M) (P F' hF'M) (Ps F' hF'M)
      (φ F' hF'M) (φs F' hF'M) (θ F' hF'M) (hconf F' hF'M) (hPv F' hF'M) (hPiso F' hF'M)
      (𝔼 := 𝔼.carrier) L hL η hη
    exact ⟨y, hy, hyη⟩
  obtain ⟨y, hy, hyz⟩ := hspan hz
  refine ⟨y, hy, ?_⟩
  rw [← hzx, ← hyz]
  rfl

/-- Internal reduction: the existence of normalized local reciprocity families, Tate's local
restriction formula for induced reciprocity representations, the central character comparison,
the associated supercuspidal induction and local transfer reciprocity imply
`HenniartGlobalizationStatement`. -/
def HenniartGlobalizationReductionStatement : Prop :=
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
    LocalInducedRestrictionStatement.{uW, 0} →
      AssociatedCentralCharacterStatement.{0, uW, uP} →
        AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP} →
          LocalTransferReciprocityStatement.{0} →
            HenniartGlobalizationStatement.{uK, uQ, uW, uP}

/-- The internal reduction holds. -/
theorem henniartGlobalization_reduction :
    HenniartGlobalizationReductionStatement.{uK, uQ, uW, uP} :=
  fun hccre hlir hacc hasi htransfer =>
    henniartGlobalization_of_inputs hccre hlir hacc hasi htransfer

end Langlands.Global
