import Langlands.Global.AdelicIntertwiningElementaryChainStatement
import Langlands.Global.ImaginaryAxisCoordinates
import Langlands.GroupScheme.Rational.LanglandsCharacterRestriction
import Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof
import Langlands.Representation.Plancherel.ParabolicRootCone
import Langlands.Global.AdelicEisensteinParameterDecay
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Rational.ReflectionNegation

/-! # Root forms of the standard parabolics of a family

For a standard parabolic family, the root form `x ↦ B(x|_{A_J}, (γ ∘ f_J))` on `X^*(P_J) ⊗ ℝ`
is `x ↦ B_T(x|_T, γ)` for the Weyl-invariant form `B_T` of the maximal split torus. For a
simple root `α ∉ J` and `L = J ∪ {α}`, every element of the kernel of the root form of
`α ∘ f_J` on `X^*(P_J) ⊗_ℤ ℝ` is the restriction of an element of `X^*(P_L) ⊗_ℤ ℝ`, and
likewise for complex parameters with `X^*(P_L) ⊗_ℤ ℂ`. Root forms are transported by the Weyl
parameter maps of normalizer representatives.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Plancherel

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem restrictReal_comp_apply {H₁ H₂ H₃ : GroupScheme (Spec (CommRingCat.of F))}
    (g : H₁ ⟶ H₂) (f : H₂ ⟶ H₃) (x : ℝ ⊗[ℤ] rationalCharacters H₃) :
    rationalCharacterRestrictReal (g ≫ f) x =
      rationalCharacterRestrictReal g (rationalCharacterRestrictReal f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s χ =>
    simp only [rationalCharacterRestrictReal_tmul, characterRestrict_comp, AddMonoidHom.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restriction of real parameters of `P_J` to the maximal split torus of the family. -/
def torusRestrictReal (J : StandardIndex F G fam.i fam.ν) :
    RealCharacterParameter F (fam.P J) →ₗ[ℝ] Vstar fam.T :=
  rationalCharacterRestrictReal (fam.torus J ≫ fam.l J)

omit [NumberField F] in
/-- The split component of `M_J` is the restriction of the maximal split torus. -/
theorem splitComponent_comp_levi (J : StandardIndex F G fam.i fam.ν) :
    fam.a J ≫ fam.l J = CommGroupScheme.groupHom (fam.f J) ≫ fam.torus J ≫ fam.l J := by
  have hp : Mono (fam.p J).hom.hom := by
    let := (fam.isCompatible J).parabolic.isClosedSubgroup.mono
    exact Over.mono_of_mono_left _
  have : Mono (fam.p J) := (Grp.forget _).mono_of_mono_map (f := fam.p J) hp
  apply (cancel_mono (fam.p J)).mp
  simp only [Category.assoc, fam.torus_comp]
  exact (fam.isCompatible J).factor_comp.symm

omit [NumberField F] in
/-- Restriction of real parameters of `P_J` to the split component factors through the maximal
split torus. -/
theorem realParameterRestriction_eq (J : StandardIndex F G fam.i fam.ν)
    (x : RealCharacterParameter F (fam.P J)) :
    realParameterRestriction (fam.a J ≫ fam.l J) x =
      rationalCharacterRestrictReal (CommGroupScheme.groupHom (fam.f J))
        (fam.torusRestrictReal J x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s χ =>
    change s ⊗ₜ[ℤ] characterRestrict (fam.a J ≫ fam.l J) χ =
      s ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom (fam.f J))
        (characterRestrict (fam.torus J ≫ fam.l J) χ)
    rw [fam.splitComponent_comp_levi J, ← AddMonoidHom.comp_apply, ← characterRestrict_comp]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restriction of real parameters of `P_J` to the maximal split torus is injective. -/
theorem torusRestrictReal_injective (J : StandardIndex F G fam.i fam.ν) :
    Function.Injective (fam.torusRestrictReal J) := by
  intro x y h
  apply realParameterRestriction_splitComponent_injective (fam.rootPresentation J)
  rw [fam.realParameterRestriction_eq, fam.realParameterRestriction_eq, h]

omit [NumberField F] in
/-- The real characters of `P_J` restrict to the coroot annihilator of `J`. -/
theorem torusRestrictReal_mem_corootAnnihilator (J : StandardIndex F G fam.i fam.ν)
    (x : RealCharacterParameter F (fam.P J)) :
    fam.torusRestrictReal J x ∈ corootAnnihilator fam.i fam.coroots J.val := by
  have hc := fam.isCompatible J
  have hjc : IsClosedSubgroup (fam.l J ≫ fam.p J) :=
    hc.levi.isClosedSubgroup.comp hc.parabolic.isClosedSubgroup
  let : IsClosedImmersion (fam.l J ≫ fam.p J).hom.hom.left := hjc
  have hrep : (standardLevi fam.i fam.ν J.val).IsRepresentedBy (fam.l J ≫ fam.p J) :=
    ⟨Over.mono_of_mono_left _, hc.levi_eq⟩
  have hrange := standardLeviCharacterAnnihilator F G fam.connectedReductive fam.T fam.i
    fam.maximalSplit fam.ν fam.generic J.val J.property (fam.M J) (fam.l J ≫ fam.p J) hjc hrep
    (fam.torus J) (fam.torus_comp J) fam.coroots
  rw [← hrange]
  refine ⟨rationalCharacterRestrictReal (fam.l J) x, ?_⟩
  change ((rationalCharacterRestrictReal (fam.torus J)).comp
    (rationalCharacterRestrictReal (fam.l J))) x = rationalCharacterRestrictReal _ x
  congr 1
  apply TensorProduct.AlgebraTensorModule.ext
  intro s χ
  rfl

omit [NumberField F] in
/-- The restriction of real characters of `M_J` to the maximal split torus has image the coroot
annihilator of `J`. -/
theorem range_restrictReal_torus (J : StandardIndex F G fam.i fam.ν) :
    LinearMap.range (rationalCharacterRestrictReal (fam.torus J)) =
      corootAnnihilator fam.i fam.coroots J.val := by
  have hc := fam.isCompatible J
  have hjc : IsClosedSubgroup (fam.l J ≫ fam.p J) :=
    hc.levi.isClosedSubgroup.comp hc.parabolic.isClosedSubgroup
  let : IsClosedImmersion (fam.l J ≫ fam.p J).hom.hom.left := hjc
  have hrep : (standardLevi fam.i fam.ν J.val).IsRepresentedBy (fam.l J ≫ fam.p J) :=
    ⟨Over.mono_of_mono_left _, hc.levi_eq⟩
  exact standardLeviCharacterAnnihilator F G fam.connectedReductive fam.T fam.i
    fam.maximalSplit fam.ν fam.generic J.val J.property (fam.M J) (fam.l J ≫ fam.p J) hjc hrep
    (fam.torus J) (fam.torus_comp J) fam.coroots

omit [NumberField F] in
/-- The maximal split torus factors compatibly through nested standard parabolics. -/
theorem torus_comp_factor {J L : StandardIndex F G fam.i fam.ν} (e : fam.P J ⟶ fam.P L)
    (he : e ≫ fam.p L = fam.p J) :
    fam.torus J ≫ fam.l J ≫ e = fam.torus L ≫ fam.l L := by
  have hp : Mono (fam.p L).hom.hom := by
    let := (fam.isCompatible L).parabolic.isClosedSubgroup.mono
    exact Over.mono_of_mono_left _
  have : Mono (fam.p L) := (Grp.forget _).mono_of_mono_map (f := fam.p L) hp
  apply (cancel_mono (fam.p L)).mp
  simp only [Category.assoc, he, fam.torus_comp]

variable [Fintype (relativeWeylGroup fam.i)]

/-- The Weyl-invariant positive form of the maximal split torus of the family. -/
abbrev torusForm : LinearMap.BilinForm ℝ (Vstar fam.T) :=
  relativeWeylInvariantForm fam.i fam.maximalSplit.isSplitSubtorus.1

omit [NumberField F] in
/-- The form `torusForm` is a Weyl-invariant inner product. -/
theorem isWeylInvariantInnerProduct_torusForm :
    IsWeylInvariantInnerProduct fam.i fam.torusForm :=
  ⟨relativeWeylInvariantForm_symm fam.i _, fun _ => relativeWeylInvariantForm_pos fam.i _,
    relativeWeylInvariantForm_invariant fam.i _⟩

omit [NumberField F] [Fintype (relativeWeylGroup fam.i)] in
/-- The kernel of restriction from the maximal split torus to the split component of `M_J` is
the real span of `J`. -/
theorem ker_restrictReal_splitComponent (J : StandardIndex F G fam.i fam.ν) :
    LinearMap.ker (rationalCharacterRestrictReal (CommGroupScheme.groupHom (fam.f J))) =
      Submodule.span ℝ ((fun α : characterLattice fam.T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J.val) := by
  have hc := fam.isCompatible J
  have hjc : IsClosedSubgroup (fam.l J ≫ fam.p J) :=
    hc.levi.isClosedSubgroup.comp hc.parabolic.isClosedSubgroup
  let : IsClosedImmersion (fam.l J ≫ fam.p J).hom.hom.left := hjc
  have hrep : (standardLevi fam.i fam.ν J.val).IsRepresentedBy (fam.l J ≫ fam.p J) :=
    ⟨Over.mono_of_mono_left _, hc.levi_eq⟩
  obtain ⟨_, f', hf', _, _, himage, _⟩ :=
    (standardLeviCentralDirections.2 F G fam.connectedReductive fam.T fam.i fam.maximalSplit
      fam.ν fam.generic J.val J.property (fam.M J) (fam.l J ≫ fam.p J) hjc hrep).2
      (fam.A J) (fam.a J) hc.splitComponent
  have hff : f' = fam.f J := eq_of_groupHom_comp_eq fam.i (fam.l J ≫ fam.p J) hf' hc.factor_comp
  subst hff
  exact ker_restrictReal_eq_rootSpan_of_range hc.splitComponent.1.1.1
    fam.maximalSplit.isSplitSubtorus.1 (fam.f J) J.val himage

omit [NumberField F] in
/-- The real characters of `P_J`, restricted to the maximal split torus, are orthogonal to the
kernel of restriction to the split component. -/
theorem torusRestrictReal_mem_orthogonal (J : StandardIndex F G fam.i fam.ν)
    (x : RealCharacterParameter F (fam.P J)) :
    fam.torusRestrictReal J x ∈ fam.torusForm.orthogonal
      (LinearMap.ker (rationalCharacterRestrictReal (CommGroupScheme.groupHom (fam.f J)))) := by
  rw [fam.ker_restrictReal_splitComponent J, ← corootAnnihilator_eq_orthogonal fam.i fam.coroots
    fam.torusForm fam.isWeylInvariantInnerProduct_torusForm J.val
    (fun α hα => (J.property hα).1.1)]
  exact fam.torusRestrictReal_mem_corootAnnihilator J x

variable [∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left]

/-- **The root forms of a family.** For a character `beta` of the maximal split torus, the root form
of `beta ∘ f_J` on `X^*(P_J) ⊗ ℝ` is `x ↦ B_T(x|_T, beta)`. -/
theorem realRootFunctional_eq (J : StandardIndex F G fam.i fam.ν) (beta : characterLattice fam.T)
    (x : RealCharacterParameter F (fam.P J)) :
    (fam.rootPresentation J).realRootFunctional
        (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1
        fam.maximalSplit.isSplitSubtorus.1 (fam.f J ≫ beta) x =
      fam.torusForm (fam.torusRestrictReal J x) ((1 : ℝ) ⊗ₜ[ℤ] beta) := by
  set hA := (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1
  set hT := fam.maximalSplit.isSplitSubtorus.1
  set res := rationalCharacterRestrictReal (CommGroupScheme.groupHom (fam.f J))
  set BA := weylInducedCharacterForm hA hT (fam.f J) fam.i
  set L := weylCharacterRestrictionLift hA hT (fam.f J) fam.i
  have hcomp := weylInducedCharacterForm_compatible hA hT (fam.f J) fam.i
  have hBA : ∀ u v, BA u v = BA v u := fun u v =>
    (weylInducedCharacterForm_symm hA hT (fam.f J) fam.i).eq u v
  have hBT : ∀ u v, fam.torusForm u v = fam.torusForm v u :=
    relativeWeylInvariantForm_symm fam.i hT
  set xT := fam.torusRestrictReal J x
  set g : Vstar fam.T := (1 : ℝ) ⊗ₜ[ℤ] beta
  have hlhs : (fam.rootPresentation J).realRootFunctional hA hT (fam.f J ≫ beta) x =
      BA (res xT) (res g) := by
    change BA (realParameterRestriction (fam.a J ≫ fam.l J) x) ((1 : ℝ) ⊗ₜ[ℤ] (fam.f J ≫ beta)) = _
    rw [fam.realParameterRestriction_eq]
    rfl
  have hker : g - L (res g) ∈ LinearMap.ker res := by
    rw [LinearMap.mem_ker, map_sub, hcomp.1, sub_self]
  have horth := fam.torusRestrictReal_mem_orthogonal J x
  have h0 : fam.torusForm xT (g - L (res g)) = 0 := by
    rw [hBT]
    exact horth _ hker
  rw [map_sub] at h0
  rw [hlhs, sub_eq_zero.mp h0, hBT, hcomp.2, hBA]

/-- **Kernel of a simple root form.** Let `L = J ∪ {α}` for a simple root `α`, and `e : P_J → P_L`
the inclusion. A real parameter of `P_J` on which the root form of `α ∘ f_J` vanishes is the
restriction of a real parameter of `P_L`. -/
theorem exists_restrictReal_of_realRootFunctional_eq_zero {J L : StandardIndex F G fam.i fam.ν}
    {α : characterLattice fam.T} (hα : α ∈ simpleRelativeRoots fam.i fam.ν)
    (hL : L.val = insert α J.val) (e : fam.P J ⟶ fam.P L) (he : e ≫ fam.p L = fam.p J)
    {x : RealCharacterParameter F (fam.P J)}
    (hx : (fam.rootPresentation J).realRootFunctional
        (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1
        fam.maximalSplit.isSplitSubtorus.1 (fam.f J ≫ α) x = 0) :
    ∃ y : RealCharacterParameter F (fam.P L), rationalCharacterRestrictReal e y = x := by
  set xT := fam.torusRestrictReal J x
  have hB := fam.isWeylInvariantInnerProduct_torusForm
  rw [fam.realRootFunctional_eq] at hx
  have hαr : α ∈ relativeRoots fam.i := hα.1.1
  have hcor : pair fam.T xT ((1 : ℝ) ⊗ₜ[ℤ] fam.coroots.coroot ⟨α, hαr⟩) = 0 :=
    (fam.coroots.coroot_eq_zero_iff fam.i fam.torusForm hB ⟨α, hαr⟩ xT).mpr hx
  have hJ := fam.torusRestrictReal_mem_corootAnnihilator J x
  have hxL : xT ∈ corootAnnihilator fam.i fam.coroots L.val := by
    rw [mem_corootAnnihilator] at hJ ⊢
    intro β hβ
    rw [hL] at hβ
    rcases hβ with hβ | hβ
    · have : β = ⟨α, hαr⟩ := Subtype.ext hβ
      subst this
      exact hcor
    · exact hJ β hβ
  rw [← fam.range_restrictReal_torus L] at hxL
  obtain ⟨z, hz⟩ := hxL
  obtain ⟨_, _, π, _, _, hπ, _⟩ := (fam.isCompatible L).levi.exists_unipotentRadical_retraction
  refine ⟨rationalCharacterRestrictReal π z, fam.torusRestrictReal_injective J ?_⟩
  change rationalCharacterRestrictReal (fam.torus J ≫ fam.l J)
      (rationalCharacterRestrictReal e (rationalCharacterRestrictReal π z)) = xT
  rw [← restrictReal_comp_apply, ← restrictReal_comp_apply,
    show ((fam.torus J ≫ fam.l J) ≫ e) ≫ π = fam.torus L by
      simp only [Category.assoc]
      rw [reassoc_of% (fam.torus_comp_factor e he), hπ, Category.comp_id], hz]

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [Fintype (relativeWeylGroup fam.i)] [∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left]
  in
/-- A complex parameter is the sum of its complexified real part and `i` times its complexified
imaginary part. -/
private theorem eq_complexify_add_I_smul {H : GroupScheme (Spec (CommRingCat.of F))}
    (ν : ComplexCharacterParameter F H) :
    ν = ImaginaryAxis.complexify (parameterRealPart F H ν) + Complex.I •
      ImaginaryAxis.complexify
        (AlgebraTensorModule.map Complex.imLm (LinearMap.id : rationalCharacters H →ₗ[ℤ] _) ν) := by
  induction ν using TensorProduct.inductionOn with
  | tmul s χ =>
    simp only [parameterRealPart_tmul, AlgebraTensorModule.map_tmul, Complex.imLm_coe,
      LinearMap.id_coe, id_eq, ImaginaryAxis.complexify_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, ← TensorProduct.add_tmul]
    congr 1
    rw [mul_comm]
    exact (Complex.re_add_im s).symm
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add, smul_add]
    conv_lhs => rw [hx, hy]
    abel

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [Fintype (relativeWeylGroup fam.i)] [∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left]
  in
private theorem parameterRestrict_complexify {H₁ H₂ : GroupScheme (Spec (CommRingCat.of F))}
    (e : H₁ ⟶ H₂) (y : RealCharacterParameter F H₂) :
    parameterRestrict e (ImaginaryAxis.complexify y) =
      ImaginaryAxis.complexify (rationalCharacterRestrictReal e y) := by
  induction y using TensorProduct.inductionOn with
  | tmul r χ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Kernel of a simple root form, complex version.** Let `L = J ∪ {α}` for a simple root `α`,
and `e : P_J → P_L` the inclusion. A complex parameter of `P_J` on which the root form of
`α ∘ f_J` vanishes is the restriction of a complex parameter of `P_L`. -/
theorem exists_parameterRestrict_of_rootFunctional_eq_zero {J L : StandardIndex F G fam.i fam.ν}
    {α : characterLattice fam.T} (hα : α ∈ simpleRelativeRoots fam.i fam.ν)
    (hL : L.val = insert α J.val) (e : fam.P J ⟶ fam.P L) (he : e ≫ fam.p L = fam.p J)
    {ν : ComplexCharacterParameter F (fam.P J)}
    (hν : (fam.rootPresentation J).rootFunctional
        (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1
        fam.maximalSplit.isSplitSubtorus.1 (fam.f J ≫ α) ν = 0) :
    ∃ νL : ComplexCharacterParameter F (fam.P L), parameterRestrict e νL = ν := by
  set hA := (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1
  set hT := fam.maximalSplit.isSplitSubtorus.1
  set x₁ := parameterRealPart F (fam.P J) ν
  set x₂ := AlgebraTensorModule.map Complex.imLm
    (LinearMap.id : rationalCharacters (fam.P J) →ₗ[ℤ] _) ν
  have hdec := eq_complexify_add_I_smul ν
  have hval : (fam.rootPresentation J).rootFunctional hA hT (fam.f J ≫ α) ν =
      ((fam.rootPresentation J).realRootFunctional hA hT (fam.f J ≫ α) x₁ : ℂ) +
        Complex.I * ((fam.rootPresentation J).realRootFunctional hA hT (fam.f J ≫ α) x₂ : ℂ) := by
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, ImaginaryAxis.rootFunctional_complexify,
      ImaginaryAxis.rootFunctional_complexify, smul_eq_mul]
  rw [hν] at hval
  have h₁ : (fam.rootPresentation J).realRootFunctional hA hT (fam.f J ≫ α) x₁ = 0 := by
    have := congrArg Complex.re hval
    simpa using this.symm
  have h₂ : (fam.rootPresentation J).realRootFunctional hA hT (fam.f J ≫ α) x₂ = 0 := by
    have := congrArg Complex.im hval
    simpa using this.symm
  obtain ⟨y₁, hy₁⟩ := fam.exists_restrictReal_of_realRootFunctional_eq_zero hα hL e he h₁
  obtain ⟨y₂, hy₂⟩ := fam.exists_restrictReal_of_realRootFunctional_eq_zero hα hL e he h₂
  refine ⟨ImaginaryAxis.complexify y₁ + Complex.I • ImaginaryAxis.complexify y₂, ?_⟩
  rw [map_add, map_smul, parameterRestrict_complexify, parameterRestrict_complexify, hy₁, hy₂]
  exact hdec.symm

omit [NumberField F] [Fintype (relativeWeylGroup fam.i)]
  [∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left] in
/-- For a normalizer representative `W` of a Weyl conjugation from `P_I` to `P_K`, the inverse
conjugation restricts on the maximal split torus to the automorphism of the Weyl action. -/
theorem torus_comp_weylConjugation {I K : StandardIndex F G fam.i fam.ν}
    {W : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} (hW : W ∈ normalizerPoints fam.i)
    {C : fam.M K ⟶ fam.M I}
    (hC : IsWeylConjugation (fam.p I) (fam.l I) (fam.p K) (fam.l K) W C) :
    fam.torus K ≫ C ≫ fam.l I =
      CommGroupScheme.groupHom (normalizingAut fam.i ⟨W, hW⟩).inv ≫ fam.torus I ≫ fam.l I := by
  have hp : Mono (fam.p I).hom.hom := by
    let := (fam.isCompatible I).parabolic.isClosedSubgroup.mono
    exact Over.mono_of_mono_left _
  have : Mono (fam.p I) := (Grp.forget _).mono_of_mono_map (f := fam.p I) hp
  set σ := normalizingAut fam.i ⟨W, hW⟩
  have hσ : fam.i ≫ (G.innerIso W).hom = CommGroupScheme.groupHom σ.hom ≫ fam.i :=
    isNormalizingPoint_normalizingAut fam.i ⟨W, hW⟩
  have hσinv : fam.i ≫ (G.innerIso W).inv = CommGroupScheme.groupHom σ.inv ≫ fam.i := by
    rw [Iso.comp_inv_eq, Category.assoc, hσ, ← Category.assoc]
    change fam.i = CommGroupScheme.groupHom (σ.inv ≫ σ.hom) ≫ fam.i
    rw [Iso.inv_hom_id]
    exact (Category.id_comp _).symm
  apply (cancel_mono (fam.p I)).mp
  simp only [Category.assoc]
  rw [hC.comp_eq, reassoc_of% (fam.torus_comp K), hσinv, fam.torus_comp]

/-- **Transport of root forms by a Weyl parameter.** For a normalizer representative `W` of a
Weyl conjugation `(W, C)` from `P_I` to `P_K` and a character `γ` of the maximal split torus,
the root form of `γ ∘ f_K` at the transported parameter is the root form of `(W⁻¹ γ) ∘ f_I`. -/
theorem rootFunctional_weylParameter {I K : StandardIndex F G fam.i fam.ν}
    {W : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} (hW : W ∈ normalizerPoints fam.i)
    {C : fam.M K ⟶ fam.M I}
    (hC : IsWeylConjugation (fam.p I) (fam.l I) (fam.p K) (fam.l K) W C)
    {π : fam.P K ⟶ fam.M K} (hπ : fam.l K ≫ π = 𝟙 (fam.M K))
    (chi0 : characterLattice fam.T) (ν : ComplexCharacterParameter F (fam.P I)) :
    (fam.rootPresentation K).rootFunctional
        (fam.isCompatible K).splitComponent.isCentralSplitTorus.1.1
        fam.maximalSplit.isSplitSubtorus.1 (fam.f K ≫ chi0)
        (weylParameter (fam.l I) C π ν) =
      (fam.rootPresentation I).rootFunctional
        (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
        fam.maximalSplit.isSplitSubtorus.1
        (fam.f I ≫ relativeWeylLatticeAction fam.i (QuotientGroup.mk ⟨W, hW⟩)⁻¹ chi0) ν := by
  set w : relativeWeylGroup fam.i := QuotientGroup.mk ⟨W, hW⟩
  have htor := fam.torus_comp_weylConjugation hW hC
  have hmap : ((fam.rootPresentation K).rootFunctional
        (fam.isCompatible K).splitComponent.isCentralSplitTorus.1.1
        fam.maximalSplit.isSplitSubtorus.1 (fam.f K ≫ chi0)).comp
        (weylParameter (fam.l I) C π) =
      (fam.rootPresentation I).rootFunctional
        (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
        fam.maximalSplit.isSplitSubtorus.1
        (fam.f I ≫ relativeWeylLatticeAction fam.i w⁻¹ chi0) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s χ
    rw [LinearMap.comp_apply, weylParameter_tmul, ParabolicRootPresentation.rootFunctional_tmul,
      ParabolicRootPresentation.rootFunctional_tmul, fam.realRootFunctional_eq,
      fam.realRootFunctional_eq]
    congr 2
    have hres : fam.torusRestrictReal K ((1 : ℝ) ⊗ₜ[ℤ] characterRestrict (π ≫ C ≫ fam.l I) χ) =
        relativeWeylRealCharacterAction fam.i w (fam.torusRestrictReal I ((1 : ℝ) ⊗ₜ[ℤ] χ)) := by
      change (1 : ℝ) ⊗ₜ[ℤ] characterRestrict (fam.torus K ≫ fam.l K)
          (characterRestrict (π ≫ C ≫ fam.l I) χ) =
        (1 : ℝ) ⊗ₜ[ℤ] relativeWeylCharacterAction fam.i w
          (characterRestrict (fam.torus I ≫ fam.l I) χ)
      congr 1
      rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp]
      rw [show (fam.torus K ≫ fam.l K) ≫ π ≫ C ≫ fam.l I = fam.torus K ≫ C ≫ fam.l I by
        simp only [Category.assoc, reassoc_of% hπ], htor, characterRestrict_comp,
        AddMonoidHom.comp_apply]
      rfl
    rw [hres]
    have hinv : (1 : ℝ) ⊗ₜ[ℤ] chi0 = relativeWeylRealCharacterAction fam.i w
        ((1 : ℝ) ⊗ₜ[ℤ] relativeWeylLatticeAction fam.i w⁻¹ chi0) := by
      rw [relativeWeylRealCharacterAction_tmul]
      congr 1
      change chi0 = relativeWeylLatticeAction fam.i w (relativeWeylLatticeAction fam.i w⁻¹ chi0)
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hinv, relativeWeylInvariantForm_invariant]
  exact LinearMap.congr_fun hmap ν

omit [NumberField F] [Fintype (relativeWeylGroup fam.i)]
  [∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left] in
/-- The simple relative roots of the family are linearly independent in the real character
space of the maximal split torus. -/
theorem linearIndependent_simpleRoots_real :
    LinearIndependent ℝ (fun β : simpleRelativeRoots fam.i fam.ν =>
      (1 : ℝ) ⊗ₜ[ℤ] (β : characterLattice fam.T)) :=
  Module.Flat.linearIndependent_one_tmul
    (linearIndependent_simpleRelativeRoots_of_standardCocharacter_exists fam.i fam.ν
      fun J hJ => (standardCocharacter F G fam.connectedReductive fam.T fam.i fam.maximalSplit
        fam.ν fam.generic J hJ).1)

omit [NumberField F] [Fintype (relativeWeylGroup fam.i)]
  [∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left] in
/-- A simple root outside `K` is not in the real span of `K`. -/
theorem one_tmul_notMem_span {K : StandardIndex F G fam.i fam.ν} {α : characterLattice fam.T}
    (hα : α ∈ simpleRelativeRoots fam.i fam.ν) (hαK : α ∉ K.val) :
    (1 : ℝ) ⊗ₜ[ℤ] α ∉
      Submodule.span ℝ ((fun χ : characterLattice fam.T => (1 : ℝ) ⊗ₜ[ℤ] χ) '' K.val) := by
  have h := fam.linearIndependent_simpleRoots_real.notMem_span_image
    (s := {β : simpleRelativeRoots fam.i fam.ν | (β : characterLattice fam.T) ∈ K.val})
    (x := ⟨α, hα⟩) hαK
  convert h using 3
  ext v
  constructor
  · rintro ⟨χ, hχ, rfl⟩
    exact ⟨⟨χ, K.property hχ⟩, hχ, rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨β, hβ, rfl⟩

omit [NumberField F] [Fintype (relativeWeylGroup fam.i)]
  [∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left] in
/-- A simple root outside `K` restricts to a nonzero character of the split component of
`M_K`. -/
theorem restrict_simple_ne_zero {K : StandardIndex F G fam.i fam.ν} {α : characterLattice fam.T}
    (hα : α ∈ simpleRelativeRoots fam.i fam.ν) (hαK : α ∉ K.val) : fam.f K ≫ α ≠ 0 := by
  intro h
  apply fam.one_tmul_notMem_span hα hαK
  rw [← fam.ker_restrictReal_splitComponent K, LinearMap.mem_ker]
  change (1 : ℝ) ⊗ₜ[ℤ] (fam.f K ≫ α) = 0
  rw [h, TensorProduct.tmul_zero]

omit [Fintype (relativeWeylGroup fam.i)]
  [∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left] in
/-- A simple root outside `K` gives a root of the split component of `P_K` in its unipotent
radical. -/
theorem restrict_simple_mem_unipotentRoots {K : StandardIndex F G fam.i fam.ν}
    {α : characterLattice fam.T} (hα : α ∈ simpleRelativeRoots fam.i fam.ν) (hαK : α ∉ K.val) :
    fam.f K ≫ α ∈ (fam.rootPresentation K).unipotentRoots :=
  ⟨fam.restrict_simple_ne_zero hα hαK, α, hα.1, rfl⟩

/-- The root form changes sign with the root. -/
theorem rootFunctional_neg (J : StandardIndex F G fam.i fam.ν) (chi0 : characterLattice fam.T)
    (ν : ComplexCharacterParameter F (fam.P J)) :
    (fam.rootPresentation J).rootFunctional
        (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1
        fam.maximalSplit.isSplitSubtorus.1 (fam.f J ≫ (-chi0)) ν =
      -(fam.rootPresentation J).rootFunctional
        (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1
        fam.maximalSplit.isSplitSubtorus.1 (fam.f J ≫ chi0) ν := by
  have hmap : (fam.rootPresentation J).rootFunctional
        (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1
        fam.maximalSplit.isSplitSubtorus.1 (fam.f J ≫ (-chi0)) =
      -(fam.rootPresentation J).rootFunctional
        (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1
        fam.maximalSplit.isSplitSubtorus.1 (fam.f J ≫ chi0) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s χ
    rw [LinearMap.neg_apply, ParabolicRootPresentation.rootFunctional_tmul,
      ParabolicRootPresentation.rootFunctional_tmul, fam.realRootFunctional_eq,
      fam.realRootFunctional_eq, TensorProduct.tmul_neg, map_neg, Complex.ofReal_neg, mul_neg]
  exact LinearMap.congr_fun hmap ν

/-- **Transport of a simple root hyperplane.** Let `(W, C)` be a Weyl conjugation from `P_I` to
`P_K` with `W` normalizing the maximal split torus and carrying the simple roots of `I` into
`K`, and let `α ∉ K` be simple. Then some root `β` of the split component of `P_I` in its
unipotent radical has its kernel carried by the Weyl parameter map into the kernel of the root
form of `α ∘ f_K`. -/
theorem exists_unipotentRoot_weylParameter {I K : StandardIndex F G fam.i fam.ν}
    {W : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} (hW : W ∈ normalizerPoints fam.i)
    {C : fam.M K ⟶ fam.M I}
    (hC : IsWeylConjugation (fam.p I) (fam.l I) (fam.p K) (fam.l K) W C)
    {π : fam.P K ⟶ fam.M K} (hπ : fam.l K ≫ π = 𝟙 (fam.M K))
    (hmaps : ∀ β ∈ I.val, relativeWeylLatticeAction fam.i (QuotientGroup.mk ⟨W, hW⟩) β ∈ K.val)
    {α : characterLattice fam.T} (hα : α ∈ simpleRelativeRoots fam.i fam.ν) (hαK : α ∉ K.val) :
    ∃ β ∈ (fam.rootPresentation I).unipotentRoots,
      ∀ ν : ComplexCharacterParameter F (fam.P I),
        (fam.rootPresentation I).rootFunctional
            (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
            fam.maximalSplit.isSplitSubtorus.1 β ν = 0 →
          (fam.rootPresentation K).rootFunctional
            (fam.isCompatible K).splitComponent.isCentralSplitTorus.1.1
            fam.maximalSplit.isSplitSubtorus.1 (fam.f K ≫ α)
            (weylParameter (fam.l I) C π ν) = 0 := by
  set w : relativeWeylGroup fam.i := QuotientGroup.mk ⟨W, hW⟩
  set g := relativeWeylLatticeAction fam.i w⁻¹ α
  have hg : g ∈ relativeRoots fam.i :=
    relativeWeylLatticeAction_mapsTo_relativeRoots fam.i w⁻¹ hα.1.1
  have hng : -g ∈ relativeRoots fam.i := fam.coroots.neg_mem_relativeRoots fam.i hg
  have hwg : relativeWeylLatticeAction fam.i w g = α := by
    change relativeWeylLatticeAction fam.i w (relativeWeylLatticeAction fam.i w⁻¹ α) = α
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hg0 : fam.f I ≫ g ≠ 0 := by
    intro h0
    have hmem : (1 : ℝ) ⊗ₜ[ℤ] g ∈
        Submodule.span ℝ ((fun χ : characterLattice fam.T => (1 : ℝ) ⊗ₜ[ℤ] χ) '' I.val) := by
      rw [← fam.ker_restrictReal_splitComponent I, LinearMap.mem_ker]
      change (1 : ℝ) ⊗ₜ[ℤ] (fam.f I ≫ g) = 0
      rw [h0, TensorProduct.tmul_zero]
    have h1 : (relativeWeylRealCharacterAction fam.i w).toLinearMap ((1 : ℝ) ⊗ₜ[ℤ] g) =
        (1 : ℝ) ⊗ₜ[ℤ] α := by
      change relativeWeylRealCharacterAction fam.i w ((1 : ℝ) ⊗ₜ[ℤ] g) = _
      rw [relativeWeylRealCharacterAction_tmul]
      congr 1
    have hmem' := Submodule.mem_map_of_mem
      (f := (relativeWeylRealCharacterAction fam.i w).toLinearMap) hmem
    rw [Submodule.map_span, h1] at hmem'
    apply fam.one_tmul_notMem_span hα hαK
    refine Submodule.span_mono ?_ hmem'
    rintro _ ⟨_, ⟨χ, hχ, rfl⟩, rfl⟩
    exact ⟨_, hmaps χ hχ, (relativeWeylRealCharacterAction_tmul fam.i w 1 χ).symm⟩
  have hkey : ∀ ν : ComplexCharacterParameter F (fam.P I),
      (fam.rootPresentation K).rootFunctional
          (fam.isCompatible K).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1 (fam.f K ≫ α) (weylParameter (fam.l I) C π ν) =
        (fam.rootPresentation I).rootFunctional
          (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1 (fam.f I ≫ g) ν :=
    fun ν => fam.rootFunctional_weylParameter hW hC hπ α ν
  rcases lt_or_gt_of_ne (fam.generic g hg) with hneg | hpos
  · refine ⟨fam.f I ≫ (-g), ⟨?_, -g, ⟨hng, ?_⟩, rfl⟩, fun ν hν => ?_⟩
    · rw [Preadditive.comp_neg]
      exact neg_ne_zero.mpr hg0
    · rw [map_neg]
      exact neg_pos.mpr hneg
    · rw [fam.rootFunctional_neg, neg_eq_zero] at hν
      rw [hkey, hν]
  · exact ⟨fam.f I ≫ g, ⟨hg0, g, ⟨hg, hpos⟩, rfl⟩, fun ν hν => by rw [hkey, hν]⟩

end Langlands.Global.StandardParabolicFamily
