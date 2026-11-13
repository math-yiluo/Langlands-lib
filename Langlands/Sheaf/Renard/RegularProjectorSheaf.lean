import Langlands.Sheaf.Renard.ProjectorVectorSheafSections
import Langlands.Sheaf.Renard.VectorSheafScalars
import Langlands.Sheaf.Equivariant.LocallyConstant
import Langlands.Algebra.NondegenerateTensorFunctor
import Langlands.Algebra.RegularModuleHom

/-!
# The sheaf of the regular test module is the locally constant scalar sheaf

Renard (9 July 2026), II.2.5, first Example after the stalk description, printed p.41 /
PDF p.47: if `M = 𝒟(X)`, the sheaf `ℳ` attached to `M` by the Theorem of II.2.5 is the sheaf
`𝒞^∞_X` of locally constant functions on `X`.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis

universe u

namespace Langlands.Sheaf.Renard.RegularProjectorSheaf

open ProjectorBasisSheaf ProjectorVectorSheaf
open Langlands.Sheaf.Renard.VectorSheafScalars (VectorSheaf)

/-! ### The complex vector sheaf `𝒞^∞_X` -/

section Scalar

variable (X : Type u) [TopologicalSpace X]

/-- The presheaf of complex vector spaces `U ↦ 𝒞^∞(U)` of locally constant complex
functions, with restriction the pullback along the inclusion. -/
def scalarPresheaf : TopCat.Presheaf (ModuleCat.{u} ℂ) (TopCat.of X) where
  obj U := ModuleCat.of ℂ (LocallyConstant U.unop ℂ)
  map f := ModuleCat.ofHom
    (LocallyConstant.comapₗ ℂ (LocallyConstantScalar.inclusion f.unop.le))
  map_id _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply LocallyConstant.ext
    intro x
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply LocallyConstant.ext
    intro x
    rfl

variable {X} in
/-- The restriction maps are those of the published scalar ring presheaf. -/
theorem scalarPresheaf_map_eq_restrict {U V : Opens X} (i : U ⟶ V)
    (s : LocallyConstant V ℂ) :
    ((scalarPresheaf X).map i.op).hom s = LocallyConstantScalar.restrict ℂ i.le s := rfl

/-- Forgetting the vector space structure gives Mathlib's presheaf of functions satisfying
the published local predicate of local constancy. -/
def underlyingIso : scalarPresheaf X ⋙ forget (ModuleCat.{u} ℂ) ≅
    TopCat.subpresheafToTypes
      (Langlands.Sheaf.Equivariant.LocallyConstantSheaf.localPredicate X ℂ).toPrelocalPredicate :=
  NatIso.ofComponents (fun _ =>
    { hom := TypeCat.ofHom (fun s => ⟨s.toFun, s.isLocallyConstant⟩)
      inv := TypeCat.ofHom (fun s => ⟨s.val, s.property⟩) }) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro s
    rfl)

theorem scalarPresheaf_isSheaf : (scalarPresheaf X).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget (ModuleCat.{u} ℂ))]
  exact (CategoryTheory.Presheaf.isSheaf_of_iso_iff (underlyingIso X)).mpr
    (TopCat.subpresheafToTypes.isSheaf
      (Langlands.Sheaf.Equivariant.LocallyConstantSheaf.localPredicate X ℂ))

/-- Renard's sheaf `𝒞^∞_X` as a complex vector sheaf. -/
def scalarSheaf : VectorSheaf X :=
  ⟨scalarPresheaf X, scalarPresheaf_isSheaf X⟩

variable {X} in
/-- The published action of `𝒞^∞(U)` on the sections of `𝒞^∞_X` is multiplication. -/
theorem scalarSheaf_smul {U : Opens X} (f s : LocallyConstant U ℂ) :
    VectorSheafScalars.smul (scalarSheaf X) f s = f * s := by
  refine ((VectorSheafScalars.eq_smul_iff (scalarSheaf X) f s
    (show (scalarSheaf X).presheaf.obj (op U) from f * s)).mpr ?_).symm
  intro x hx
  have hW := VectorSheafScalars.fiber_le f ⟨x, hx⟩
  have hxW := VectorSheafScalars.mem_fiber_self f ⟨x, hx⟩
  rw [← TopCat.Presheaf.germ_res_apply (scalarSheaf X).presheaf (homOfLE hW) x hxW,
    ← TopCat.Presheaf.germ_res_apply (scalarSheaf X).presheaf (homOfLE hW) x hxW s,
    ← map_smul]
  congr 1
  apply LocallyConstant.ext
  intro y
  change f ⟨y.val, _⟩ * s ⟨y.val, _⟩ = f ⟨x, hx⟩ * s ⟨y.val, _⟩
  rw [VectorSheafScalars.apply_eq_of_mem_fiber f ⟨x, hx⟩ y.property]

end Scalar

/-! ### The sheaf of the regular module `𝒟(X)` -/

section Regular

variable {X : Type u} [TopologicalSpace X] (hX : Langlands.Topology.IsLocallyProfinite X)

attribute [local instance] NonUnitalModule.regular

/-- The regular module `𝒟(X)` (left multiplication) is nondegenerate; this is the published
`NondegenerateTensorFunctor.regular_isNondegenerate` for the idempotented algebra `𝒟(X)`. -/
theorem isNondegenerate_regular :
    IsNondegenerate (PointwiseTestAlgebra.Carrier X) (PointwiseTestAlgebra.Carrier X) :=
  NondegenerateTensorFunctor.regular_isNondegenerate PointwiseTestAlgebra.isIdempotented

/-- Renard's sheaf `ℳ` attached by the Theorem of II.2.5 to the regular module `M = 𝒟(X)`:
the published complex vector sheaf `ProjectorVectorSheaf.sheaf` of this module. -/
abbrev regularSheaf : VectorSheaf X :=
  ProjectorVectorSheaf.sheaf.{u,0} hX (isNondegenerate_regular (X := X))

variable {hX}

/-- The characteristic test function `χ_U` is `1` on `U`. -/
theorem test_apply_of_mem (U : CompactOpen hX) {x : X} (hx : x ∈ U.obj) :
    test hX U x = 1 := by
  change (U.obj : Set X).indicator (fun _ => (1 : ℂ)) x = 1
  exact Set.indicator_of_mem hx _

/-- The characteristic test function `χ_U` is `0` off `U`. -/
theorem test_apply_of_not_mem (U : CompactOpen hX) {x : X} (hx : x ∉ U.obj) :
    test hX U x = 0 := by
  change (U.obj : Set X).indicator (fun _ => (1 : ℂ)) x = 0
  exact Set.indicator_of_notMem hx _

/-- On the regular module, the projector `χ_U` acts by pointwise multiplication. -/
theorem action_regular (U : CompactOpen hX) (g : PointwiseTestAlgebra.Carrier X) :
    action hX (PointwiseTestAlgebra.Carrier X) U g = test hX U * g := rfl

/-- Elements of `χ_U · 𝒟(X)` vanish off `U`. -/
theorem value_apply_of_not_mem {U : CompactOpen hX}
    (g : Value hX (PointwiseTestAlgebra.Carrier X) U) {x : X} (hx : x ∉ U.obj) :
    g.val x = 0 := by
  have h := value_fixed hX (PointwiseTestAlgebra.Carrier X) g
  calc g.val x = (action hX (PointwiseTestAlgebra.Carrier X) U g.val) x := by rw [h]
    _ = test hX U x * g.val x := rfl
    _ = 0 := by rw [test_apply_of_not_mem U hx, zero_mul]

/-- Projector restriction does not change values on the smaller compact open. -/
theorem restrict_apply_of_mem {U V : CompactOpen hX} (h : U.obj ≤ V.obj)
    (g : Value hX (PointwiseTestAlgebra.Carrier X) V) {x : X} (hx : x ∈ U.obj) :
    (restrict hX (PointwiseTestAlgebra.Carrier X) h g).val x = g.val x := by
  change test hX U x * g.val x = g.val x
  rw [test_apply_of_mem U hx, one_mul]

/-- Renard's canonical complex structure on the regular module is the given one. -/
theorem regular_smul (c : ℂ) (g : PointwiseTestAlgebra.Carrier X) :
    @HSMul.hSMul ℂ _ _
      (@instHSMul _ _ (originalModule (isNondegenerate_regular (X := X))).toSMul) c g =
      c • g := by
  obtain ⟨e, he⟩ := isNondegenerate_regular (X := X) g
  rw [NondegenerateScalars.complex_smul_eq PointwiseTestAlgebra.isIdempotented
    isNondegenerate_regular c g e he]
  change (c • (e : PointwiseTestAlgebra.Carrier X)) * g = c • g
  rw [smul_mul_assoc]
  exact congrArg (c • ·) he

/-- Two components of a section agree on a smaller compact open. -/
theorem component_apply_of_le {V : Opens X}
    (s : (ProjectorVectorSheaf.presheaf hX (isNondegenerate_regular (X := X))).obj (op V))
    (U W : BasisAllOpen.Inside (compactOpenBasis hX) V) (h : W.val.obj ≤ U.val.obj)
    {x : X} (hx : x ∈ W.val.obj) :
    (s.val W).val x = (s.val U).val x := by
  rw [← section_compatible hX isNondegenerate_regular s U W h]
  exact restrict_apply_of_mem h _ hx

/-- Two components of a section agree at every common point. -/
theorem component_apply_eq {V : Opens X}
    (s : (ProjectorVectorSheaf.presheaf hX (isNondegenerate_regular (X := X))).obj (op V))
    (U W : BasisAllOpen.Inside (compactOpenBasis hX) V) {x : X}
    (hxU : x ∈ U.val.obj) (hxW : x ∈ W.val.obj) :
    (s.val U).val x = (s.val W).val x := by
  let I : BasisAllOpen.Inside (compactOpenBasis hX) V :=
    ⟨interOpen hX U.val W.val, inf_le_left.trans U.property⟩
  have hxI : x ∈ I.val.obj := Opens.mem_inf.mpr ⟨hxU, hxW⟩
  rw [← component_apply_of_le s U I inf_le_left hxI,
    component_apply_of_le s W I inf_le_right hxI]

variable (hX) in
/-- A chosen compact open neighbourhood inside `V` of a point of `V`. -/
def neighborhood {V : Opens X} (x : V) : BasisAllOpen.Inside (compactOpenBasis hX) V :=
  ⟨((compactOpenBasis hX).exists_subset V x.property).choose,
    ((compactOpenBasis hX).exists_subset V x.property).choose_spec.2⟩

/-- The chosen neighbourhood contains the point. -/
theorem mem_neighborhood {V : Opens X} (x : V) : (x : X) ∈ (neighborhood hX x).val.obj :=
  ((compactOpenBasis hX).exists_subset V x.property).choose_spec.1

/-- The value at `x` of a section, read off any compact open neighbourhood. -/
def sectionValue {V : Opens X}
    (s : (ProjectorVectorSheaf.presheaf hX (isNondegenerate_regular (X := X))).obj (op V))
    (x : V) : ℂ :=
  (s.val (neighborhood hX x)).val x

/-- The value does not depend on the compact open neighbourhood used to read it. -/
theorem sectionValue_eq {V : Opens X}
    (s : (ProjectorVectorSheaf.presheaf hX (isNondegenerate_regular (X := X))).obj (op V))
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) {x : V} (hx : (x : X) ∈ U.val.obj) :
    sectionValue s x = (s.val U).val x :=
  component_apply_eq s _ U (mem_neighborhood x) hx

/-- The values of a section form a locally constant function on `V`. -/
theorem isLocallyConstant_sectionValue {V : Opens X}
    (s : (ProjectorVectorSheaf.presheaf hX (isNondegenerate_regular (X := X))).obj (op V)) :
    IsLocallyConstant (sectionValue s) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  let U := neighborhood hX x
  let g : PointwiseTestAlgebra.Carrier X := (s.val U).val
  refine ⟨Subtype.val ⁻¹' ((U.val.obj : Set X) ∩ {z | g z = g x}), ?_,
    ⟨mem_neighborhood x, rfl⟩, ?_⟩
  · exact (U.val.obj.isOpen.inter
      ((PointwiseTestAlgebra.locallyConstant g).isOpen_fiber _)).preimage continuous_subtype_val
  · rintro y ⟨hyU, hyg⟩
    rw [sectionValue_eq s U hyU, sectionValue_eq s U (mem_neighborhood x)]
    exact hyg

/-- The locally constant function on `V` of a section of the regular sheaf. -/
def sectionFun {V : Opens X}
    (s : (ProjectorVectorSheaf.presheaf hX (isNondegenerate_regular (X := X))).obj (op V)) :
    LocallyConstant V ℂ :=
  ⟨sectionValue s, isLocallyConstant_sectionValue s⟩

/-- The function of a section agrees with each component on its compact open. -/
theorem sectionFun_apply {V : Opens X}
    (s : (ProjectorVectorSheaf.presheaf hX (isNondegenerate_regular (X := X))).obj (op V))
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) {x : V} (hx : (x : X) ∈ U.val.obj) :
    sectionFun s x = (s.val U).val x :=
  sectionValue_eq s U hx

open Classical in
/-- Extension by zero of a locally constant function on a compact open `U`. -/
def extendLC (U : CompactOpen hX) (f : LocallyConstant U.obj ℂ) : LocallyConstant X ℂ :=
  LocallyConstant.piecewise (clopen hX U).isClosed U.obj.isOpen.isClosed_compl
    (Set.union_compl_self _) f 0 (fun _ hx => (hx.2 hx.1).elim)

/-- The extension by zero agrees with `f` on `U`. -/
theorem extendLC_apply_of_mem (U : CompactOpen hX) (f : LocallyConstant U.obj ℂ) {x : X}
    (hx : x ∈ U.obj) : extendLC U f x = f ⟨x, hx⟩ := by
  classical
  exact LocallyConstant.piecewise_apply_left _ _ _ _ _ _ x hx

/-- The extension by zero vanishes off `U`. -/
theorem extendLC_apply_of_not_mem (U : CompactOpen hX) (f : LocallyConstant U.obj ℂ) {x : X}
    (hx : x ∉ U.obj) : extendLC U f x = 0 := by
  classical
  exact LocallyConstant.piecewise_apply_right _ _ _ _ _ _ x hx

/-- The test function extending `f` by zero outside the compact open `U`. -/
def extendTest (U : CompactOpen hX) (f : LocallyConstant U.obj ℂ) :
    PointwiseTestAlgebra.Carrier X :=
  ⟨extendLC U f, HasCompactSupport.intro' (compact hX U) (clopen hX U).isClosed
    fun _ hx => extendLC_apply_of_not_mem U f hx⟩

/-- The extended test function agrees with `f` on `U`. -/
theorem extendTest_apply_of_mem (U : CompactOpen hX) (f : LocallyConstant U.obj ℂ) {x : X}
    (hx : x ∈ U.obj) : extendTest U f x = f ⟨x, hx⟩ :=
  extendLC_apply_of_mem U f hx

/-- The extended test function vanishes off `U`. -/
theorem extendTest_apply_of_not_mem (U : CompactOpen hX) (f : LocallyConstant U.obj ℂ)
    {x : X} (hx : x ∉ U.obj) : extendTest U f x = 0 :=
  extendLC_apply_of_not_mem U f hx

/-- The extension by zero lies in `χ_U · 𝒟(X)`. -/
def extendValue (U : CompactOpen hX) (f : LocallyConstant U.obj ℂ) :
    Value hX (PointwiseTestAlgebra.Carrier X) U :=
  ⟨extendTest U f, by
    change test hX U * extendTest U f = extendTest U f
    ext x
    rw [PointwiseTestAlgebra.mul_apply]
    by_cases hx : x ∈ U.obj
    · rw [test_apply_of_mem U hx, one_mul]
    · rw [test_apply_of_not_mem U hx, zero_mul, extendTest_apply_of_not_mem U f hx]⟩

/-- The underlying test function of `extendValue U f` is `extendTest U f`. -/
theorem extendValue_val (U : CompactOpen hX) (f : LocallyConstant U.obj ℂ) :
    (extendValue U f).val = extendTest U f := rfl

/-- The section of the regular sheaf whose component on each compact open `U ⊆ V` is the
extension by zero of `f|_U`. -/
def extendSection {V : Opens X} (f : LocallyConstant V ℂ) :
    (ProjectorVectorSheaf.presheaf hX (isNondegenerate_regular (X := X))).obj (op V) :=
  sectionMk hX isNondegenerate_regular V
    (fun U => extendValue U.val (LocallyConstantScalar.restrict ℂ U.property f))
    (fun U W h => by
      apply Subtype.ext
      ext x
      rw [restrict_val, action_regular, PointwiseTestAlgebra.mul_apply, extendValue_val,
        extendValue_val]
      by_cases hx : x ∈ W.val.obj
      · rw [test_apply_of_mem _ hx, one_mul, extendTest_apply_of_mem _ _ (h hx),
          extendTest_apply_of_mem _ _ hx]
        rfl
      · rw [test_apply_of_not_mem _ hx, zero_mul, extendTest_apply_of_not_mem _ _ hx])

/-- Each component of `extendSection f` agrees with `f` on its compact open. -/
theorem extendSection_apply {V : Opens X} (f : LocallyConstant V ℂ)
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) {x : X} (hx : x ∈ U.val.obj) :
    ((extendSection (hX := hX) f).val U).val x = f ⟨x, U.property hx⟩ :=
  extendTest_apply_of_mem _ _ hx

variable (hX) in
/-- Over every open `V`, the sections of the regular sheaf are exactly the locally constant
functions on `V`: a section goes to the function `x ↦ s_U(x)` for compact opens `U ∋ x`. -/
def sectionScalarEquiv (V : Opens X) :
    (ProjectorVectorSheaf.presheaf hX (isNondegenerate_regular (X := X))).obj (op V) ≃ₗ[ℂ]
      LocallyConstant V ℂ where
  toFun := sectionFun
  map_add' _ _ := rfl
  map_smul' c s := by
    apply LocallyConstant.ext
    intro x
    change ((c • s).val (neighborhood hX x)).val x = c • (s.val (neighborhood hX x)).val x
    rw [smul_val, regular_smul]
    rfl
  invFun := extendSection
  left_inv s := by
    apply section_ext
    intro U
    ext x
    by_cases hx : x ∈ U.val.obj
    · rw [extendSection_apply _ U hx]
      exact sectionFun_apply s U (x := ⟨x, U.property hx⟩) hx
    · exact (value_apply_of_not_mem _ hx).trans (value_apply_of_not_mem _ hx).symm
  right_inv f := by
    apply LocallyConstant.ext
    intro x
    exact (sectionFun_apply _ _ (mem_neighborhood x)).trans
      (extendSection_apply f _ (mem_neighborhood x))

/-- The function of a section is read off any component whose compact open contains the
point. -/
theorem sectionScalarEquiv_apply {V : Opens X}
    (s : (ProjectorVectorSheaf.presheaf hX (isNondegenerate_regular (X := X))).obj (op V))
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) {x : V} (hx : (x : X) ∈ U.val.obj) :
    sectionScalarEquiv hX V s x = (s.val U).val x :=
  sectionFun_apply s U hx

/-- The function of a restricted section is the restricted function. -/
theorem sectionScalarEquiv_restrict {U V : Opens X} (i : U ⟶ V)
    (s : (ProjectorVectorSheaf.presheaf hX (isNondegenerate_regular (X := X))).obj (op V)) :
    sectionScalarEquiv hX U
        (((ProjectorVectorSheaf.presheaf hX isNondegenerate_regular).map i.op).hom s) =
      LocallyConstantScalar.restrict ℂ i.le (sectionScalarEquiv hX V s) := by
  apply LocallyConstant.ext
  intro x
  rw [LocallyConstantScalar.restrict_apply,
    sectionScalarEquiv_apply _ (neighborhood hX x) (mem_neighborhood x),
    sectionScalarEquiv_apply _ ⟨(neighborhood hX x).val, (neighborhood hX x).property.trans i.le⟩
      (mem_neighborhood x)]
  rfl

variable (hX) in
/-- The natural isomorphism of presheaves of complex vector spaces. -/
def presheafIso :
    ProjectorVectorSheaf.presheaf hX (isNondegenerate_regular (X := X)) ≅ scalarPresheaf X :=
  NatIso.ofComponents (fun V => (sectionScalarEquiv hX V.unop).toModuleIso) (by
    intro V W i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact sectionScalarEquiv_restrict i.unop s)

variable (hX) in
/-- **Renard II.2.5, Example.** For `M = 𝒟(X)` the sheaf `ℳ` of the Theorem of II.2.5 is the
sheaf `𝒞^∞_X` of locally constant functions. -/
def regularSheafIso : regularSheaf hX ≅ scalarSheaf X :=
  ObjectProperty.isoMk _ (presheafIso hX)

/-- The components of `regularSheafIso` are the linear equivalences `sectionScalarEquiv`. -/
theorem regularSheafIso_hom_app (V : Opens X) :
    ((regularSheafIso hX).hom.hom.app (op V)).hom = (sectionScalarEquiv hX V).toLinearMap :=
  rfl

/-- The section over `V` of an original vector `m ∈ 𝒟(X)` is the restriction `m|_V`. -/
theorem sectionScalarEquiv_originalSection (V : Opens X) (m : PointwiseTestAlgebra.Carrier X)
    (x : V) :
    sectionScalarEquiv hX V (originalSection hX isNondegenerate_regular V m) x = m x := by
  refine (sectionScalarEquiv_apply _ (neighborhood hX x) (mem_neighborhood x)).trans ?_
  change test hX (neighborhood hX x).val x * m x = m x
  rw [test_apply_of_mem _ (mem_neighborhood x), one_mul]

/-- On a compact open `U`, the section of `g ∈ χ_U · 𝒟(X)` is the restriction `g|_U`. -/
theorem sectionScalarEquiv_sectionLinearEquiv (U : CompactOpen hX)
    (g : Value hX (PointwiseTestAlgebra.Carrier X) U) (x : U.obj) :
    sectionScalarEquiv hX U.obj
      (ProjectorVectorSheaf.sectionLinearEquiv hX isNondegenerate_regular U g) x = g.val x :=
  (sectionScalarEquiv_apply _ ⟨U, le_rfl⟩ x.property).trans
    (restrict_apply_of_mem le_rfl g x.property)

/-- The isomorphism is linear over the locally constant scalars of II.2.5
(`VectorSheafScalars`), which act on `𝒞^∞_X` by multiplication. -/
theorem sectionScalarEquiv_smul {V : Opens X} (f : LocallyConstant V ℂ)
    (s : (regularSheaf hX).presheaf.obj (op V)) :
    sectionScalarEquiv hX V (f • s) = f * sectionScalarEquiv hX V s :=
  (VectorSheafScalars.app_smul (regularSheafIso hX).hom f s).trans (scalarSheaf_smul f _)

end Regular

end Langlands.Sheaf.Renard.RegularProjectorSheaf
