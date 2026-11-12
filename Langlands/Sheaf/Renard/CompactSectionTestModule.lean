import Langlands.Sheaf.Renard.VectorSheafScalars
import Langlands.Sheaf.CompactSupport
import Langlands.HarmonicAnalysis.PointwiseTestAlgebra
import Langlands.Algebra.NondegenerateScalars
import Langlands.Topology.LocallyProfinite

/-!
# Compact sections of a complex vector sheaf as a nondegenerate test module

Renard (9 July 2026), II.2.5 Theorem and its proof, printed pp.39–40 / PDF pp.45–46.
The pointwise test algebra acts on compactly supported global sections through the
locally constant scalar action, and a compact open containing the support fixes a section.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.CompactSectionTestModule

open CategoryTheory TopologicalSpace Opposite
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Renard.VectorSheafScalars

variable {X : Type} [TopologicalSpace X]

/-- The continuous inclusion of the largest open into the space. -/
def topInclusion : C((⊤ : Opens X), X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Pointwise test functions, read as locally constant functions on the largest open. -/
def testScalar : PointwiseTestAlgebra.Carrier X →ₙₐ[ℂ] LocallyConstant (⊤ : Opens X) ℂ :=
  (LocallyConstant.comapₐ (Z := ℂ) ℂ (topInclusion (X := X))).toNonUnitalAlgHom.comp
    PointwiseTestAlgebra.inclusion

@[simp]
theorem testScalar_apply (f : PointwiseTestAlgebra.Carrier X) (x : (⊤ : Opens X)) :
    testScalar f x = f x := rfl

/-- A compact subset lies in a compact open when compact opens form a neighborhood basis. -/
theorem exists_compactOpen_superset
    (hX : Langlands.Topology.HasCompactOpenNeighborhoodBasis X) {K : Set X}
    (hK : IsCompact K) : ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ K ⊆ V := by
  choose W hxW hWo hWc _ using fun x : X => hX x Set.univ Filter.univ_mem
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover W fun x _ => (hWo x).mem_nhds (hxW x)
  exact ⟨⋃ x ∈ t, W x, isOpen_biUnion fun x _ => hWo x,
    t.isCompact_biUnion fun x _ => hWc x, hKt⟩

variable (F : VectorSheaf X)

/-- The germ formula `(f s)(x) = f(x) s(x)` for global sections. -/
theorem Γgerm_smul (f : LocallyConstant (⊤ : Opens X) ℂ) (s : F.presheaf.obj (op ⊤))
    (x : X) : F.presheaf.Γgerm x (f • s) = f ⟨x, trivial⟩ • F.presheaf.Γgerm x s :=
  germ_lc_smul F f s x trivial

/-- Locally constant scalars cannot enlarge the support of a global section. -/
theorem support_smul_subset (f : LocallyConstant (⊤ : Opens X) ℂ)
    (s : F.presheaf.obj (op ⊤)) :
    CompactSupport.support F.presheaf (f • s) ⊆ CompactSupport.support F.presheaf s := by
  intro x hx
  by_contra hs
  have h0 : F.presheaf.Γgerm x s = 0 := by simpa [CompactSupport.support] using hs
  exact hx (by rw [Γgerm_smul, h0, smul_zero])

/-- The section `f • s` for a test function `f` and a compactly supported section `s`. -/
def testSmul (f : PointwiseTestAlgebra.Carrier X) (s : CompactSupport.submodule F.presheaf) :
    CompactSupport.submodule F.presheaf :=
  ⟨testScalar f • (s : F.presheaf.obj (op ⊤)),
    (show IsCompact (CompactSupport.support F.presheaf s.1) from s.2).of_isClosed_subset
      (CompactSupport.isClosed_support _ _) (support_smul_subset F _ _)⟩

/-- Renard II.2.5: the pointwise test algebra acts on compactly supported sections. -/
instance testModule :
    NonUnitalModule (PointwiseTestAlgebra.Carrier X) (CompactSupport.submodule F.presheaf) where
  smul := testSmul F
  smul_zero f := by
    change testSmul F f 0 = 0
    exact Subtype.ext (smul_zero _)
  smul_add f s t := by
    change testSmul F f (s + t) = testSmul F f s + testSmul F f t
    exact Subtype.ext (smul_add _ _ _)
  mul_smul f g s := by
    change testSmul F (f * g) s = testSmul F f (testSmul F g s)
    exact Subtype.ext (by
      change testScalar (f * g) • (s : F.presheaf.obj (op ⊤)) =
        testScalar f • testScalar g • (s : F.presheaf.obj (op ⊤))
      rw [map_mul, mul_smul])
  add_smul f g s := by
    change testSmul F (f + g) s = testSmul F f s + testSmul F g s
    exact Subtype.ext (by
      change testScalar (f + g) • (s : F.presheaf.obj (op ⊤)) =
        testScalar f • (s : F.presheaf.obj (op ⊤)) + testScalar g • (s : F.presheaf.obj (op ⊤))
      rw [map_add, add_smul])
  zero_smul s := by
    change testSmul F 0 s = 0
    exact Subtype.ext (by
      change testScalar 0 • (s : F.presheaf.obj (op ⊤)) = 0
      rw [map_zero, zero_smul])

@[simp]
theorem coe_testSmul (f : PointwiseTestAlgebra.Carrier X)
    (s : CompactSupport.submodule F.presheaf) :
    ((f • s : CompactSupport.submodule F.presheaf) : F.presheaf.obj (op ⊤)) =
      testScalar f • (s : F.presheaf.obj (op ⊤)) := rfl

/-- The source formula for the test action, read on germs. -/
theorem Γgerm_testSmul (f : PointwiseTestAlgebra.Carrier X)
    (s : CompactSupport.submodule F.presheaf) (x : X) :
    F.presheaf.Γgerm x ((f • s : CompactSupport.submodule F.presheaf) : F.presheaf.obj (op ⊤)) =
      f x • F.presheaf.Γgerm x (s : F.presheaf.obj (op ⊤)) :=
  Γgerm_smul F (testScalar f) s.1 x

/-- A compact clopen containing the support fixes the section (proof of the Theorem). -/
theorem characteristic_smul_eq_self {V : Set X} (hV : IsClopen V) (hc : IsCompact V)
    (s : CompactSupport.submodule F.presheaf)
    (hs : CompactSupport.support F.presheaf s.1 ⊆ V) :
    PointwiseTestAlgebra.characteristic hV hc • s = s := by
  apply Subtype.ext
  apply ext_germ F
  intro x hx
  change F.presheaf.Γgerm x _ = F.presheaf.Γgerm x _
  rw [Γgerm_testSmul, PointwiseTestAlgebra.characteristic_apply]
  by_cases hxV : x ∈ V
  · rw [Set.indicator_of_mem hxV, one_smul]
  · rw [Set.indicator_of_notMem hxV, zero_smul]
    have h0 : F.presheaf.Γgerm x s.1 = 0 := by
      simpa [CompactSupport.support] using fun h => hxV (hs h)
    exact h0.symm

/-- Renard II.2.5 Theorem, first assertion: compact sections form a nondegenerate module. -/
theorem isNondegenerate (hX : Langlands.Topology.IsLocallyProfinite X) :
    IsNondegenerate (PointwiseTestAlgebra.Carrier X) (CompactSupport.submodule F.presheaf) := by
  intro s
  obtain ⟨V, hVo, hVc, hsV⟩ := exists_compactOpen_superset hX.2 s.2
  have := hX.1
  exact ⟨PointwiseTestAlgebra.characteristicIdempotent ⟨hVc.isClosed, hVo⟩ hVc,
    characteristic_smul_eq_self F ⟨hVc.isClosed, hVo⟩ hVc s hsV⟩

/-- The test action is compatible with the original complex scalars. -/
instance isScalarTower :
    IsScalarTower ℂ (PointwiseTestAlgebra.Carrier X) (CompactSupport.submodule F.presheaf) where
  smul_assoc c f s := Subtype.ext (by
    change testScalar (c • f) • (s : F.presheaf.obj (op ⊤)) =
      c • testScalar f • (s : F.presheaf.obj (op ⊤))
    rw [map_smul, smul_assoc])

/-- The canonical complex structure of the nondegenerate module is the original one. -/
theorem complexModule_eq (hX : Langlands.Topology.IsLocallyProfinite X) :
    NondegenerateScalars.complexModule PointwiseTestAlgebra.isIdempotented
        (isNondegenerate F hX) =
      (inferInstance : Module ℂ (CompactSupport.submodule F.presheaf)) :=
  NondegenerateScalars.module_eq_of_compatible ℂ _ _

section Morphisms

variable {F} {G H : VectorSheaf X}

/-- The published compact-section map of a sheaf morphism, as a test-module map. -/
def compactSectionMap (φ : F ⟶ G) :
    NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X)
      (CompactSupport.submodule F.presheaf) (CompactSupport.submodule G.presheaf) where
  toAddMonoidHom := (CompactSupport.map φ.hom).toAddMonoidHom
  map_smul' f s := Subtype.ext (app_smul φ (testScalar f) s.1)

@[simp]
theorem coe_compactSectionMap (φ : F ⟶ G) (s : CompactSupport.submodule F.presheaf) :
    (compactSectionMap φ s : G.presheaf.obj (op ⊤)) = φ.hom.app (op ⊤) s.1 := rfl

theorem compactSectionMap_eq (φ : F ⟶ G) (s : CompactSupport.submodule F.presheaf) :
    compactSectionMap φ s = CompactSupport.map φ.hom s := rfl

end Morphisms

/-- Renard II.2.5 Theorem: the compact-section functor to nondegenerate test modules,
on the original carriers `CompactSupport.submodule F.presheaf`. -/
def compactSectionFunctor (hX : Langlands.Topology.IsLocallyProfinite X) :
    VectorSheaf X ⥤ NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier X) where
  obj F := ⟨NonUnitalModuleCat.of _ (CompactSupport.submodule F.presheaf), isNondegenerate F hX⟩
  map φ := ObjectProperty.homMk (compactSectionMap φ)
  map_id F := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro s
    rfl
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro s
    rfl

@[simp]
theorem compactSectionFunctor_obj_carrier (hX : Langlands.Topology.IsLocallyProfinite X)
    (F : VectorSheaf X) :
    ((compactSectionFunctor hX).obj F).obj.carrier = CompactSupport.submodule F.presheaf := rfl

@[simp]
theorem compactSectionFunctor_map_hom (hX : Langlands.Topology.IsLocallyProfinite X)
    {F G : VectorSheaf X} (φ : F ⟶ G) :
    ((compactSectionFunctor hX).map φ).hom = compactSectionMap φ := rfl

/-- The underlying maps are those of the published `CompactSupport.functor`. -/
theorem compactSectionMap_eq_functor_map {F G : VectorSheaf X} (φ : F ⟶ G)
    (s : CompactSupport.submodule F.presheaf) :
    compactSectionMap φ s = (CompactSupport.functor (X := TopCat.of X) (R := ℂ)).map φ s := rfl

end Langlands.Sheaf.Renard.CompactSectionTestModule
