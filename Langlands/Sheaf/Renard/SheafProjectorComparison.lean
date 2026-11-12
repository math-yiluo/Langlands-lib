import Langlands.Sheaf.Renard.CompactSectionTestModule
import Langlands.Sheaf.Renard.ProjectorSheafFunctor
import Langlands.Sheaf.Renard.BasisMathlibSheafEquivalence
import Langlands.Sheaf.CompactGerms
import Langlands.Sheaf.Renard.ProjectorVectorSheaf

/-!
# The original-sheaf comparison with the projector sheaf of compact sections

Renard (9 July 2026), II.2.5, end of the proof of the Theorem, printed p.40 / PDF p.46:
for a compact open `U`, `χ_U · M = χ_U · M(U) = M(U)` with `M = M_c(X)`.
A section `s` over an open `V` gives, on each compact open `U ⊆ V`, the zero extension
of `s|_U`, which is a compact section fixed by `χ_U`.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.SheafProjectorComparison

open CategoryTheory TopologicalSpace Opposite
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Renard.VectorSheafScalars Langlands.Sheaf.Renard.CompactSectionTestModule
open Langlands.Sheaf.Renard.ProjectorBasisSheaf

variable {X : Type} [TopologicalSpace X] (F : VectorSheaf X)

/-- Global germs of the published zero extension inside the clopen. -/
theorem Γgerm_extend_of_mem (U : Opens X) (hU : IsClosed (U : Set X))
    (t : F.presheaf.obj (op U)) {x : X} (h : x ∈ U) :
    F.presheaf.Γgerm x (CompactGerms.extend F U hU t) = F.presheaf.germ U x h t := by
  conv_rhs => rw [← CompactGerms.restrict_extend F U hU t]
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

/-- Global germs of the published zero extension vanish outside the clopen. -/
theorem Γgerm_extend_of_not_mem (U : Opens X) (hU : IsClosed (U : Set X))
    (t : F.presheaf.obj (op U)) {x : X} (h : x ∉ U) :
    F.presheaf.Γgerm x (CompactGerms.extend F U hU t) = 0 := by
  by_contra hne
  exact h (CompactGerms.support_extend_subset F U hU t hne)

/-- Stalk maps of sheaf morphisms on global germs. -/
theorem Γgerm_app {G : VectorSheaf X} (φ : F ⟶ G) (m : F.presheaf.obj (op ⊤)) (x : X) :
    G.presheaf.Γgerm x (φ.hom.app (op ⊤) m) =
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).map φ.hom (F.presheaf.Γgerm x m) := by
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply (X := TopCat.of X)
    (C := ModuleCat.{0} ℂ) (F := F.presheaf) (G := G.presheaf) ⊤ x trivial φ.hom m
  exact h.symm

variable (hX : Langlands.Topology.IsLocallyProfinite X)

/-- The zero extension of the restriction of `s` to a compact open `U ≤ V`. -/
def extension {V : Opens X} (U : CompactOpen hX) (hUV : U.obj ≤ V)
    (s : F.presheaf.obj (op V)) : CompactSupport.submodule F.presheaf :=
  CompactGerms.compactExtension F U.obj (clopen hX U).isClosed (compact hX U)
    (F.presheaf.map (homOfLE hUV).op s)

/-- Germs of the extension inside `U` are those of `s`. -/
theorem Γgerm_extension_of_mem {V : Opens X} (U : CompactOpen hX) (hUV : U.obj ≤ V)
    (s : F.presheaf.obj (op V)) {x : X} (h : x ∈ U.obj) :
    F.presheaf.Γgerm x (extension F hX U hUV s : F.presheaf.obj (op ⊤)) =
      F.presheaf.germ V x (hUV h) s := by
  change F.presheaf.Γgerm x (CompactGerms.extend F U.obj _ _) = _
  rw [Γgerm_extend_of_mem F U.obj _ _ h]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- Germs of the extension vanish outside `U`. -/
theorem Γgerm_extension_of_not_mem {V : Opens X} (U : CompactOpen hX) (hUV : U.obj ≤ V)
    (s : F.presheaf.obj (op V)) {x : X} (h : x ∉ U.obj) :
    F.presheaf.Γgerm x (extension F hX U hUV s : F.presheaf.obj (op ⊤)) = 0 :=
  Γgerm_extend_of_not_mem F U.obj _ _ h

/-- Extensions are equal when their germs agree. -/
theorem ext_compact {s t : CompactSupport.submodule F.presheaf}
    (h : ∀ x : X, F.presheaf.Γgerm x (s : F.presheaf.obj (op ⊤)) =
      F.presheaf.Γgerm x (t : F.presheaf.obj (op ⊤))) : s = t :=
  Subtype.ext (ext_germ F fun x _ => h x)

/-- The extension is fixed by the characteristic idempotent of `U`. -/
theorem extension_mem_fixedPart {V : Opens X} (U : CompactOpen hX) (hUV : U.obj ≤ V)
    (s : F.presheaf.obj (op V)) :
    extension F hX U hUV s ∈ NonUnitalModuleCorner.fixedPart (idempotent hX U)
      (CompactSupport.submodule F.presheaf) :=
  characteristic_smul_eq_self F (clopen hX U) (compact hX U) _
    (CompactGerms.support_extend_subset F U.obj _ _)

/-- The compact-open component of the comparison: `s ↦ (s|_U extended by zero)`. -/
def component {V : Opens X} (s : F.presheaf.obj (op V))
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) :
    Value hX (CompactSupport.submodule F.presheaf) U.val :=
  ⟨extension F hX U.val U.property s, extension_mem_fixedPart F hX U.val U.property s⟩

@[simp]
theorem component_val {V : Opens X} (s : F.presheaf.obj (op V))
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) :
    (component F hX s U).val = extension F hX U.val U.property s := rfl

/-- The projector restriction of a component is the smaller component. -/
theorem action_extension {V : Opens X} {U W : CompactOpen hX} (hUV : U.obj ≤ V)
    (hWU : W.obj ≤ U.obj) (s : F.presheaf.obj (op V)) :
    action hX (CompactSupport.submodule F.presheaf) W (extension F hX U hUV s) =
      extension F hX W (hWU.trans hUV) s := by
  apply ext_compact F
  intro x
  change F.presheaf.Γgerm x ((test hX W • extension F hX U hUV s :
    CompactSupport.submodule F.presheaf) : F.presheaf.obj (op ⊤)) = _
  rw [Γgerm_testSmul]
  change (W.obj : Set X).indicator (fun _ => (1 : ℂ)) x • _ = _
  by_cases hxW : x ∈ W.obj
  · rw [Set.indicator_of_mem hxW, one_smul, Γgerm_extension_of_mem F hX U hUV s (hWU hxW),
      Γgerm_extension_of_mem F hX W _ s hxW]
  · rw [Set.indicator_of_notMem hxW, zero_smul, Γgerm_extension_of_not_mem F hX W _ s hxW]

/-- The compatible family of components over an arbitrary open `V`. -/
def family {V : Opens X} (s : F.presheaf.obj (op V)) :
    BasisAllOpen.Families (rawPresheaf hX (CompactSupport.submodule F.presheaf)) V :=
  ⟨component F hX s, fun U _ h => Subtype.ext (action_extension F hX U.property h s)⟩

@[simp]
theorem family_apply_val {V : Opens X} (s : F.presheaf.obj (op V))
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) :
    ((family F hX s).val U).val = extension F hX U.val U.property s := rfl

/-- The comparison on sections over `V`, as an additive map. -/
def familyHom (V : Opens X) :
    F.presheaf.obj (op V) →+
      BasisAllOpen.Families (rawPresheaf hX (CompactSupport.submodule F.presheaf)) V where
  toFun := family F hX
  map_zero' := by
    apply BasisAllOpen.families_ext
    intro U
    apply Subtype.ext
    apply ext_compact F
    intro x
    change F.presheaf.Γgerm x (extension F hX U.val U.property 0 : F.presheaf.obj (op ⊤)) =
      F.presheaf.Γgerm x 0
    rw [map_zero]
    by_cases hx : x ∈ U.val.obj
    · rw [Γgerm_extension_of_mem F hX _ _ _ hx, map_zero]
    · rw [Γgerm_extension_of_not_mem F hX _ _ _ hx]
  map_add' s t := by
    apply BasisAllOpen.families_ext
    intro U
    apply Subtype.ext
    apply ext_compact F
    intro x
    change F.presheaf.Γgerm x (extension F hX U.val U.property (s + t) :
        F.presheaf.obj (op ⊤)) =
      F.presheaf.Γgerm x ((extension F hX U.val U.property s : F.presheaf.obj (op ⊤)) +
        (extension F hX U.val U.property t : F.presheaf.obj (op ⊤)))
    rw [map_add]
    by_cases hx : x ∈ U.val.obj
    · rw [Γgerm_extension_of_mem F hX _ _ _ hx, Γgerm_extension_of_mem F hX _ _ _ hx,
        Γgerm_extension_of_mem F hX _ _ _ hx, map_add]
    · rw [Γgerm_extension_of_not_mem F hX _ _ _ hx, Γgerm_extension_of_not_mem F hX _ _ _ hx,
        Γgerm_extension_of_not_mem F hX _ _ _ hx, add_zero]

@[simp]
theorem familyHom_apply (V : Opens X) (s : F.presheaf.obj (op V)) :
    familyHom F hX V s = family F hX s := rfl

/-- The components are complex-linear for the original structure on compact sections. -/
theorem extension_smul {V : Opens X} (U : CompactOpen hX) (hUV : U.obj ≤ V) (c : ℂ)
    (s : F.presheaf.obj (op V)) :
    extension F hX U hUV (c • s) = c • extension F hX U hUV s := by
  apply ext_compact F
  intro x
  change F.presheaf.Γgerm x (extension F hX U hUV (c • s) : F.presheaf.obj (op ⊤)) =
    F.presheaf.Γgerm x (c • (extension F hX U hUV s : F.presheaf.obj (op ⊤)))
  rw [map_smul]
  by_cases hx : x ∈ U.obj
  · rw [Γgerm_extension_of_mem F hX _ _ _ hx, Γgerm_extension_of_mem F hX _ _ _ hx, map_smul]
  · rw [Γgerm_extension_of_not_mem F hX _ _ _ hx, Γgerm_extension_of_not_mem F hX _ _ _ hx,
      smul_zero]

/-- Restriction to a smaller open discards components (naturality in the open). -/
theorem family_restrict {U V : Opens X} (h : U ≤ V) (s : F.presheaf.obj (op V)) :
    BasisAllOpen.familyRestriction (rawPresheaf hX (CompactSupport.submodule F.presheaf)) h
        (family F hX s) =
      family F hX (F.presheaf.map (homOfLE h).op s) := by
  apply BasisAllOpen.families_ext
  intro W
  apply Subtype.ext
  apply ext_compact F
  intro x
  change F.presheaf.Γgerm x (extension F hX W.val (W.property.trans h) s :
      F.presheaf.obj (op ⊤)) =
    F.presheaf.Γgerm x (extension F hX W.val W.property (F.presheaf.map (homOfLE h).op s) :
      F.presheaf.obj (op ⊤))
  by_cases hx : x ∈ W.val.obj
  · rw [Γgerm_extension_of_mem F hX _ _ _ hx, Γgerm_extension_of_mem F hX _ _ _ hx]
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  · rw [Γgerm_extension_of_not_mem F hX _ _ _ hx, Γgerm_extension_of_not_mem F hX _ _ _ hx]

section Naturality

variable {F} {G : VectorSheaf X}

/-- Compact-section maps commute with the extensions (naturality in the sheaf). -/
theorem map_extension (φ : F ⟶ G) {V : Opens X} (U : CompactOpen hX) (hUV : U.obj ≤ V)
    (s : F.presheaf.obj (op V)) :
    compactSectionMap φ (extension F hX U hUV s) =
      extension G hX U hUV (φ.hom.app (op V) s) := by
  apply ext_compact G
  intro x
  rw [coe_compactSectionMap, Γgerm_app]
  by_cases hx : x ∈ U.obj
  · rw [Γgerm_extension_of_mem F hX _ _ _ hx, Γgerm_extension_of_mem G hX _ _ _ hx]
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _
  · rw [Γgerm_extension_of_not_mem F hX _ _ _ hx, Γgerm_extension_of_not_mem G hX _ _ _ hx]
    exact map_zero _

/-- Naturality of the families in sheaf morphisms. -/
theorem familyMap_family (φ : F ⟶ G) {V : Opens X} (s : F.presheaf.obj (op V)) :
    BasisAllOpen.familyMap (rawMap hX (compactSectionMap φ)) V (family F hX s) =
      family G hX (φ.hom.app (op V) s) := by
  apply BasisAllOpen.families_ext
  intro U
  apply Subtype.ext
  exact map_extension hX φ U.val U.property s

end Naturality

/-- The additive comparison `F → P(Γc F)` on actual additive sheaves, with components
`s ↦ (U ↦ s|_U extended by zero)` on every open. -/
def additiveComparison :
    CompactGerms.additive F ⟶
      (BasisMathlib.toMathlib.{0, 0} (compactOpenBasis hX)).obj
        ((nondegenerateFunctor.{0, 0} hX).obj ((compactSectionFunctor hX).obj F)) :=
  ObjectProperty.homMk
    { app V := AddCommGrpCat.ofHom (familyHom F hX V.unop)
      naturality U V f := by
        ext s
        exact (family_restrict F hX (leOfHom f.unop) s).symm }

@[simp]
theorem additiveComparison_app_apply (V : Opens X) (s : F.presheaf.obj (op V)) :
    (additiveComparison F hX).hom.app (op V) s = family F hX s := rfl

/-- Naturality of the additive comparison in the original vector sheaf. -/
def additiveComparisonNat :
    sheafCompose (Opens.grothendieckTopology (TopCat.of X))
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) ⟶
      compactSectionFunctor hX ⋙ nondegenerateFunctor.{0, 0} hX ⋙
        BasisMathlib.toMathlib.{0, 0} (compactOpenBasis hX) where
  app F := additiveComparison F hX
  naturality F G φ := by
    apply ObjectProperty.hom_ext
    ext V s
    exact (familyMap_family hX φ s).symm

/-! ### The complex-linear comparison -/

/-- The comparison on sections over `V` is complex-linear for the canonical complex
structure of `ProjectorVectorSheaf`, which is componentwise the original one. -/
def sheafComparisonApp (V : Opens X) :
    F.presheaf.obj (op V) ⟶ ProjectorVectorSheaf.familySpace.{0, 0} hX (isNondegenerate F hX) V :=
  letI := ProjectorVectorSheaf.familyModule.{0, 0} hX (isNondegenerate F hX) V
  ModuleCat.ofHom
    { toFun := family F hX
      map_add' := (familyHom F hX V).map_add
      map_smul' c s := by
        apply BasisAllOpen.families_ext
        intro U
        apply Subtype.ext
        change extension F hX U.val U.property (c • s) =
          NondegenerateScalars.scalarMul ℂ (isNondegenerate F hX) c
            (extension F hX U.val U.property s)
        rw [extension_smul, NondegenerateScalars.scalarMul_eq_of_compatible] }

@[simp]
theorem sheafComparisonApp_apply (V : Opens X) (s : F.presheaf.obj (op V)) :
    (sheafComparisonApp F hX V).hom s = family F hX s := rfl

/-- Renard II.2.5, end of the proof: the original-sheaf comparison
`F ⟶ P(Γc F)`, `s ↦ (U ↦ s|_U extended by zero)` on compact opens `U`. -/
def sheafComparison :
    F ⟶ (ProjectorVectorSheaf.functor.{0, 0} hX).obj ((compactSectionFunctor hX).obj F) :=
  ObjectProperty.homMk
    { app V := sheafComparisonApp F hX V.unop
      naturality U V f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact (family_restrict F hX (leOfHom f.unop) s).symm }

/-- The literal compact-open formula of the comparison. -/
@[simp]
theorem sheafComparison_app_val {V : Opens X} (s : F.presheaf.obj (op V))
    (U : BasisAllOpen.Inside (compactOpenBasis hX) V) :
    ((((sheafComparison F hX).hom.app (op V)).hom s).val U).val =
      CompactGerms.compactExtension F U.val.obj (clopen hX U.val).isClosed
        (compact hX U.val) (F.presheaf.map (homOfLE U.property).op s) := rfl

/-- Forgetting the complex structure gives the additive comparison. -/
theorem sheafComparison_forget₂ {V : Opens X} (s : F.presheaf.obj (op V)) :
    ((sheafComparison F hX).hom.app (op V)).hom s =
      (additiveComparison F hX).hom.app (op V) s := rfl

/-- Naturality of the original-sheaf comparison in sheaf morphisms. -/
def sheafComparisonNat :
    𝟭 (VectorSheaf X) ⟶ compactSectionFunctor hX ⋙ ProjectorVectorSheaf.functor.{0, 0} hX where
  app F := sheafComparison F hX
  naturality F G φ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact (familyMap_family hX φ s).symm

end Langlands.Sheaf.Renard.SheafProjectorComparison
