import Langlands.Sheaf.Renard.CompactSectionStalksProof
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Isomorphisms of sheaves over a homeomorphism

Renard (9 July 2026), II.2.5, last two paragraphs, printed pp.42–43 / PDF pp.48–49.
A homeomorphism `γ : X → Y` of t.d. spaces gives the algebra isomorphism
`D(Y) ≃ D(X)`, `g ↦ g ∘ γ`. An isomorphism between `F ∈ C^∞_X-Mod(X)` and
`E ∈ C^∞_Y-Mod(Y)` is a homeomorphism `γ` with an isomorphism of `D(X)`-modules
`F_c(X) ≃ E_c(Y)`. It induces complex isomorphisms of stalks `F_x ≃ E_{γ(x)}`, and its
transpose is a map `E_c(Y)^* → F_c(X)^*` of algebraic duals.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.HomeomorphSheafIso

open CategoryTheory Opposite
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Renard.VectorSheafScalars Langlands.Sheaf.Renard.CompactSectionTestModule
open Langlands.Sheaf.Renard.CompactSectionStalks

universe uX uY uM

/-! ### The algebra isomorphism `D(Y) ≃ D(X)` -/

section TestAlgebra

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]

/-- Renard's algebra map `D(Y) → D(X)`, `g ↦ g ∘ γ`, on the published pointwise
test algebras. -/
def testComap (γ : X ≃ₜ Y) :
    PointwiseTestAlgebra.Carrier Y →ₙₐ[ℂ] PointwiseTestAlgebra.Carrier X where
  toFun g := ⟨g.val.comap (γ : C(X, Y)), g.property.comp_homeomorph γ⟩
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem testComap_apply (γ : X ≃ₜ Y) (g : PointwiseTestAlgebra.Carrier Y) (x : X) :
    testComap γ g x = g (γ x) := rfl

@[simp]
theorem testComap_symm_testComap (γ : X ≃ₜ Y) (g : PointwiseTestAlgebra.Carrier Y) :
    testComap γ.symm (testComap γ g) = g :=
  PointwiseTestAlgebra.ext fun y => congrArg g (γ.apply_symm_apply y)

@[simp]
theorem testComap_testComap_symm (γ : X ≃ₜ Y) (f : PointwiseTestAlgebra.Carrier X) :
    testComap γ (testComap γ.symm f) = f :=
  PointwiseTestAlgebra.ext fun x => congrArg f (γ.symm_apply_apply x)

/-- Renard's algebra isomorphism `D(Y) ≃ D(X)` induced by `γ`, as a ring isomorphism;
it is complex-linear by `testComap`. -/
def testRingEquiv (γ : X ≃ₜ Y) :
    PointwiseTestAlgebra.Carrier Y ≃+* PointwiseTestAlgebra.Carrier X where
  toFun := testComap γ
  invFun := testComap γ.symm
  left_inv := testComap_symm_testComap γ
  right_inv := testComap_testComap_symm γ
  map_mul' := map_mul (testComap γ)
  map_add' := map_add (testComap γ)

@[simp]
theorem testRingEquiv_apply (γ : X ≃ₜ Y) (g : PointwiseTestAlgebra.Carrier Y) :
    testRingEquiv γ g = testComap γ g := rfl

@[simp]
theorem testRingEquiv_symm_apply (γ : X ≃ₜ Y) (f : PointwiseTestAlgebra.Carrier X) :
    (testRingEquiv γ).symm f = testComap γ.symm f := rfl

/-- Through `D(Y) ≃ D(X)`, a `D(Y)`-module is a `D(X)`-module:
`f · m = (f ∘ γ⁻¹) · m`. This is not a global instance. -/
@[instance_reducible]
def transportModule (γ : X ≃ₜ Y) (M : Type uM) [AddCommGroup M]
    [h : NonUnitalModule (PointwiseTestAlgebra.Carrier Y) M] :
    NonUnitalModule (PointwiseTestAlgebra.Carrier X) M :=
  NonUnitalModule.ofEndHom
    ((NonUnitalModule.toEndHom h).comp
      (testComap γ.symm : PointwiseTestAlgebra.Carrier X →ₙ+* PointwiseTestAlgebra.Carrier Y))

theorem transportModule_smul (γ : X ≃ₜ Y) {M : Type uM} [AddCommGroup M]
    [NonUnitalModule (PointwiseTestAlgebra.Carrier Y) M]
    (f : PointwiseTestAlgebra.Carrier X) (m : M) :
    (letI := transportModule γ M; f • m) = testComap γ.symm f • m := rfl

end TestAlgebra

/-! ### Isomorphisms of sheaves over a homeomorphism -/

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Renard II.2.5: an isomorphism between the complex vector sheaves `F` on `X` and `E`
on `Y` is a homeomorphism `γ : X → Y` together with an isomorphism of `D(X)`-modules
between the compact sections `F_c(X)` and `E_c(Y)`, where `D(X)` acts on `E_c(Y)` through
the algebra isomorphism `D(X) ≃ D(Y)`, `f ↦ f ∘ γ⁻¹`. The module isomorphism is an
additive bijection intertwining the actions, as for the published nondegenerate module
categories. -/
structure SheafIso (F : VectorSheaf X) (E : VectorSheaf Y) where
  /-- The underlying homeomorphism `γ : X → Y`. -/
  homeomorph : X ≃ₜ Y
  /-- The isomorphism of compact sections `F_c(X) ≃ E_c(Y)`. -/
  sectionEquiv : CompactSupport.submodule F.presheaf ≃+ CompactSupport.submodule E.presheaf
  /-- `D(X)`-linearity for the transported action on `E_c(Y)`. -/
  map_smul' : ∀ (f : PointwiseTestAlgebra.Carrier X) (s : CompactSupport.submodule F.presheaf),
    sectionEquiv (f • s) = testComap homeomorph.symm f • sectionEquiv s

namespace SheafIso

variable {F : VectorSheaf X} {E : VectorSheaf Y} (Φ : SheafIso F E)

theorem map_smul (f : PointwiseTestAlgebra.Carrier X) (s : CompactSupport.submodule F.presheaf) :
    Φ.sectionEquiv (f • s) = testComap Φ.homeomorph.symm f • Φ.sectionEquiv s :=
  Φ.map_smul' f s

/-- The same intertwining, read with `g ∈ D(Y)`: `Φ((g ∘ γ) · s) = g · Φ(s)`. -/
theorem map_testComap_smul (g : PointwiseTestAlgebra.Carrier Y)
    (s : CompactSupport.submodule F.presheaf) :
    Φ.sectionEquiv (testComap Φ.homeomorph g • s) = g • Φ.sectionEquiv s := by
  rw [map_smul, testComap_symm_testComap]

/-- The section isomorphism is a `D(X)`-module map for the transported action on `E_c(Y)`. -/
def toModuleHom :
    letI := transportModule Φ.homeomorph (CompactSupport.submodule E.presheaf)
    NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X)
      (CompactSupport.submodule F.presheaf) (CompactSupport.submodule E.presheaf) :=
  letI := transportModule Φ.homeomorph (CompactSupport.submodule E.presheaf)
  { toAddMonoidHom := Φ.sectionEquiv.toAddMonoidHom
    map_smul' := Φ.map_smul' }

@[simp]
theorem toModuleHom_apply (s : CompactSupport.submodule F.presheaf) :
    Φ.toModuleHom s = Φ.sectionEquiv s := rfl

/-- The identity isomorphism over the identity homeomorphism. -/
def refl (F : VectorSheaf X) : SheafIso F F where
  homeomorph := Homeomorph.refl X
  sectionEquiv := AddEquiv.refl _
  map_smul' f s := by
    congr 1

/-- The inverse isomorphism, over `γ⁻¹`. -/
def symm : SheafIso E F where
  homeomorph := Φ.homeomorph.symm
  sectionEquiv := Φ.sectionEquiv.symm
  map_smul' g t := by
    apply Φ.sectionEquiv.injective
    rw [AddEquiv.apply_symm_apply, map_smul, Homeomorph.symm_symm,
      testComap_symm_testComap, AddEquiv.apply_symm_apply]

@[simp]
theorem symm_homeomorph : Φ.symm.homeomorph = Φ.homeomorph.symm := rfl

@[simp]
theorem symm_sectionEquiv : Φ.symm.sectionEquiv = Φ.sectionEquiv.symm := rfl

/-- Composition of isomorphisms, over the composite homeomorphism. -/
def trans {Z : Type} [TopologicalSpace Z] {G : VectorSheaf Z} (Ψ : SheafIso E G) :
    SheafIso F G where
  homeomorph := Φ.homeomorph.trans Ψ.homeomorph
  sectionEquiv := Φ.sectionEquiv.trans Ψ.sectionEquiv
  map_smul' f s := by
    change Ψ.sectionEquiv (Φ.sectionEquiv (f • s)) = _
    rw [map_smul, map_smul]
    rfl

@[simp]
theorem trans_homeomorph {Z : Type} [TopologicalSpace Z] {G : VectorSheaf Z}
    (Ψ : SheafIso E G) : (Φ.trans Ψ).homeomorph = Φ.homeomorph.trans Ψ.homeomorph := rfl

@[simp]
theorem trans_sectionEquiv {Z : Type} [TopologicalSpace Z] {G : VectorSheaf Z}
    (Ψ : SheafIso E G) : (Φ.trans Ψ).sectionEquiv = Φ.sectionEquiv.trans Ψ.sectionEquiv := rfl

/-- An ordinary isomorphism of sheaves on `X` is an isomorphism over the identity of `X`;
its section isomorphism is the published compact-section map. -/
def ofIso {G : VectorSheaf X} (φ : F ≅ G) : SheafIso F G where
  homeomorph := Homeomorph.refl X
  sectionEquiv :=
    { toFun := compactSectionMap φ.hom
      invFun := compactSectionMap φ.inv
      left_inv s := Subtype.ext (by
        change (φ.hom ≫ φ.inv).hom.app (op ⊤) s.1 = s.1
        rw [φ.hom_inv_id]
        rfl)
      right_inv t := Subtype.ext (by
        change (φ.inv ≫ φ.hom).hom.app (op ⊤) t.1 = t.1
        rw [φ.inv_hom_id]
        rfl)
      map_add' := (compactSectionMap φ.hom).map_add }
  map_smul' f s := (compactSectionMap φ.hom).map_smul f s

@[simp]
theorem ofIso_homeomorph {G : VectorSheaf X} (φ : F ≅ G) :
    (ofIso φ).homeomorph = Homeomorph.refl X := rfl

@[simp]
theorem ofIso_sectionEquiv_apply {G : VectorSheaf X} (φ : F ≅ G)
    (s : CompactSupport.submodule F.presheaf) :
    (ofIso φ).sectionEquiv s = CompactSupport.map φ.hom.hom s := rfl

/-! ### Complex linearity -/

/-- On a t.d. space the `D(X)`-isomorphism is complex-linear for the original complex
structures of the compact sections: a section `s` is fixed by an idempotent `e`, and
`c • s = (c • e) • s`. -/
theorem map_complex_smul (hX : Langlands.Topology.IsLocallyProfinite X) (c : ℂ)
    (s : CompactSupport.submodule F.presheaf) :
    Φ.sectionEquiv (c • s) = c • Φ.sectionEquiv s := by
  obtain ⟨e, he⟩ := isNondegenerate F hX s
  calc Φ.sectionEquiv (c • s)
      = Φ.sectionEquiv ((c • (e : PointwiseTestAlgebra.Carrier X)) • s) := by
        rw [smul_assoc, he]
    _ = c • (testComap Φ.homeomorph.symm (e : PointwiseTestAlgebra.Carrier X) •
          Φ.sectionEquiv s) := by
        rw [map_smul, _root_.map_smul, smul_assoc]
    _ = c • Φ.sectionEquiv s := by
        rw [← map_smul, he]

/-- The section isomorphism as a complex-linear equivalence, on a t.d. space `X`. -/
def linearEquiv (hX : Langlands.Topology.IsLocallyProfinite X) :
    CompactSupport.submodule F.presheaf ≃ₗ[ℂ] CompactSupport.submodule E.presheaf :=
  { Φ.sectionEquiv with map_smul' := Φ.map_complex_smul hX }

@[simp]
theorem linearEquiv_apply (hX : Langlands.Topology.IsLocallyProfinite X)
    (s : CompactSupport.submodule F.presheaf) :
    Φ.linearEquiv hX s = Φ.sectionEquiv s := rfl

@[simp]
theorem linearEquiv_symm_apply (hX : Langlands.Topology.IsLocallyProfinite X)
    (t : CompactSupport.submodule E.presheaf) :
    (Φ.linearEquiv hX).symm t = Φ.sectionEquiv.symm t := rfl

/-! ### Stalks -/

/-- The isomorphism carries the generators `f · s`, `f(x) = 0`, to the generators at
`γ(x)`. -/
theorem vanishingSpan_le_comap (hX : Langlands.Topology.IsLocallyProfinite X) (x : X) :
    vanishingSpan F x ≤
      (vanishingSpan E (Φ.homeomorph x)).comap (Φ.linearEquiv hX : _ →ₗ[ℂ] _) := by
  rw [vanishingSpan, Submodule.span_le]
  rintro _ ⟨f, s, hf, rfl⟩
  change Φ.sectionEquiv (f • s) ∈ vanishingSpan E (Φ.homeomorph x)
  rw [map_smul]
  apply smul_mem_vanishingSpan
  rw [testComap_apply, Homeomorph.symm_apply_apply, hf]

/-- The isomorphism maps Renard's span `⟨f · φ, f(x) = 0⟩` onto the span at `γ(x)`. -/
theorem map_vanishingSpan (hX : Langlands.Topology.IsLocallyProfinite X)
    (hY : Langlands.Topology.IsLocallyProfinite Y) (x : X) :
    (vanishingSpan F x).map (Φ.linearEquiv hX : _ →ₗ[ℂ] _) =
      vanishingSpan E (Φ.homeomorph x) := by
  apply le_antisymm
  · exact Submodule.map_le_iff_le_comap.mpr (Φ.vanishingSpan_le_comap hX x)
  · have h := Φ.symm.vanishingSpan_le_comap hY (Φ.homeomorph x)
    rw [symm_homeomorph, Homeomorph.symm_apply_apply] at h
    intro t ht
    refine ⟨Φ.sectionEquiv.symm t, h ht, ?_⟩
    exact Φ.sectionEquiv.apply_symm_apply t

/-- The induced isomorphism of Renard's quotients
`F_c(X)/⟨f · φ, f(x) = 0⟩ ≃ E_c(Y)/⟨g · ψ, g(γ(x)) = 0⟩`. -/
def quotientEquiv (hX : Langlands.Topology.IsLocallyProfinite X)
    (hY : Langlands.Topology.IsLocallyProfinite Y) (x : X) :
    (CompactSupport.submodule F.presheaf ⧸ vanishingSpan F x) ≃ₗ[ℂ]
      (CompactSupport.submodule E.presheaf ⧸ vanishingSpan E (Φ.homeomorph x)) :=
  Submodule.Quotient.equiv _ _ (Φ.linearEquiv hX) (Φ.map_vanishingSpan hX hY x)

@[simp]
theorem quotientEquiv_mk (hX : Langlands.Topology.IsLocallyProfinite X)
    (hY : Langlands.Topology.IsLocallyProfinite Y) (x : X)
    (s : CompactSupport.submodule F.presheaf) :
    Φ.quotientEquiv hX hY x (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk (Φ.sectionEquiv s) := rfl

/-- The published comparison `F_c(X)/⟨f · φ, f(x) = 0⟩ ≃ F_x` (Remark of II.2.5), as a
linear equivalence. -/
def stalkQuotientEquiv {Z : Type} [TopologicalSpace Z]
    (hZ : Langlands.Topology.IsLocallyProfinite Z) (G : VectorSheaf Z) (z : Z) :
    (CompactSupport.submodule G.presheaf ⧸ vanishingSpan G z) ≃ₗ[ℂ] G.presheaf.stalk z :=
  LinearEquiv.ofBijective (stalkQuotientMap G z) (stalkQuotientComparison Z hZ G z)

@[simp]
theorem stalkQuotientEquiv_mk {Z : Type} [TopologicalSpace Z]
    (hZ : Langlands.Topology.IsLocallyProfinite Z) (G : VectorSheaf Z) (z : Z)
    (s : CompactSupport.submodule G.presheaf) :
    stalkQuotientEquiv hZ G z (Submodule.Quotient.mk s) = CompactGerms.germ G z s := rfl

/-- Renard II.2.5: the induced complex isomorphism of stalks `F_x ≃ E_{γ(x)}`. -/
def stalkEquiv (hX : Langlands.Topology.IsLocallyProfinite X)
    (hY : Langlands.Topology.IsLocallyProfinite Y) (x : X) :
    F.presheaf.stalk x ≃ₗ[ℂ] E.presheaf.stalk (Φ.homeomorph x) :=
  (stalkQuotientEquiv hX F x).symm ≪≫ₗ Φ.quotientEquiv hX hY x ≪≫ₗ
    stalkQuotientEquiv hY E (Φ.homeomorph x)

/-- The stalk isomorphism sends the germ of a compact section `s` at `x` to the germ of
`Φ(s)` at `γ(x)`. -/
theorem stalkEquiv_germ (hX : Langlands.Topology.IsLocallyProfinite X)
    (hY : Langlands.Topology.IsLocallyProfinite Y) (x : X)
    (s : CompactSupport.submodule F.presheaf) :
    Φ.stalkEquiv hX hY x (CompactGerms.germ F x s) =
      CompactGerms.germ E (Φ.homeomorph x) (Φ.sectionEquiv s) := by
  have hs : (stalkQuotientEquiv hX F x).symm (CompactGerms.germ F x s) =
      Submodule.Quotient.mk s := by
    rw [LinearEquiv.symm_apply_eq, stalkQuotientEquiv_mk]
  rw [stalkEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply, hs]
  rfl

/-- The germ compatibility determines the stalk isomorphism, since every germ comes from a
compact section. -/
theorem eq_stalkEquiv (hX : Langlands.Topology.IsLocallyProfinite X)
    (hY : Langlands.Topology.IsLocallyProfinite Y) (x : X)
    (L : F.presheaf.stalk x →ₗ[ℂ] E.presheaf.stalk (Φ.homeomorph x))
    (hL : ∀ s : CompactSupport.submodule F.presheaf,
      L (CompactGerms.germ F x s) = CompactGerms.germ E (Φ.homeomorph x) (Φ.sectionEquiv s)) :
    L = (Φ.stalkEquiv hX hY x : _ →ₗ[ℂ] _) := by
  ext t
  obtain ⟨s, rfl⟩ := CompactGerms.germ_surjective F hX x t
  rw [hL, LinearEquiv.coe_coe, stalkEquiv_germ]

/-! ### Transposes -/

/-- Renard II.2.5: the transpose `E_c(Y)^* → F_c(X)^*` of the isomorphism, on the algebraic
duals of the compact sections, `T ↦ T ∘ Φ`. -/
def transpose (hX : Langlands.Topology.IsLocallyProfinite X) :
    Module.Dual ℂ (CompactSupport.submodule E.presheaf) ≃ₗ[ℂ]
      Module.Dual ℂ (CompactSupport.submodule F.presheaf) :=
  (Φ.linearEquiv hX).dualMap

@[simp]
theorem transpose_apply (hX : Langlands.Topology.IsLocallyProfinite X)
    (T : Module.Dual ℂ (CompactSupport.submodule E.presheaf))
    (s : CompactSupport.submodule F.presheaf) :
    Φ.transpose hX T s = T (Φ.sectionEquiv s) := rfl

/-- The transpose intertwines the test actions on the duals,
`⟨Φᵀ T, (g ∘ γ) · s⟩ = ⟨T, g · Φ(s)⟩` for `g ∈ D(Y)`. -/
theorem transpose_testComap_smul (hX : Langlands.Topology.IsLocallyProfinite X)
    (T : Module.Dual ℂ (CompactSupport.submodule E.presheaf))
    (g : PointwiseTestAlgebra.Carrier Y) (s : CompactSupport.submodule F.presheaf) :
    Φ.transpose hX T (testComap Φ.homeomorph g • s) = T (g • Φ.sectionEquiv s) := by
  rw [transpose_apply, map_testComap_smul]

end SheafIso

end Langlands.Sheaf.Renard.HomeomorphSheafIso
