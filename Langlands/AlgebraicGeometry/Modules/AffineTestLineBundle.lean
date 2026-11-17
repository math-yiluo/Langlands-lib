import Langlands.AlgebraicGeometry.Modules.AffineTestComparison
import Langlands.AlgebraicGeometry.Picard.LineBundleLocusRestriction
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs

/-! # Line bundles and global sections from affine test systems

If the associated sheaves of the chart modules of an affine test system are locally free of rank
one, its realization is a line bundle. A global section of the realization has a value in the
module of every affine test, compatible with coefficient extension.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules

namespace AffineTestSystem

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard ProperFormalCoherentExistenceOfFLT

variable {S : Scheme.{u}} (E : AffineTestSystem S)

section LineBundle

/-- The realization is locally free of rank one when the associated sheaves of the chart modules
of all affine opens are. -/
theorem isLocallyFreeRankOne_toModules
    (h : ∀ (U : S.Opens) (hU : IsAffineOpen U), IsLocallyFreeRankOne (tilde (E.obj hU.fromSpec))) :
    IsLocallyFreeRankOne E.toModules := by
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hx : x ∈ hU.fromSpec.opensRange := by
    rw [hU.opensRange_fromSpec]
    exact hxU
  obtain ⟨q, hq⟩ := hx
  have h1 : IsLocallyFreeRankOne (E.toModules.restrict hU.fromSpec) :=
    (h U hU).of_iso ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app E.toModules ≪≫
      E.frame hU.fromSpec).symm
  have hq' : q ∈ rankOneLocus (E.toModules.restrict hU.fromSpec) :=
    (mem_rankOneLocus _ q).mpr (h1 q)
  rw [rankOneLocus_restrict] at hq'
  apply (mem_rankOneLocus _ x).mp
  change hU.fromSpec q ∈ rankOneLocus E.toModules at hq'
  simpa only [hq] using hq'

/-- The realization as a line bundle. -/
def toLineBundle
    (h : ∀ (U : S.Opens) (hU : IsAffineOpen U), IsLocallyFreeRankOne (tilde (E.obj hU.fromSpec))) :
    LineBundle S :=
  ⟨E.toModules, E.isLocallyFreeRankOne_toModules h⟩

end LineBundle

section Eval

variable {R : CommRingCat.{u}} (a : Spec R ⟶ S)

lemma top_le_preimage_top {X Y : Scheme.{u}} (f : X ⟶ Y) : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

/-- `topLinear` as a linear equivalence. -/
def topEquiv : E.obj a ≃ₗ[R] (moduleSpecΓFunctor (R := R)).obj (E.pullback a).toModules :=
  LinearEquiv.ofBijective (E.topLinear a) (E.topLinear_bijective a)

/-- The value on the affine test `a` of a global section of the realization. -/
def evalTop (s : Γ(E.toModules, ⊤)) : E.obj a :=
  (E.topEquiv a).symm ((comparison (E.toPullback a)).app ⊤
    (sectionPullbackLE a E.toModules (top_le_preimage_top a) s))

lemma topLinear_evalTop (s : Γ(E.toModules, ⊤)) :
    E.topLinear a (E.evalTop a s) = (comparison (E.toPullback a)).app ⊤
      (sectionPullbackLE a E.toModules (top_le_preimage_top a) s) :=
  (E.topEquiv a).apply_symm_apply _

lemma evalTop_add (s t : Γ(E.toModules, ⊤)) :
    E.evalTop a (s + t) = E.evalTop a s + E.evalTop a t := by
  apply (E.topLinear_bijective a).injective
  rw [map_add, topLinear_evalTop, topLinear_evalTop, topLinear_evalTop, sectionPullbackLE_add,
    map_add]

/-- **Coherence of the values of a global section.** For an `R`-algebra `A` and
`b = Spec A ⟶ Spec R ⟶ S`, the value on `b` is the coefficient extension of the value on `a`. -/
theorem evalTop_ext {A : CommRingCat.{u}} [Algebra R A] {b : Spec A ⟶ S}
    (h : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b) (s : Γ(E.toModules, ⊤)) :
    E.evalTop b s = E.ext h (1 ⊗ₜ E.evalTop a s) := by
  subst h
  rw [ext_one_tmul]
  apply (E.map_bijective_of_isIso (Scheme.ΓSpecIso A).inv
    (specMap_ΓSpecIso_inv_comp _)).injective
  rw [← sectionsEquiv_topLinear, topLinear_evalTop]
  have hA := comparison_comp (E.toPullback a)
    (E.pullbackComp a (Spec.map (CommRingCat.ofHom (algebraMap R A))))
  rw [toPullback_comp_pullbackComp] at hA
  rw [hA, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply,
    pullbackComp_inv_sectionPullbackLE _ a E.toModules (top_le_preimage_top a)
      (top_le_preimage_top _)]
  erw [pullback_map_sectionPullbackLE _ (comparison (E.toPullback a)) (top_le_preimage_top _)
    (sectionPullbackLE a E.toModules (top_le_preimage_top a) s)]
  rw [← topLinear_evalTop, sectionsEquiv_comparison_app _ (isAffineOpen_top (Spec R))
    (isAffineOpen_top (Spec A)) (top_le_preimage_top _), sectionsEquiv_topLinear, chartMap_apply,
    pullbackComp_app, pullback_map', E.map_map, E.transport_map _ _ _ (by
      rw [Spec.map_comp, Category.assoc, specMap_ΓSpecIso_inv_comp, ← Category.assoc,
        IsAffineOpen.SpecMap_appLE_fromSpec _ (isAffineOpen_top (Spec R))
          (isAffineOpen_top (Spec A)) (top_le_preimage_top _), Category.assoc]), E.map_map]
  refine E.map_congr ?_ _ _ _
  rw [ringHom_top_eq, show (homOfLE (le_top : (⊤ : (Spec A).Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id, Category.comp_id]

end Eval

section Trivialization

variable {R : CommRingCat.{u}} (a : Spec R ⟶ S)

lemma tilde_toOpen_one :
    (show Γ(SheafOfModules.unit (Spec R).ringCatSheaf, ⊤) from
      tilde.toOpen (ModuleCat.of R R) ⊤ (1 : R)) =
      (show Γ(SheafOfModules.unit (Spec R).ringCatSheaf, ⊤) from (1 : Γ(Spec R, ⊤))) :=
  StructureSheaf.const_one _

lemma pullbackUnitIso_hom_one :
    (pullbackUnitIso a).hom.app ⊤ (sectionPullbackLE a (SheafOfModules.unit S.ringCatSheaf)
      (top_le_preimage_top a) (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : Γ(S, ⊤)))) =
      (show Γ(SheafOfModules.unit (Spec R).ringCatSheaf, ⊤) from (1 : Γ(Spec R, ⊤))) := by
  have h := homEquiv_app_apply a (pullbackUnitIso a).hom ⊤
    (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : Γ(S, ⊤)))
  rw [pullbackUnitAdjunction (Spec R) S a] at h
  rw [sectionPullbackLE, ← OpenCoverHomGluing.hom_map_app, ← h,
    show (homOfLE (top_le_preimage_top a)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  exact map_one (a.app ⊤).hom

lemma pullbackUnitIso_inv_one :
    (pullbackUnitIso a).inv.app ⊤
      (show Γ(SheafOfModules.unit (Spec R).ringCatSheaf, ⊤) from (1 : Γ(Spec R, ⊤))) =
      sectionPullbackLE a (SheafOfModules.unit S.ringCatSheaf) (top_le_preimage_top a)
        (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : Γ(S, ⊤))) := by
  rw [← pullbackUnitIso_hom_one a]
  have := congrArg (fun φ => φ.app ⊤ (sectionPullbackLE a (SheafOfModules.unit S.ringCatSheaf)
      (top_le_preimage_top a) (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : Γ(S, ⊤)))))
    (pullbackUnitIso a).hom_inv_id
  simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using this

variable (ψ : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ≅ E.toModules)

/-- The global generator of the realization given by a trivialization `𝒪_S ≅ E.toModules`. -/
def generator : Γ(E.toModules, ⊤) :=
  Scheme.Modules.Hom.app ψ.hom ⊤
    (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : Γ(S, ⊤)))

/-- The isomorphism `R^~ ≅ (E.obj a)^~` obtained by pulling back a trivialization along `a`
and applying the frame of `a`. -/
def frameIso : tilde (ModuleCat.of R R) ≅ tilde (E.obj a) :=
  tildeSelf ≪≫ (pullbackUnitIso a).symm ≪≫ (Scheme.Modules.pullback a).mapIso ψ ≪≫ E.frame a

lemma frame_hom_app_sectionPullbackLE (s : Γ(E.toModules, ⊤)) :
    (E.frame a).hom.app ⊤ (sectionPullbackLE a E.toModules (top_le_preimage_top a) s) =
      tilde.toOpen (E.obj a) ⊤ (E.evalTop a s) := by
  have h1 := congrArg (fun φ => φ.app ⊤ (tilde.toOpen (E.obj a) ⊤ (E.evalTop a s)))
    (asIso (E.tildeComparison a)).hom_inv_id
  simp only [asIso_hom, asIso_inv, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h1
  rw [tildeComparison_app_toOpen, topLinear_evalTop] at h1
  exact h1

lemma frameIso_hom_app_toOpen_one :
    (E.frameIso a ψ).hom.app ⊤ (tilde.toOpen (ModuleCat.of R R) ⊤ (1 : R)) =
      tilde.toOpen (E.obj a) ⊤ (E.evalTop a (E.generator ψ)) := by
  rw [← frame_hom_app_sectionPullbackLE, generator,
    ← pullback_map_sectionPullbackLE a ψ.hom (top_le_preimage_top a), ← pullbackUnitIso_inv_one]
  change ((E.frame a).hom.app ⊤ (((Scheme.Modules.pullback a).map ψ.hom).app ⊤
    ((pullbackUnitIso a).inv.app ⊤ (tilde.toOpen (ModuleCat.of R R) ⊤ (1 : R))))) = _
  exact congrArg (fun y => (E.frame a).hom.app ⊤ (((Scheme.Modules.pullback a).map ψ.hom).app ⊤
    ((pullbackUnitIso a).inv.app ⊤ y))) (tilde_toOpen_one (R := R))

/-- The frame `R → E.obj a`, `r ↦ r • evalTop a (generator ψ)`, as a morphism of modules. -/
def trivFrameHom : ModuleCat.of R R ⟶ E.obj a :=
  ConcreteCategory.ofHom (C := ModuleCat R) (X := ModuleCat.of R R) (Y := E.obj a)
    (LinearMap.toSpanSingleton R (E.obj a) (E.evalTop a (E.generator ψ)))

lemma tilde_map_trivFrameHom : tilde.map (E.trivFrameHom a ψ) = (E.frameIso a ψ).hom := by
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  ext1
  apply LinearMap.ext_ring
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (tilde.map (E.trivFrameHom a ψ)).app ⊤ (tilde.toOpen (ModuleCat.of R R) ⊤ (1 : R)) =
    (E.frameIso a ψ).hom.app ⊤ (tilde.toOpen (ModuleCat.of R R) ⊤ (1 : R))
  rw [frameIso_hom_app_toOpen_one]
  refine (ConcreteCategory.congr_hom (tilde.toOpen_map_app (E.trivFrameHom a ψ) ⊤) 1).trans ?_
  change tilde.toOpen (E.obj a) ⊤ ((1 : R) • E.evalTop a (E.generator ψ)) = _
  rw [one_smul]

lemma trivFrame_bijective :
    Function.Bijective (LinearMap.toSpanSingleton R (E.obj a) (E.evalTop a (E.generator ψ))) := by
  have : IsIso ((tilde.functor R).map (E.trivFrameHom a ψ)) := by
    change IsIso (tilde.map (E.trivFrameHom a ψ))
    rw [tilde_map_trivFrameHom]
    infer_instance
  have : IsIso (E.trivFrameHom a ψ) := isIso_of_reflects_iso _ (tilde.functor R)
  exact ConcreteCategory.bijective_of_isIso (E.trivFrameHom a ψ)

/-- **The frame of a trivialization.** A trivialization `𝒪_S ≅ E.toModules` gives, for every
affine test `a : Spec R ⟶ S`, the linear equivalence `R ≃ E.obj a`, `r ↦ r • e_a`, where `e_a` is
the value on `a` of the global generator. -/
def trivFrame : R ≃ₗ[R] E.obj a :=
  LinearEquiv.ofBijective _ (E.trivFrame_bijective a ψ)

lemma trivFrame_apply (r : R) : E.trivFrame a ψ r = r • E.evalTop a (E.generator ψ) :=
  rfl

lemma trivFrame_one : E.trivFrame a ψ 1 = E.evalTop a (E.generator ψ) := by
  rw [trivFrame_apply, one_smul]

/-- **Coherence of the frames of a trivialization**: on `b = Spec A ⟶ Spec R ⟶ S` the frame
vector is the coefficient extension of the frame vector on `a`. -/
theorem trivFrame_ext {A : CommRingCat.{u}} [Algebra R A] {b : Spec A ⟶ S}
    (h : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b) :
    E.trivFrame b ψ 1 = E.ext h (1 ⊗ₜ E.trivFrame a ψ 1) := by
  rw [trivFrame_one, trivFrame_one, evalTop_ext E a h]

end Trivialization

section Picard

variable (h : ∀ (U : S.Opens) (hU : IsAffineOpen U),
  IsLocallyFreeRankOne (tilde (E.obj hU.fromSpec)))
  (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S))

/-- Under the hypothesis that every line bundle on `S` is trivial, a chosen trivialization of
the realization. -/
def picardTrivialization : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ≅ E.toModules :=
  ((LineBundle.forget S).mapIso (hPic (E.toLineBundle h)).some).symm

/-- Under the hypothesis that every line bundle on `S` is trivial, chosen frames
`R ≃ E.obj a` on all affine tests, coherent under coefficient extension
(`picardFrame_ext`). -/
def picardFrame {R : CommRingCat.{u}} (a : Spec R ⟶ S) : R ≃ₗ[R] E.obj a :=
  E.trivFrame a (E.picardTrivialization h hPic)

theorem picardFrame_ext {R A : CommRingCat.{u}} [Algebra R A] (a : Spec R ⟶ S) {b : Spec A ⟶ S}
    (hab : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b) :
    E.picardFrame h hPic b 1 = E.ext hab (1 ⊗ₜ E.picardFrame h hPic a 1) :=
  E.trivFrame_ext a _ hab

end Picard

end AffineTestSystem

end Langlands.AlgebraicGeometry.Modules
