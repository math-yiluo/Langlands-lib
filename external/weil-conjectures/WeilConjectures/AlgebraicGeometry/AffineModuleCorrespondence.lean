/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorConstruction
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorComparisonIsIso
import WeilConjectures.AlgebraicGeometry.QuasiCoherenceScalarRestriction
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Quasi-coherent modules along an affine morphism

Source: Stacks Project, Morphisms, Lemma 01SB
(blueprint: lem-weil-pbc-affine-module-correspondence).

The algebra `B = u^* A` is specified by its tensor-product universal property: the pushout
of `u⁻¹ O_X → O_U` and `u⁻¹ O_X → u⁻¹ A` in commutative ring sheaves. The functor `P`
is extension of scalars from `u⁻¹ A` to `B`; `κ` identifies its underlying module with the
recorded tensor pullback. Its formula on the pullback unit fixes this identification.
Thus the action is `(b ⊗ a)(b' ⊗ g) = bb' ⊗ ag`. The functor `H` is extension of
scalars along the multiplication counit `ε : B → O_U`, with the target scalar first
in the tensor notation. No alternative pullback or tensor product is defined here.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

local instance instHasLeftKanExtension_affineModuleCorrespondence
    : ∀ (F : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}),
    (Opens.map f.base).op.HasLeftKanExtension F := fun F ↦ by
  have : (Opens.map f.base).op.HasPointwiseLeftKanExtension F := fun _ ↦ inferInstance
  exact Functor.HasLeftKanExtension.mk _
    (Functor.pointwiseLeftKanExtensionUnit (Opens.map f.base).op F)

set_option hygiene false in
local notation "𝓙" T => Opens.grothendieckTopology T
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "ρ" => (show X.sheaf ⟶ A from ⟨f.c⟩)
set_option hygiene false in
local notation "R" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := 𝓡 A) (R := U.ringCatSheaf) (𝟙 (𝓡 A))
set_option hygiene false in
local notation "S" => SheafOfModules.restrictScalars.{u} (𝓻 ρ)
set_option hygiene false in
local notation "I" => TopCat.Sheaf.inverseImageModule f.base A
set_option hygiene false in
local notation "IA" => TopCat.Sheaf.inverseImageRing f.base A
set_option hygiene false in
local notation "r₀" => tensorPullbackRingMap f
set_option hygiene false in
local notation "t₀" => (TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map ρ
set_option hygiene false in
local notation "e₀" =>
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)).homEquiv A U.sheaf).symm (𝟙 A)
set_option hygiene false in
local notation "adj₀" => Classical.choose (exists_tensorPullbackAdjunction f)
set_option hygiene false in
local notation "qU" => SheafOfModules.isQuasicoherent U.ringCatSheaf
set_option hygiene false in
local notation "qA" => SheafOfModules.isQuasicoherent (𝓡 A)

private theorem equivalence_on_full_subcategories
    {C D : Type*} [Category C] [Category D] (p : ObjectProperty C) (q : ObjectProperty D)
    (F : C ⥤ D) (G : D ⥤ C)
    (hF : ∀ X, p X → q (F.obj X)) (hG : ∀ Y, q Y → p (G.obj Y))
    (α : F ⋙ G ⟶ 𝟭 C) (β : 𝟭 D ⟶ G ⋙ F)
    (hα : ∀ X, p X → IsIso (α.app X)) (hβ : ∀ Y, q Y → IsIso (β.app Y)) :
    ∃ E : p.FullSubcategory ≌ q.FullSubcategory,
      Nonempty (E.functor ⋙ q.ι ≅ p.ι ⋙ F) ∧
      Nonempty (E.inverse ⋙ p.ι ≅ q.ι ⋙ G) := by
  let F' := q.lift (p.ι ⋙ F) (fun X ↦ hF X.obj X.property)
  let G' := p.lift (q.ι ⋙ G) (fun Y ↦ hG Y.obj Y.property)
  let a : F' ⋙ G' ≅ 𝟭 p.FullSubcategory :=
    NatIso.ofComponents (fun X ↦ by
      let := hα X.obj X.property
      exact ObjectProperty.isoMk _ (asIso (α.app X.obj))) (by
        intro X Y f
        apply InducedCategory.hom_ext
        exact α.naturality f.hom)
  let b : 𝟭 q.FullSubcategory ≅ G' ⋙ F' :=
    NatIso.ofComponents (fun Y ↦ by
      let := hβ Y.obj Y.property
      exact ObjectProperty.isoMk _ (asIso (β.app Y.obj))) (by
        intro X Y f
        apply InducedCategory.hom_ext
        exact β.naturality f.hom)
  exact ⟨CategoryTheory.Equivalence.mk F' G' a.symm b.symm, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩

/-- For an affine morphism, pushforward gives the equivalence of quasi-coherent modules
with quasi-coherent modules over its direct-image algebra. Quasi-coherence is unchanged
by restriction to the structure sheaf. The inverse is the two tensor operations in 01SB,
and the canonical counit-induced `α` and adjoint `β` are isomorphisms.
Source: Stacks Project, Morphisms, Lemma 01SB
(blueprint: lem-weil-pbc-affine-module-correspondence).

Proof:
1. The direct-image algebra is quasi-coherent by affine relative Spec
   (`lem-weil-pbc-affine-morphism-relative-spec`). Apply quasi-coherence under scalar
   restriction (`lem-weil-pbc-quasi-coherence-scalar-restriction`) to obtain clause (1).
2. Pushforward has the sectionwise algebra action and sends quasi-coherent modules to
   quasi-coherent modules (`pqf-lem-pushforward-qcoh`), since an affine morphism is
   quasi-compact and separated, hence quasi-separated.
3. Form the pulled-back algebra by the tensor pushout, and the pulled-back module by
   extension of scalars. Associativity of tensor products gives `κ`, with its stated
   formula. The counit is multiplicative and induces `ε`, hence the second extension
   of scalars `H`. Pullback and change of rings preserve quasi-coherence
   (`lem-weil-pbc-module-pullback-quasi-coherent`,
   `lem-weil-pbc-quasi-coherent-algebra-change-of-rings`). The tensor unit gives `γ`.
   The ordinary counit factors uniquely through it to give `α`; its adjoint gives `β`.
4. On an affine open `V` with inverse image `W`, the affine-sections pullback formula
   (`lem-weil-pbc-module-pullback-affine-sections`) identifies `H(G)(W)` with
   `(N ⊗_R B) ⊗_(B ⊗_R B) B`, where `N = G(V)`. The balanced map
   `(n ⊗ b) ⊗ c ↦ bc n` has inverse `n ↦ (n ⊗ 1) ⊗ 1`: move `b` and `c`
   through the balancing relation. Both are linear for the last-factor action.
5. Under this identification `α` is the balanced map and `β` its inverse. Their
   components are bijections on the affine covers. Apply
   `lem-weil-pbc-quasi-coherent-iso-on-affine-cover` to get isomorphisms. The maps
   are natural, and `β` is algebra-linear (check on affine opens, then glue).
6. Restrict these functors and natural isomorphisms to the full quasi-coherent
   subcategories, obtaining the asserted equivalence with inverse `H`. -/
theorem affine_module_correspondence [IsAffineHom f] :
    (∀ G : SheafOfModules.{u} (𝓡 A), G.IsQuasicoherent ↔ ((S).obj G).IsQuasicoherent) ∧
    (∀ F : U.Modules, F.IsQuasicoherent → ((R).obj F).IsQuasicoherent) ∧
    ∃ (B : U.toTopCat.Sheaf CommRingCat.{u})
      (b : U.sheaf ⟶ B) (t : IA ⟶ B) (ε : B ⟶ U.sheaf),
      IsPushout r₀ t₀ b t ∧ b ≫ ε = 𝟙 U.sheaf ∧ t ≫ ε = e₀ ∧
      ∃ (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f),
        (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
          P.map a = eqToHom (pobj G) ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} t (I G)
              (TopCat.Sheaf.inverseImageModuleMap f.base A G a) ≫
            eqToHom (pobj G').symm) ∧
        (∀ (G : SheafOfModules.{u} (𝓡 A)) (V : (Opens X)ᵒᵖ) (g : G.val.obj V),
          ((eqToHom (pobj G)).val.app ((Opens.map f.base).op.obj V))
            ((κ.inv.app G).val.app ((Opens.map f.base).op.obj V)
              (((adj₀).unit.app ((S).obj G)).val.app V g)) =
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t (I G))).app
                ((Opens.map f.base).op.obj V)
                ((1 : B.obj.obj ((Opens.map f.base).op.obj V)) ⊗ₜ[
                  (IA).obj.obj ((Opens.map f.base).op.obj V),
                  (t.hom.app ((Opens.map f.base).op.obj V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))) ∧
        ∃ (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
          (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G))
          (γ : S ⋙ tensorPullback f ⟶ H),
          (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
            H.map a = eqToHom (hobj G) ≫
              SheafOfModules.changeOfRingsHom.{u, u, u} ε (P.obj G) (P.map a) ≫
              eqToHom (hobj G').symm) ∧
          (∀ (G : SheafOfModules.{u} (𝓡 A)) (W : (Opens U)ᵒᵖ)
              (p : (P.obj G).val.obj W),
            ((eqToHom (hobj G)).val.app W)
              ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) =
              ((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
                (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
                  ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W, (ε.hom.app W).hom] p)) ∧
          (∀ G : SheafOfModules.{u} (𝓡 A),
            G.IsQuasicoherent → (H.obj G).IsQuasicoherent) ∧
          ∃ (α : R ⋙ H ⟶ 𝟭 U.Modules) (β : 𝟭 (SheafOfModules.{u} (𝓡 A)) ⟶ H ⋙ R),
            (∀ F : U.Modules, γ.app ((R).obj F) ≫ α.app F = (adj₀).counit.app F) ∧
            (∀ G : SheafOfModules.{u} (𝓡 A),
              (S).map (β.app G) = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G)) ∧
            (∀ F : U.Modules, F.IsQuasicoherent → IsIso (α.app F)) ∧
            (∀ G : SheafOfModules.{u} (𝓡 A), G.IsQuasicoherent → IsIso (β.app G)) ∧
            ∃ E : (qU).FullSubcategory ≌ (qA).FullSubcategory,
              Nonempty (E.functor ⋙ (qA).ι ≅ (qU).ι ⋙ R) ∧
              Nonempty (E.inverse ⋙ (qU).ι ≅ (qA).ι ⋙ H) := by
  classical
  -- Cache the sheafification instances shared by the quasi-coherence predicates.
  let : ∀ V : Opens X,
      HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u} :=
    fun _ ↦ inferInstance
  let : ∀ V : Opens U,
      HasWeakSheafify ((Opens.grothendieckTopology U).over V) AddCommGrpCat.{u} :=
    fun _ ↦ inferInstance
  let : ∀ V : Opens X,
      ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun _ ↦ inferInstance
  let : ∀ V : Opens U,
      ((Opens.grothendieckTopology U).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun _ ↦ inferInstance
  let RA := 𝓡 A
  let Rf : U.Modules ⥤ SheafOfModules.{u} RA := R
  let Sf : SheafOfModules.{u} RA ⥤ X.Modules := S
  let pU := qU
  let pA := qA
  let pX := SheafOfModules.isQuasicoherent X.ringCatSheaf
  have hqc (G : SheafOfModules.{u} RA) :
      pA G ↔ pX (Sf.obj G) := by
    exact quasiCoherent_iff_restrictScalars X (Under.mk ρ)
      ((affine_morphism_relative_spec X).1 f inferInstance) G
  have hpush (F : U.Modules) (hF : pU F) :
      pA (Rf.obj F) := by
    have : F.IsQuasicoherent := hF
    let := IsSeparated.of_isAffineHom f
    apply (hqc (Rf.obj F)).mpr
    exact isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f F
  refine ⟨hqc, hpush, ?_⟩
  -- Rebuild each existential as it is unpacked, keeping the dependent goals small.
  refine Exists.elim (affine_module_tensor_construction f) (fun B hB ↦ ?_)
  refine ⟨B, ?_⟩
  refine Exists.elim hB (fun b hb ↦ ?_)
  refine ⟨b, ?_⟩
  refine Exists.elim hb (fun t ht ↦ ?_)
  refine ⟨t, ?_⟩
  refine Exists.elim ht (fun ε hring ↦ ?_)
  refine ⟨ε, hring.1, hring.2.1, hring.2.2.1, ?_⟩
  refine Exists.elim hring.2.2.2 (fun P hP₀ ↦ ?_)
  refine ⟨P, ?_⟩
  refine Exists.elim hP₀ (fun pobj hP₁ ↦ ?_)
  refine ⟨pobj, ?_⟩
  refine Exists.elim hP₁ (fun κ hP ↦ ?_)
  refine ⟨κ, hP.1, hP.2.1, ?_⟩
  refine Exists.elim hP.2.2 (fun H hH₀ ↦ ?_)
  refine ⟨H, ?_⟩
  refine Exists.elim hH₀ (fun hobj hH₁ ↦ ?_)
  refine ⟨hobj, ?_⟩
  refine Exists.elim hH₁ (fun γ hH ↦ ?_)
  refine ⟨γ, hH.1, hH.2.1, hH.2.2.1, ?_⟩
  refine Exists.elim hH.2.2.2 (fun α hβ₀ ↦ ?_)
  refine ⟨α, ?_⟩
  refine Exists.elim hβ₀ (fun β hcomp ↦ ?_)
  refine ⟨β, hcomp.1, hcomp.2, ?_⟩
  have hiso := affine_module_tensor_comparison_isIso f B b t ε
    ⟨hring.1, hring.2.1, hring.2.2.1⟩ P pobj κ ⟨hP.1, hP.2.1⟩ H hobj γ
    ⟨hH.1, hH.2.1, hH.2.2.1⟩ α β hcomp
  refine ⟨hiso.1, hiso.2, ?_⟩
  exact equivalence_on_full_subcategories pU pA Rf H hpush hH.2.2.1 α β hiso.1 hiso.2

end
end AlgebraicGeometry.Scheme.Modules
