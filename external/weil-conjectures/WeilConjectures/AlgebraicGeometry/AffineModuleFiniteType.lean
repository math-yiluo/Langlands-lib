/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineModuleCorrespondence
import WeilConjectures.AlgebraicGeometry.AffinePushforwardFreeEvaluation
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Finite type under the affine module correspondence

Source: Stacks Project, Cohomology of Schemes, Tag 0897, proof; Morphisms, Tag 01SB;
Properties, Tag 01PB (blueprint: lem-weil-pbc-affine-module-finite-type).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

section SiteHelpers

universe v w

open SheafOfModules CategoryTheory.Limits

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  {R₀ : Sheaf J RingCat.{u}}
  [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

private theorem finiteType_of_data {M : SheafOfModules.{u} R₀}
    (q : M.LocalGeneratorsData) [hq : q.IsFiniteType] : M.IsFiniteType := by
  have : q.shrink.IsFiniteType := by
    constructor
    intro i
    exact hq.isFiniteType i.2.choose
  constructor
  exact ⟨q.shrink, this⟩

private theorem finiteType_of_generators {M : SheafOfModules.{u} R₀}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasBinaryProducts C] (g : M.GeneratingSections) [g.IsFiniteType] :
    M.IsFiniteType := by
  have : g.localGeneratorsData.IsFiniteType := by
    constructor
    intro x
    dsimp [SheafOfModules.GeneratingSections.localGeneratorsData]
    infer_instance
  exact finiteType_of_data g.localGeneratorsData

private theorem finiteType_of_iso {M N : SheafOfModules.{u} R₀} (e : M ≅ N)
    [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  let q' : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (e.hom.over (q.X i)) }
  have : q'.IsFiniteType := by
    constructor
    intro i
    have := hq.isFiniteType i
    exact inferInstanceAs ((q.generators i).ofEpi _).IsFiniteType
  exact finiteType_of_data q'

end SiteHelpers

private theorem affine_generators_cover {X : Scheme.{u}}
    {S : X.toTopCat.Sheaf RingCat.{u}} (M : SheafOfModules.{u} S) [M.IsFiniteType] :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} M, q.IsFiniteType ∧ ∀ i, IsAffineOpen (q.X i) := by
  classical
  obtain ⟨p, hp⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let q : M.LocalGeneratorsData :=
    { I := Σ i : p.I, { V : X.affineOpens // V.1 ≤ p.X i }
      X i := i.2.1.1
      coversTop := by
        apply (Opens.coversTop_iff _ _).mpr
        apply eq_top_iff.mpr
        intro x _
        have hx : x ∈ ⨆ i, p.X i := by
          rw [(Opens.coversTop_iff _ _).mp p.coversTop]
          trivial
        obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
        obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset hi
        exact Opens.mem_iSup.mpr ⟨⟨i, ⟨⟨V, hV⟩, hle⟩⟩, hxV⟩
      generators i :=
        ((p.generators i.1).map (SheafOfModules.overMap S (homOfLE i.2.2))
          (SheafOfModules.overMapUnitIso (R := S) (homOfLE i.2.2)).symm).ofEpi
            ((SheafOfModules.overFunctorMap S (homOfLE i.2.2)).app M).hom }
  refine ⟨q, ?_, fun i ↦ i.2.1.2⟩
  constructor
  intro i
  have := hp.isFiniteType i.1
  dsimp [q]
  infer_instance

/-- Finite generation at a terminal object gives finite generating sections whenever
finite free evaluation detects epimorphisms. -/
private theorem finite_generators_iff_finite_terminal_sections
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R₀ : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (N : SheafOfModules.{u} R₀) (T : C) (hT : CategoryTheory.Limits.IsTerminal T)
    (hepi : ∀ (I : Type u) [Finite I] (s : I → N.sections),
      Epi (N.freeHomEquiv.symm s) ↔
        Function.Surjective ((N.freeHomEquiv.symm s).val.app (.op T))) :
    (∃ σ : N.GeneratingSections, Finite σ.I) ↔
      Module.Finite (R₀.obj.obj (.op T)) (N.val.obj (.op T)) := by
  classical
  constructor
  · rintro ⟨σ, hσ⟩
    let : Fintype σ.I := Fintype.ofFinite σ.I
    have hf : Module.Finite (R₀.obj.obj (.op T))
        ((SheafOfModules.free (R := R₀) σ.I).val.obj (.op T)) :=
      Module.Finite.equiv
        (SheafOfModules.freeSectionsLinearEquiv (R := R₀) σ.I (.op T)).symm
    have hsurj := (hepi σ.I σ.s).mp σ.epi
    exact Module.Finite.of_surjective (σ.π.val.app (.op T)).hom hsurj
  · intro h
    have : Module.Finite (R₀.obj.obj (.op T)) (N.val.obj (.op T)) := h
    obtain ⟨k, t, ht⟩ := Module.Finite.exists_fin
      (R := (R₀).obj.obj (.op T)) (M := N.val.obj (.op T))
    let τ (W : Cᵒᵖ) : W.unop ⟶ T := hT.from W.unop
    let s : ULift.{u} (Fin k) → N.sections := fun i ↦
      PresheafOfModules.sectionsMk
        (fun W ↦ N.val.map (τ W).op (t i.down))
        (fun W Z g ↦ by
          change N.val.presheaf.map g (N.val.presheaf.map (τ W).op (t i.down)) =
            N.val.presheaf.map (τ Z).op (t i.down)
          rw [← Functor.map_comp_apply]
          have hcomp : (τ W).op ≫ g = (τ Z).op := by
            apply Quiver.Hom.unop_inj
            exact hT.hom_ext _ _
          rw [hcomp])
    let φ := N.freeHomEquiv.symm s
    have hsurj : Function.Surjective (φ.val.app (.op T)) := by
      let L := (φ.val.app (.op T)).hom
      apply LinearMap.range_eq_top.mp
      apply top_unique
      rw [← ht]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      refine ⟨(SheafOfModules.freeSection (R := R₀)
        (ULift.up i : ULift.{u} (Fin k))).1 (.op T), ?_⟩
      have he := congrArg (fun a : N.sections ↦ a.1 (.op T))
        (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s (ULift.up i))
      have hτ : τ (.op T) = 𝟙 T := by
        exact hT.hom_ext _ _
      change (φ.val.app (.op T))
        ((SheafOfModules.freeSection (R := R₀)
          (ULift.up i : ULift.{u} (Fin k))).1 (.op T)) =
            N.val.presheaf.map (τ (.op T)).op (t i) at he
      rw [hτ] at he
      simpa only [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using he
    have hφ : Epi φ :=
      (hepi (ULift.{u} (Fin k)) s).mpr hsurj
    exact ⟨{ I := ULift.{u} (Fin k), s := s, epi := hφ }, inferInstance⟩

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "AR" => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj A
set_option hygiene false in
local notation "PUSH" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := AR) (R := U.ringCatSheaf) (𝟙 AR)

/-- On one affine open, finite global generators of the direct image over its
sectionwise algebra are equivalent to finite generation of the inverse-image sections.
Source: Stacks Project, Morphisms, Tag 01SB; Properties, Tag 01PB; Cohomology of
Schemes, Tag 0897, proof, finite-type detail
(blueprint: lem-weil-pbc-affine-module-finite-type), steps 2 and 3.

Proof:
1. Put W = f⁻¹ V and B = O_U(W). W is affine. Sections of f_*F over V, including
   their B-action and restrictions, are definitionally sections of F over W.
2. Given a finite generating family for (f_*F)|V, regard its sections as sections
   on W and form the evaluation map O_W^n → F|W. For each t in F(W), generation
   on V expresses t locally as combinations of these sections. Pull those opens
   back to W. Thus t lies in the sheaf image of evaluation. Since evaluation is
   between quasi-coherent modules on the affine W, the affine-sections image formula
   (Stacks 01IC) expresses t as a B-linear combination of the same finite family.
3. Conversely choose finitely many B-module generators of F(W). The affine
   tilde-Gamma equivalence shows their evaluation map O_W^n → F|W is surjective.
   On each affine V' contained in V its inverse image W' is affine; the same
   image formula gives a lift of every section of F(W') to O_U(W')^n. These
   coefficients are exactly sections of A on V'. The affine V' cover every open
   contained in V, so the family generates (f_*F)|V as an A|V-module.
No finite-type assumption on either sheaf is made in this local assertion. -/
private theorem affine_pushforward_finite_generators [IsAffineHom f]
    (F : U.Modules) (hF : F.IsQuasicoherent) (V : X.Opens) (hV : IsAffineOpen V) :
    (∃ σ : ((PUSH).obj F |>.over V).GeneratingSections, Finite σ.I) ↔
      Module.Finite Γ(U, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V)  := by
  exact finite_generators_iff_finite_terminal_sections
    (((PUSH).obj F).over V) (Over.mk (𝟙 V)) CategoryTheory.Over.mkIdTerminal
    (affine_pushforward_free_evaluation f F hF V hV)


set_option hygiene false in
local notation "R" => PUSH

/-- Finite type is preserved in both directions by the affine module correspondence.
The direct image carries its sectionwise action by `A = f_* O_U`, rather than merely
its restricted `O_X`-action. Source: Stacks Project, Tag 0897, proof (the omitted
finite-type detail), with Tags 01SB and 01PB
(blueprint: lem-weil-pbc-affine-module-finite-type).

Proof (the five steps of the node):
1. Transport finite generation through the given `A`-linear isomorphism, reducing to
   `M = f_* F` (`lem-weil-pbc-affine-module-correspondence`). An epimorphism from a
   finite free module means every section is locally a linear combination of its
   basis images (`situation-conventions`,
   `def-weil-pbc-module-finite-type-presentation`). Generation restricts to smaller
   opens. Affine opens form a basis, and their inverse images are affine.
2. On an affine open `V` of `X`, set `B = O_U(f⁻¹ V)`. A finite family generating
   `M|_V` over `A|_V` generates `F(f⁻¹ V)` over `B`: form the map from the finite
   free quasi-coherent module on `f⁻¹ V` and use the affine-sections image formula
   (`lem-weil-pbc-quasi-coherent-module-cokernel-image`), together with
   `lem-weil-pbc-module-restriction-open-immersion-colimits` and
   `lem-weil-pbc-spec-tilde-free-module`.
3. Conversely, sections generating `F|_(f⁻¹ V)` generate `M|_V`: cover any open
   inside `V` by affine opens. On their affine inverse images the same image formula
   supplies the coefficients, now read as sections of `A`.
4. If `M` is finite type, choose generators near `f(y)` and shrink to an affine
   neighbourhood. Step 2 gives a finite `B`-module of sections. Apply
   `lem-weil-pbc-quasi-coherent-finite-type-affine` to get finite type near `y`.
5. If `F` is finite type, that same affine criterion gives a finite `B`-module of
   sections on every affine inverse image. Its generators generate the sheaf by
   `lem-weil-pbc-affine-finite-type-generating-sections`. Step 3 gives generators
   over `A` near every point of `X`. These prove the asserted equivalence. -/
theorem affine_module_finite_type [IsAffineHom f]
    (M : SheafOfModules.{u} AR) (hM : M.IsQuasicoherent)
    (F : U.Modules) (hF : F.IsQuasicoherent) (e : (R).obj F ≅ M) :
    M.IsFiniteType ↔ F.IsFiniteType := by
  classical
  have _ : M.IsQuasicoherent := hM
  let N := (R).obj F
  have hcriterion := (quasicoherent_finite_type_affine.{u, u} U).2 F hF
  constructor
  · intro h
    have : N.IsFiniteType := finiteType_of_iso (R₀ := AR) e.symm
    obtain ⟨q, hq, hqa⟩ := affine_generators_cover N
    have hcover : (⨆ i, f ⁻¹ᵁ q.X i) = ⊤ := by
      apply eq_top_iff.mpr
      intro y _
      have hy : f.base y ∈ ⨆ i, q.X i := by
        rw [(Opens.coversTop_iff _ _).mp q.coversTop]
        trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
      exact Opens.mem_iSup.mpr ⟨i, hi⟩
    exact (hcriterion.2.1 q.I
      (fun i ↦ f ⁻¹ᵁ q.X i) hcover (fun i ↦ (hqa i).preimage f)
      (fun i ↦ (affine_pushforward_finite_generators f F hF (q.X i) (hqa i)).mp
        ⟨q.generators i, (hq.isFiniteType i).finite⟩)).1
  · intro h
    obtain ⟨q, hq, hqa⟩ := affine_generators_cover F
    have hsections :=
      (hcriterion.2.1 q.I q.X
        ((Opens.coversTop_iff _ _).mp q.coversTop) hqa (fun i ↦ by
          have := hq.isFiniteType i
          exact (hcriterion.1
            (q.X i) (hqa i)).1.mp
              (finiteType_of_generators (R₀ := U.ringCatSheaf.over (q.X i)) (q.generators i)))).2
    have hgen (V : X.affineOpens) :
        ∃ σ : (N.over V.1).GeneratingSections, Finite σ.I :=
      (affine_pushforward_finite_generators f F hF V.1 V.2).mpr
        (hsections (f ⁻¹ᵁ V.1) (V.2.preimage f))
    choose σ hσ using hgen
    let p : N.LocalGeneratorsData :=
      { I := X.affineOpens
        X V := V.1
        coversTop := by
          apply (Opens.coversTop_iff _ _).mpr
          apply eq_top_iff.mpr
          intro x _
          obtain ⟨V, hV, hxV, -⟩ :=
            exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
          exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩
        generators V := σ V }
    have : p.IsFiniteType := by
      constructor
      intro V
      exact ⟨hσ V⟩
    have : N.IsFiniteType := finiteType_of_data (R₀ := AR) p
    exact finiteType_of_iso (R₀ := AR) e

end
end AlgebraicGeometry.Scheme.Modules
