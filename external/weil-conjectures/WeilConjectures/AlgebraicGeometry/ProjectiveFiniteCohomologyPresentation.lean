/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
import WeilConjectures.AlgebraicGeometry.ProjectiveTwistFiniteCohomology

/-! # A projective presentation with finite cohomology source

Source: Stacks Project, Tag 01YS, proof of Lemma 30.14.1 (1) and (3),
Tag 01Y6, Lemma 30.9.9, and Tag 01XT, Lemma 30.8.1.
(blueprint: lem-pc-u3-projective-finite-cohomology-presentation)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- For an affine open `U`, the global sections of the restriction of `M` along
`hU.fromSpec : Spec Γ(X, U) ⟶ X` are the sections of `M` over `U`, as `Γ(X, U)`-modules. -/
private noncomputable def sectionsTopRestrictFromSpecEquiv {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(M.restrict hU.fromSpec, ⊤) ≃ₗ[Γ(X, U)] Γ(M, U) where
  toFun x := M.presheaf.map (homOfLE (by rw [Hom.image_top_eq_opensRange,
    hU.opensRange_fromSpec])).op ((M.restrictAppIso hU.fromSpec ⊤).hom x)
  invFun y := (M.restrictAppIso hU.fromSpec ⊤).inv
    (M.presheaf.map (homOfLE (hU.fromSpec_image_le ⊤)).op y)
  map_add' x y := by simp
  map_smul' r x := by
    dsimp only
    rw [restrictAppIso_fromSpec_smul, map_smul, ← Functor.map_comp_apply,
      Subsingleton.elim (_ ≫ _ : Opposite.op U ⟶ Opposite.op U) (𝟙 _),
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, RingHom.id_apply]
  left_inv x := by
    dsimp only
    rw [← Functor.map_comp_apply,
      Subsingleton.elim (_ ≫ _ : Opposite.op (hU.fromSpec ''ᵁ ⊤) ⟶ _) (𝟙 _),
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, Iso.hom_inv_id_apply]
  right_inv y := by
    dsimp only
    rw [Iso.inv_hom_id_apply, ← Functor.map_comp_apply,
      Subsingleton.elim (_ ≫ _ : Opposite.op U ⟶ Opposite.op U) (𝟙 _),
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- Let `i : X ⟶ Y` be a morphism of schemes and `V` an open of `Y` such that
`i.app V : Γ(Y, V) ⟶ Γ(X, i ⁻¹ᵁ V)` is surjective. If `Γ(F, i ⁻¹ᵁ V)` is a finite
`Γ(X, i ⁻¹ᵁ V)`-module, then `Γ(i_* F, V)`, which is the same group with `Γ(Y, V)` acting through
`i.app V`, is a finite `Γ(Y, V)`-module. -/
private theorem finite_sections_pushforward_of_surjective {X Y : Scheme.{u}}
    (i : X ⟶ Y) (F : X.Modules)
    (V : Y.Opens) (hi : Function.Surjective (i.app V))
    [Module.Finite Γ(X, i ⁻¹ᵁ V) Γ(F, i ⁻¹ᵁ V)] :
    Module.Finite Γ(Y, V) Γ((pushforward i).obj F, V) := by
  let := (i.app V).hom.toAlgebra
  let : Module Γ(Y, V) Γ(F, i ⁻¹ᵁ V) := Module.compHom _ (i.app V).hom
  have : IsScalarTower Γ(Y, V) Γ(X, i ⁻¹ᵁ V) Γ(F, i ⁻¹ᵁ V) := ⟨fun a b m ↦ mul_smul _ _ _⟩
  have : Module.Finite Γ(Y, V) Γ(X, i ⁻¹ᵁ V) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) hi
  have := Module.Finite.trans Γ(X, i ⁻¹ᵁ V) Γ(F, i ⁻¹ᵁ V) (R := Γ(Y, V))
  exact Module.Finite.equiv
    { AddEquiv.refl _ with map_smul' _ _ := rfl :
      Γ(F, i ⁻¹ᵁ V) ≃ₗ[Γ(Y, V)] Γ((pushforward i).obj F, V) }

/-- Closed pushforward preserves coherent modules on a locally Noetherian target.

Source: Stacks Project, Tag 01Y6, Lemma 30.9.9.
(blueprint: lem-pc-closed-immersion-coherent-cohomology)

Proof: On an affine open Spec R of the target, the inverse image under the closed
immersion is Spec(R/I). The restriction of F is associated to a finitely presented
R/I-module M. Regard M as an R-module along the quotient map. Its generators over R/I
also generate it over R because R surjects onto R/I. Since R is Noetherian, M is finitely
presented over R. Localization of M as an R-module agrees with localization as an
R/I-module on inverse-image principal opens, giving an identification of the closed
pushforward with the associated R-module. These local identifications give
quasi-coherence and finite presentation on an affine cover, hence globally. This uses
only localization and sheaf gluing and no proper-cohomology finiteness. -/
private theorem closed_pushforward_coherent_independent {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (i : X ⟶ Y) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ((pushforward i).obj F).IsQuasicoherent ∧
      ((pushforward i).obj F).IsFinitePresentation := by
  have hqc : ((pushforward i).obj F).IsQuasicoherent := by
    refine isQuasicoherent_of_forall_isAffineOpen _ (fun W hW g s ↦ ?_) (fun W hW g t ht ↦ ?_)
    · obtain ⟨n, t, ht⟩ := exists_map_eq_pow_smul_of_basicOpen_eq F (hW.preimage i) (i.app W g)
        (i.preimage_basicOpen g).symm (i.preimage_mono (Y.basicOpen_le g)) s
      refine ⟨n, t, ht.trans ?_⟩
      have h : i.app (Y.basicOpen g) (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op g) =
          X.presheaf.map (homOfLE (i.preimage_mono (Y.basicOpen_le g))).op (i.app W g) := by
        rw [← ConcreteCategory.comp_apply, i.naturality]
        rfl
      rw [← h, ← map_pow]
      rfl
    · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_basicOpen_eq F (hW.preimage i) (i.app W g)
        (i.preimage_basicOpen g).symm (i.preimage_mono (Y.basicOpen_le g)) t ht
      rw [← map_pow] at hn
      exact ⟨n, hn⟩
  let := hqc
  refine ⟨hqc, ?_⟩
  let ι := {V : Y.Opens // IsAffineOpen V}
  have (j : ι) : Module.Finite Γ(X, i ⁻¹ᵁ j.1) Γ(F, i ⁻¹ᵁ j.1) :=
    finite_sections_of_isFinitePresentation F (j.2.preimage i)
  have (j : ι) : IsNoetherianRing Γ(Y, j.1) :=
    IsLocallyNoetherian.component_noetherian ⟨j.1, j.2⟩
  have (j : ι) : Module.Finite Γ(Y, j.1)
      Γ(((pushforward i).obj F).restrict j.2.fromSpec, ⊤) := by
    have := finite_sections_pushforward_of_surjective i F j.1 (i.app_surjective j.1 j.2)
    exact Module.Finite.equiv (sectionsTopRestrictFromSpecEquiv _ j.2).symm
  choose P hP using fun j : ι ↦
    exists_presentation_isFinite (((pushforward i).obj F).restrict j.2.fromSpec)
  refine isFinitePresentation_of_iSup_opensRange_eq_top _ (fun j : ι ↦ j.2.fromSpec) ?_ P
  refine eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  obtain ⟨V, hV, hyV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (U := ⊤) (Set.mem_univ y)
  exact ⟨⟨V, hV⟩, by rwa [IsAffineOpen.opensRange_fromSpec]⟩



private theorem exists_epi_sigma_twist_affine
    {T : Scheme.{u}} [IsAffine T] [IsLocallyNoetherian T]
    (n : Type u) [Finite n] (F : (ℙ(n; T)).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; T)).ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := (ℙ(n; T)).ringCatSheaf) F] :
    ∃ (ι : Type u) (_ : Finite ι) (e : ι → ℕ)
      (φ : (∐ fun a ↦ ProjectiveSpace.twist n T (-(e a : ℤ))) ⟶ F), Epi φ ∧
        SheafOfModules.IsQuasicoherent (R := (ℙ(n; T)).ringCatSheaf) (kernel φ) ∧
        SheafOfModules.IsFinitePresentation (R := (ℙ(n; T)).ringCatSheaf)
          (kernel φ) := by
  classical
  -- every section over `D₊(Tᵢ)` is hit by a map from a twist `𝒪(-m)`, by clearing denominators
  have key (i : n) : ∀ (V : (ℙ(n; T)).Opens)
      (_ : (Hom.zeroLocus (ProjectiveSpace.coordinateSection n T i)).support.compl
        = V) (t : Γ(F, V)), ∃ (m : ℕ) (φ : ProjectiveSpace.twist n T (-(m : ℤ)) ⟶ F)
        (w : Γ(ProjectiveSpace.twist n T (-(m : ℤ)), V)), φ.app V w = t := by
    rintro V rfl t
    have : CompactSpace ℙ(n; T) :=
      QuasiCompact.compactSpace_of_compactSpace (ℙ(n; T) ↘ T)
    obtain ⟨m, u, hu⟩ := exists_tensorPowSection_eq_restrict (ℙ(n; T) ↘ T)
      _ (ProjectiveSpace.coordinateSection n T i) F t
    obtain ⟨e₁⟩ := ProjectiveSpace.nonempty_tensorPow_twist_one_iso n T m
    obtain ⟨e₂⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso n T m (-m)
    let c : MonoidalCategory.tensorObj ((ProjectiveSpace.twist n T 1).tensorPow m)
        (ProjectiveSpace.twist n T (-(m : ℤ))) ≅ MonoidalCategory.tensorUnit _ :=
      (MonoidalCategory.tensorIso e₁ (Iso.refl _)) ≪≫ e₂ ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫
        (ProjectiveSpace.unitIsoTwistZero n _).symm
    exact ⟨m, exists_hom_app_eq_of_tensorPowSection _ (isFreeGenerator_app_one_of_le _ le_rfl)
      m c t u hu⟩
  -- finitely many generators of `Γ(D₊(Tᵢ), ℱ)` for each `i`
  have := Fintype.ofFinite n
  have hfin (i : n) : Module.Finite Γ(ℙ(n; T), ProjectiveSpace.standardOpen n _ i)
      Γ(F, ProjectiveSpace.standardOpen n _ i) :=
    finite_sections_of_isFinitePresentation F (ProjectiveSpace.isAffineOpen_standardOpen _ _ i)
  choose r t ht using fun i ↦ (hfin i).exists_fin
  choose m φ w hw using fun (a : Σ i : n, ULift.{u} (Fin (r i))) ↦ key a.1 _
    (ProjectiveSpace.compl_support_zeroLocus_coordinateSection n _ a.1) (t a.1 a.2.down)
  refine ⟨Σ i : n, ULift.{u} (Fin (r i)), inferInstance, m, Sigma.desc φ, ?_, ?_, ?_⟩
  · -- the sum of these maps is surjective on every `D₊(Tᵢ)`
    refine epi_of_surjective_app _ (ProjectiveSpace.standardOpen n T)
      (fun i ↦ ProjectiveSpace.isAffineOpen_standardOpen _ _ i)
      (ProjectiveSpace.iSup_standardOpen n _) fun i y ↦ ?_
    have hy : y ∈ Submodule.span Γ(ℙ(n; T), ProjectiveSpace.standardOpen n _ i)
        (Set.range (t i)) := by
      rw [ht i]
      trivial
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
    refine ⟨∑ a, c a • (Sigma.ι (fun b ↦ ProjectiveSpace.twist n T (-(m b : ℤ)))
      ⟨i, ⟨a⟩⟩).app _ (w ⟨i, ⟨a⟩⟩), ?_⟩
    simp only [map_sum, Hom.app_smul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Sigma.ι_comp_desc, hw]
  · have := isQuasicoherent_sigma
      (fun a ↦ ProjectiveSpace.twist n T (-(m a : ℤ)))
    exact isQuasicoherent_kernel _
  · have : IsLocallyNoetherian ℙ(n; T) :=
      LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; T) ↘ T)
    have := isFinitePresentation_sigma
      (fun a ↦ ProjectiveSpace.twist n T (-(m a : ℤ)))
    exact isFinitePresentation_kernel _


private theorem finite_H_sigma {X T : Scheme.{u}} (g : X ⟶ T)
    {ι : Type u} [Finite ι] (G : ι → X.Modules) (q : ℕ)
    (hG : ∀ i, letI : Module Γ(T, ⊤) ((G i).H q) := Module.compHom _ g.appTop.hom
      Module.Finite Γ(T, ⊤) ((G i).H q)) :
    letI : Module Γ(T, ⊤) ((∐ G).H q) := Module.compHom _ g.appTop.hom
    Module.Finite Γ(T, ⊤) ((∐ G).H q) := by
  classical
  let (M : X.Modules) : Module Γ(T, ⊤) (M.H q) := Module.compHom _ g.appTop.hom
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  suffices h : ∀ G' : Fin k → X.Modules,
      (∀ i, Module.Finite Γ(T, ⊤) ((G' i).H q)) →
      Module.Finite Γ(T, ⊤) ((∐ G').H q) by
    have := h (G ∘ e.symm) (fun i ↦ hG (e.symm i))
    let E : ((∐ (G ∘ e.symm)).H q) ≃ₗ[Γ(T, ⊤)] ((∐ G).H q) :=
      { H.mapLinearEquiv (Sigma.reindex e.symm G) q with
        map_smul' := fun c x ↦ (H.mapLinearEquiv (Sigma.reindex e.symm G) q).map_smul
          (g.appTop c) x }
    exact Module.Finite.equiv E
  intro G hG
  let (i : Fin k) : Module.Finite Γ(T, ⊤) ((G i).H q) := hG i
  have : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteCoproducts
  let E : (⨁ G).H q ≃ₗ[Γ(T, ⊤)] ((i : Fin k) → (G i).H q) :=
    { toFun := fun x i ↦ H.map (biproduct.π G i) q x
      invFun := fun y ↦ ∑ i, H.map (biproduct.ι G i) q (y i)
      map_add' := fun x y ↦ funext fun i ↦ map_add _ x y
      map_smul' := fun c x ↦ funext fun i ↦ H.map_smul _ q (g.appTop c) x
      left_inv := fun x ↦ by
        simp only [← H.map_comp_apply]
        rw [← H.map_sum_apply, biproduct.total, H.map_id_apply]
      right_inv := fun y ↦ funext fun j ↦ by
        simp only [map_sum, ← H.map_comp_apply, biproduct.ι_π]
        rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [dite_eq_right hij, H.map_zero_apply])
          (by simp), dite_eq_left rfl, eqToHom_refl, H.map_id_apply] }
  have : Module.Finite Γ(T, ⊤) ((⨁ G).H q) := Module.Finite.equiv E.symm
  let E' : (⨁ G).H q ≃ₗ[Γ(T, ⊤)] (∐ G).H q :=
    { H.mapLinearEquiv (biproduct.isoCoproduct G) q with
      map_smul' := fun c x ↦ (H.mapLinearEquiv (biproduct.isoCoproduct G) q).map_smul
        (g.appTop c) x }
  exact Module.Finite.equiv E'

/-- The closed pushforward of a coherent module has an epimorphism from a module with
finite cohomology over the affine base, with coherent kernel.

Source: Stacks Project, Tag 01YS, proof of Lemma 30.14.1 (1) and (3),
Tag 01Y6, Lemma 30.9.9, and Tag 01XT, Lemma 30.8.1.
(blueprint: lem-pc-u3-projective-finite-cohomology-presentation)

Proof: put A = Gamma(T,O). The canonical affine isomorphism T -> Spec A
induces an isomorphism of projective spaces compatible with their projections.
The projective space is locally Noetherian, as its projection is locally of
finite type over the Noetherian affine base. Closed pushforward j_*F is
quasi-coherent and finitely presented: on an affine chart a finite module over
a quotient ring is finite over the Noetherian chart ring and hence finitely
presented. Put G = j_*F and transport G to projective space over A.
Choose finitely many generators on each standard affine chart. Clearing denominators
extends each generator, after
multiplication by a power of its coordinate section, to a homomorphism from a
negative twist. The sum E of these finitely many twists maps epimorphically to G,
since its images generate on each chart. The kernel is quasi-coherent, and is
finitely presented because the standard charts are Noetherian. For each twist,
the standard-cover monomial calculation identifies degree-q cohomology with a
finite free A-module (or zero); when there is one coordinate, each twist is
free of rank one on Spec A and has no positive cohomology. Finite sums commute with
cohomology, so H^q(E)
is finite. Transport the epimorphism and its kernel back along the projective
isomorphism; the induced cohomology comparison is A-linear by naturality for
multiplication by base sections. Thus the restricted action is exactly the one
along the displayed projection. For an empty coordinate type the projective
space is empty: G, E, and the kernel are zero, and all cohomology is zero.
This argument does not use finiteness of any cohomology of G or of the kernel. -/
theorem exists_projective_finite_cohomology_presentation
    {Y T : Scheme.{u}} [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (N : Type u) [Finite N] (j : Y ⟶ ℙ(N; T)) [IsClosedImmersion j]
    (F : Y.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (q : ℕ) :
    ∃ (E : (ℙ(N; T)).Modules) (φ : E ⟶ (pushforward j).obj F) (_ : Epi φ),
      (kernel φ).IsQuasicoherent ∧ (kernel φ).IsFinitePresentation ∧
      (letI : Module Γ(T, ⊤) (E.H q) :=
        Module.compHom _ (ℙ(N; T) ↘ T).appTop.hom
       Module.Finite Γ(T, ⊤) (E.H q)) := by
  have : IsLocallyNoetherian T := isLocallyNoetherian_of_isOpenImmersion T.isoSpec.hom
  have : IsLocallyNoetherian ℙ(N; T) :=
    LocallyOfFiniteType.isLocallyNoetherian (ℙ(N; T) ↘ T)
  obtain ⟨hqc, hfp⟩ := closed_pushforward_coherent_independent j F
  have := hqc
  have := hfp
  obtain ⟨ι, hι, m, φ, hφ, hKqc, hKfp⟩ :=
    exists_epi_sigma_twist_affine N ((pushforward j).obj F)
  let : Finite ι := hι
  refine ⟨_, φ, hφ, hKqc, hKfp, ?_⟩
  exact finite_H_sigma (ℙ(N; T) ↘ T)
    (fun i ↦ ProjectiveSpace.twist N T (-(m i : ℤ))) q
    (fun i ↦ ProjectiveSpace.finite_H_twist_affine N (-(m i : ℤ)) q)

end AlgebraicGeometry.Scheme.Modules
