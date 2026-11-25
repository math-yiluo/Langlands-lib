/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import Mathlib.AlgebraicGeometry.Cover.Sigma
import WeilConjectures.AlgebraicGeometry.EtaleCoproductRepresentation
/-!
# Assembly of the finite etale local representatives

Source: Stacks Project, Tag 03RV and Descent Tag 02W5.
(blueprint: lem-weil-pbc-finite-local-models-descent-datum-existence)
-/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme


private theorem finite_sigmaMap {ι : Type u} {X Y : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ Y i) [∀ i, IsFinite (f i)] : IsFinite (CategoryTheory.Limits.Sigma.map f) := by
  have hp (i : ι) :
      IsPullback (Limits.Sigma.ι X i) (f i)
        (CategoryTheory.Limits.Sigma.map f) (Limits.Sigma.ι Y i) := by
    apply (IsOpenImmersion.isPullback (f i) (Limits.Sigma.ι X i) (Limits.Sigma.ι Y i)
      (CategoryTheory.Limits.Sigma.map f) (by simp) ?_).flip
    apply TopologicalSpace.Opens.ext
    ext x
    obtain ⟨⟨j, x⟩, rfl⟩ := (sigmaMk X).surjective x
    simp only [sigmaMk_mk]
    change (CategoryTheory.Limits.Sigma.map f) (Limits.Sigma.ι X j x) ∈
      Set.range (Limits.Sigma.ι Y i) ↔
      Limits.Sigma.ι X j x ∈ Set.range (Limits.Sigma.ι X i)
    rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_map, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨y, hy⟩
      obtain rfl := congrArg Sigma.fst ((sigmaι_eq_iff Y i j y (f j x)).mp hy)
      exact ⟨x, rfl⟩
    · rintro ⟨y, hy⟩
      obtain rfl := congrArg Sigma.fst ((sigmaι_eq_iff X i j y x).mp hy)
      exact ⟨f i x, rfl⟩
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) (sigmaOpenCover Y)
  intro i
  change IsFinite (Limits.pullback.snd (CategoryTheory.Limits.Sigma.map f) (Limits.Sigma.ι Y i))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite (hp i).isoPullback.hom,
    (hp i).isoPullback_hom_snd]
  infer_instance

/-- The coproduct of a cover admits a finite etale representative of the restricted sheaf.

Source: Stacks Project, Tag 03RV, assembly of the local representatives before descent;
Descent Tag 02W5, gluing the local representations.
(blueprint: lem-weil-pbc-finite-local-models-descent-datum-existence)

Proof: Choose Q_i and its representation isomorphism from hrep by choice. The equivalence
between the site localized at U_i and the small etale site of U_i transports each isomorphism
back to the localized site. Let U be the coproduct of the U_i, as in Cover.sigma, and let V
be the coproduct of the Q_i. The coproduct of their structure morphisms is a morphism V to U.
Each U_i is an open and closed component of U, and its inverse image in V is Q_i. Thus this
morphism is finite by target locality and etale by source locality. This gives Q in
U.FiniteEtale. To identify the presheaves, cover any etale W over U by the inverse images of
these disjoint components. The local representation isomorphisms identify the sections of
E on each piece with morphisms from that piece to Q_i. The sheaf axiom for E and the gluing
property of morphisms to a scheme glue both directions uniquely. Disjointness makes overlap
compatibility automatic; the empty intersections use the empty-cover sheaf axiom. Uniqueness
shows naturality and that the two maps are inverse. The site equivalence expresses the
result in the displayed localized-site form. If the original cover is empty, U and V are
empty; each etale W over U is empty, and the same empty-cover axiom proves the claim. No
uniform rank bound and no finite index set are used. -/
theorem finiteLocalModels_descentDatum_exists
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (𝒰 : Cover.{u} etalePrecoverage T)
    (hrep : ∀ i, ∃ Q : (𝒰.etalePrecoverageToEtale i).left.FiniteEtale,
      Nonempty (((Etale.overSheafEquiv (𝒰.etalePrecoverageToEtale i)
        (Type (u + 1))).functor.obj (E.over (𝒰.etalePrecoverageToEtale i))).obj ≅
          uliftYoneda.{u + 1}.obj Q.obj)) :
    let U := 𝒰.sigma.etalePrecoverageToEtale default
    ∃ (Q : U.left.FiniteEtale),
      Nonempty ((E.over U).obj ≅ (Etale.overToEtale U).op ⋙
        uliftYoneda.{u + 1}.obj Q.obj) := by
  classical
  let Ui := fun i ↦ 𝒰.etalePrecoverageToEtale i
  let Qi := fun i ↦ (hrep i).choose
  have hQi (i) : IsFinite (Qi i).obj.hom := (Qi i).property
  let : ∀ i, IsFinite (Qi i).obj.hom := hQi
  let π := CategoryTheory.Limits.Sigma.map fun i ↦ (Qi i).obj.hom
  have hπ : Etale π := by
    change Etale (Limits.Sigma.desc fun i ↦ (Qi i).obj.hom ≫ Limits.Sigma.ι 𝒰.X i)
    exact IsZariskiLocalAtSource.sigmaDesc fun i ↦ inferInstance
  let : Etale π := hπ
  have hf : IsFinite π := finite_sigmaMap fun i ↦ (Qi i).obj.hom
  let U := 𝒰.sigma.etalePrecoverageToEtale default
  let Q : U.left.FiniteEtale := ⟨Etale.mk π, hf⟩
  let : Etale (Limits.Sigma.desc fun i ↦ (Ui i).hom) :=
    IsZariskiLocalAtSource.sigmaDesc fun i ↦ (Ui i).prop
  obtain ⟨e⟩ := etaleCoproduct_representation T E Ui (fun i ↦ (Qi i).obj)
    (fun i ↦ (hrep i).choose_spec)
  change ((Etale.overSheafEquiv U (Type (u + 1))).functor.obj
    (E.over U)).obj ≅ uliftYoneda.{u + 1}.obj Q.obj at e
  refine ⟨Q, ⟨?_⟩⟩
  let F := Etale.overToEtale U
  let G := Etale.etaleToOver U
  let H := (E.over U).obj
  let n : H ≅ F.op ⋙ G.op ⋙ H :=
    (Functor.leftUnitor H).symm ≪≫
      Functor.isoWhiskerRight (NatIso.op (Etale.overEquiv U).unitIso).symm H ≪≫
        Functor.associator F.op G.op H
  exact n ≪≫ Functor.isoWhiskerLeft F.op e
end AlgebraicGeometry.Scheme
