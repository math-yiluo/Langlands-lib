/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.AlgebraicGeometry.SiteFiniteLocallyConstantWeakSerre
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # The one-step cohomological reduction on a covering slice

Source: Stacks Project, Cohomology on Sites, Tag 094G.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem single_map_of_cycles
    {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
    (F : A ⥤ A') [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (R : CochainComplex A ℤ) (b : ℤ) (P : A') (ψ : P ⟶ F.obj (R.cycles b))
    (hψ : Epi (ψ ≫ F.map (R.homologyπ b))) :
    ∃ g : (CochainComplex.singleFunctor A' b).obj P ⟶
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R,
      Epi (HomologicalComplex.homologyMap g b) := by
  let S := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R
  let ec : S.cycles b ≅ F.obj (R.cycles b) := (R.sc b).mapCyclesIso F
  let eh : S.homology b ≅ F.obj (R.homology b) := (R.sc b).mapHomologyIso F
  let χ := ψ ≫ ec.inv
  let g : (HomologicalComplex.single A' (ComplexShape.up ℤ) b).obj P ⟶ S :=
    HomologicalComplex.mkHomFromSingle (χ ≫ S.iCycles b)
      (fun k _ ↦ by simp only [Category.assoc, S.iCycles_d, comp_zero])
  have hc : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) b P).inv ≫
      HomologicalComplex.cyclesMap g b = χ := by
    apply (cancel_mono (S.iCycles b)).1
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i, g,
      HomologicalComplex.mkHomFromSingle_f,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc]
    simp
  have he : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) b P).inv ≫
      HomologicalComplex.homologyMap g b ≫ eh.hom = ψ ≫ F.map (R.homologyπ b) := by
    rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ,
      Category.assoc, HomologicalComplex.homologyπ_naturality_assoc,
      ← Category.assoc, hc]
    change χ ≫ (R.sc b |>.map F).homologyπ ≫ eh.hom = _
    rw [ShortComplex.homologyπ_mapHomologyIso_hom]
    simp only [χ, ec, Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  have : Epi ((HomologicalComplex.singleObjHomologySelfIso
      (ComplexShape.up ℤ) b P).inv ≫ HomologicalComplex.homologyMap g b ≫ eh.hom) := by
    rw [he]
    exact hψ
  refine ⟨g, ?_⟩
  exact (epi_comp_iff_of_isIso _ eh.hom).mp
    ((epi_comp_iff_of_epi _ _).mp this)

private theorem epi_homology_Q_map
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {R S : CochainComplex A ℤ} (g : R ⟶ S) (b : ℤ)
    (hg : Epi (HomologicalComplex.homologyMap g b)) :
    Epi ((DerivedCategory.homologyFunctor A b).map (DerivedCategory.Q.map g)) := by
  have : Epi ((DerivedCategory.homologyFunctor A b).map (DerivedCategory.Q.map g) ≫
      (DerivedCategory.homologyFunctorFactors A b).hom.app S) := by
    rw [DerivedCategory.homologyFunctorFactors_hom_naturality]
    exact inferInstance
  exact (epi_comp_iff_of_isIso _ _).mp this

section Helpers

variable {C : Type u} [SmallCategory C] (J : Precoverage C)
  (B : Type u) [CommRing B]

private theorem map_colimits {U V : C} (f : V ⟶ U) :
    PreservesFiniteColimits (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) f) :=
  ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
    (self := Adjunction.leftAdjoint_preservesColimits
      (Functor.sheafAdjunctionCocontinuous (Over.map f) (ModuleCat.{u} B)
        (J.toGrothendieck.over V) (J.toGrothendieck.over U)))⟩

private theorem map_additive {U V : C} (f : V ⟶ U) :
    (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) f).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] map_colimits map_additive

private noncomputable def mapConstants {U V : C} (f : V ⟶ U) :
    constantSheaf (J.toGrothendieck.over U) (ModuleCat.{u} B) ⋙
        J.toGrothendieck.overMapPullback (ModuleCat.{u} B) f ≅
      constantSheaf (J.toGrothendieck.over V) (ModuleCat.{u} B) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const (Over U)ᵒᵖ)
      ((Over.map f).pushforwardContinuousSheafificationCompatibility
        (ModuleCat.{u} B) (J.toGrothendieck.over V) (J.toGrothendieck.over U)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.constCompWhiskeringLeftIso _ (Over.map f).op)
      (presheafToSheaf (J.toGrothendieck.over V) (ModuleCat.{u} B))

private abbrev locallyFinite (U : C) :
    ObjectProperty (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)) :=
  fun F ↦ ∀ (V : C) (g : V ⟶ U),
    ∃ (I : Type u) (W : I → C) (f : ∀ i : I, W i ⟶ V),
      Presieve.ofArrows W f ∈ J V ∧
      ∀ i : I, ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
        ((J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i ≫ g)).obj F ≅
          (constantSheaf (J.toGrothendieck.over (W i)) (ModuleCat.{u} B)).obj M)

private instance locallyFinite_iso (U : C) :
    (locallyFinite J B U).IsClosedUnderIsomorphisms where
  of_iso e h V g := by
    obtain ⟨I, W, f, hcover, hM⟩ := h V g
    refine ⟨I, W, f, hcover, fun i ↦ ?_⟩
    obtain ⟨M, hM, ⟨eM⟩⟩ := hM i
    exact ⟨M, hM, ⟨(J.toGrothendieck.overMapPullback _ (f i ≫ g)).mapIso e.symm ≪≫ eM⟩⟩

private theorem locallyFinite_restrict {U V : C} (f : V ⟶ U)
    {F : Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)}
    (hF : locallyFinite J B U F) : locallyFinite J B V
      ((J.toGrothendieck.overMapPullback (ModuleCat.{u} B) f).obj F) := by
  intro W g
  obtain ⟨I, Z, h, hcover, hM⟩ := hF W (g ≫ f)
  refine ⟨I, Z, h, hcover, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := hM i
  refine ⟨M, hM, ⟨?_⟩⟩
  exact (J.toGrothendieck.overMapPullbackComp (ModuleCat.{u} B) (h i ≫ g) f).app F ≪≫
    (by simpa only [Category.assoc] using eM)

private theorem locallyFinite_constant [J.HasIsos] (U : C)
    (M : ModuleCat.{u} B) (hM : Module.Finite B M) :
    locallyFinite J B U
      ((constantSheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)).obj M) := by
  intro V g
  refine ⟨PUnit, fun _ ↦ V, fun _ ↦ 𝟙 V, ?_, fun _ ↦ ?_⟩
  · simpa only [Presieve.ofArrows_pUnit] using
      (Precoverage.mem_coverings_of_isIso (J := J) (𝟙 V))
  · exact ⟨M, hM, ⟨(mapConstants J B (𝟙 V ≫ g)).app M⟩⟩

private theorem locallyFinite_zero [J.HasIsos] (U : C)
    (F : Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)) (hF : IsZero F) :
    locallyFinite J B U F := by
  let M := ModuleCat.of B PUnit
  have hM : Module.Finite B M := inferInstance
  have hzero : IsZero ((constantSheaf (J.toGrothendieck.over U)
      (ModuleCat.{u} B)).obj M) :=
    (constantSheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)).map_isZero
      (ModuleCat.isZero_of_subsingleton M)
  exact (locallyFinite J B U).prop_of_iso
    (hzero.isoZero ≪≫ hF.isoZero.symm) (locallyFinite_constant J B U M hM)

private theorem locallyFinite_single [J.HasIsos] (U : C)
    [HasDerivedCategory.{w} (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))]
    (M : ModuleCat.{u} B) (hM : Module.Finite B M) (b : ℤ) :
    DerivedCategory.homologyProperty (locallyFinite J B U)
      ((DerivedCategory.singleFunctor _ b).obj
        ((constantSheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)).obj M)) := by
  intro q
  by_cases hq : q = b
  · subst q
    exact (locallyFinite J B U).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ b).app _).symm
      (locallyFinite_constant J B U M hM)
  · apply locallyFinite_zero J B
    rcases lt_or_gt_of_ne hq with hq | hq
    · exact DerivedCategory.isZero_of_isGE _ b q hq
    · exact DerivedCategory.isZero_of_isLE _ b q hq

/-- The local generator lift, written on flat slices to avoid iterated-slice transports. -/
private theorem local_free_lift [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (U : C) (r : ℕ)
    (F G : Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)) (p : F ⟶ G) [Epi p]
    (φ : (constantSheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)).obj
      (ModuleCat.of B (Fin r → B)) ⟶ G) :
    ∃ (I : Type u) (V : I → C) (f : ∀ i, V i ⟶ U),
      Presieve.ofArrows V f ∈ J U ∧
      ∀ i, ∃ ψ : (constantSheaf (J.toGrothendieck.over (V i)) (ModuleCat.{u} B)).obj
          (ModuleCat.of B (Fin r → B)) ⟶
            (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i)).obj F,
        ψ ≫ (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i)).map p =
          ((mapConstants J B (f i)).app (ModuleCat.of B (Fin r → B))).inv ≫
            (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i)).map φ := by
  classical
  let M := ModuleCat.of B (Fin r → B)
  let γ := toSheafify (J.toGrothendieck.over U) ((Functor.const (Over U)ᵒᵖ).obj M) ≫ φ.hom
  let s (i : Fin r) := γ.app (Opposite.op (Over.mk (𝟙 U))) (Pi.basisFun B (Fin r) i)
  have hp : Sheaf.IsLocallySurjective p :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u} B) p).2 inferInstance
  have : Presheaf.IsLocallySurjective (J.toGrothendieck.over U) p.hom := hp
  let S (i : Fin r) := Presheaf.imageSieve p.hom (s i)
  have hS : (⨅ i, S i) ∈ (J.toGrothendieck.over U) (Over.mk (𝟙 U)) :=
    (J.toGrothendieck.over U).iInf_mem S
      (fun i ↦ Presheaf.imageSieve_mem _ p.hom (s i))
  obtain ⟨R, hR, hle⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp
      (show Sieve.overEquiv (Over.mk (𝟙 U)) (⨅ i, S i) ∈ J.toGrothendieck U from hS)
  obtain ⟨E, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR
  refine ⟨E.I₀, E.X, E.f, E.mem₀, fun i ↦ ?_⟩
  have hf := (Sieve.overEquiv_iff _ _).mp (hle _ _ (Presieve.ofArrows.mk i))
  let X := (Over.map (E.f i)).obj (Over.mk (𝟙 (E.X i)))
  let k : X ⟶ Over.mk (𝟙 U) := Over.homMk (𝟙 (E.X i) ≫ E.f i) (by simp [X])
  have hf' : (⨅ j, S j).arrows k := by
    let Y := Over.mk (E.f i ≫ (Over.mk (𝟙 U)).hom)
    let t : X ⟶ Y := Over.homMk (𝟙 (E.X i)) (by simp [X, Y])
    have h := (⨅ j, S j).downward_closed hf t
    have hk : t ≫ (Over.homMk (E.f i) : Y ⟶ Over.mk (𝟙 U)) = k := by
      apply Over.OverMorphism.ext
      rfl
    rw [hk] at h
    exact h
  have hz (j : Fin r) : ∃ z : F.obj.obj (Opposite.op X),
      p.hom.app (Opposite.op X) z = G.obj.map k.op (s j) :=
    (iInf_le S j) _ hf'
  choose z hz using hz
  let l : (Fin r → B) →ₗ[B] F.obj.obj (Opposite.op X) :=
    (Pi.basisFun B (Fin r)).constr B z
  let adj := constantSheafAdj (J.toGrothendieck.over (E.X i))
    (ModuleCat.{u} B) Over.mkIdTerminal
  let ψ := (adj.homEquiv M
    ((J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (E.f i)).obj F)).symm
      (ModuleCat.ofHom l)
  refine ⟨ψ, ?_⟩
  apply (adj.homEquiv M _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [ψ, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right, constantSheafAdj_homEquiv_apply]
  change _ = (toSheafify (J.toGrothendieck.over (E.X i))
    ((Functor.const (Over (E.X i))ᵒᵖ).obj M)).app (Opposite.op (Over.mk (𝟙 (E.X i)))) ≫
      (((mapConstants J B (E.f i)).app M).inv).hom.app _ ≫ φ.hom.app _
  rw [← Category.assoc]
  change ModuleCat.ofHom l ≫ p.hom.app _ = _
  have hu : (toSheafify (J.toGrothendieck.over (E.X i))
      ((Functor.const (Over (E.X i))ᵒᵖ).obj M)).app (Opposite.op (Over.mk (𝟙 (E.X i)))) ≫
        (((mapConstants J B (E.f i)).app M).inv).hom.app _ =
      (toSheafify (J.toGrothendieck.over U)
        ((Functor.const (Over U)ᵒᵖ).obj M)).app
          (Opposite.op (Over.mk (𝟙 (E.X i) ≫ E.f i))) := by
    simp [mapConstants, ← NatTrans.comp_app, toSheafify_sheafifyLift]
    rfl
  rw [hu]
  apply ModuleCat.hom_ext
  apply (Pi.basisFun B (Fin r)).ext
  intro j
  change p.hom.app _ (l (Pi.basisFun B (Fin r) j)) =
    γ.app _ (Pi.basisFun B (Fin r) j)
  rw [Module.Basis.constr_basis]
  apply (hz j).trans
  have hn := γ.naturality k.op
  change (𝟙 M) ≫ γ.app _ = γ.app _ ≫ G.obj.map _ at hn
  rw [Category.id_comp] at hn
  exact (congrArg (fun q ↦ q (Pi.basisFun B (Fin r) j)) hn).symm

private theorem local_top_epi [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [∀ U : C, HasDerivedCategory.{w}
      (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))]
    (U : C) (K : DerivedCategory (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)))
    (b : ℤ) (hK : locallyFinite J B U ((DerivedCategory.homologyFunctor _ b).obj K)) :
    ∃ (I : Type u) (V : I → C) (f : ∀ i, V i ⟶ U),
      Presieve.ofArrows V f ∈ J U ∧
      ∀ i, ∃ (r : ℕ)
        (α : (DerivedCategory.singleFunctor _ b).obj
          ((constantSheaf (J.toGrothendieck.over (V i)) (ModuleCat.{u} B)).obj
            (ModuleCat.of B (Fin r → B))) ⟶
              (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i)).mapDerivedCategory.obj K),
        Epi ((DerivedCategory.homologyFunctor _ b).map α) := by
  classical
  obtain ⟨I, V, f, hcover, hM⟩ := hK U (𝟙 U)
  have hlocal (i : I) :
      ∃ (T : Type u) (W : T → C) (g : ∀ t, W t ⟶ V i),
        Presieve.ofArrows W g ∈ J (V i) ∧
        ∀ t, ∃ (r : ℕ)
          (α : (DerivedCategory.singleFunctor _ b).obj
            ((constantSheaf (J.toGrothendieck.over (W t)) (ModuleCat.{u} B)).obj
              (ModuleCat.of B (Fin r → B))) ⟶
                (J.toGrothendieck.overMapPullback (ModuleCat.{u} B)
                  (g t ≫ f i)).mapDerivedCategory.obj K),
          Epi ((DerivedCategory.homologyFunctor _ b).map α) := by
    obtain ⟨M, hM, ⟨eM⟩⟩ := hM i
    let F := J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i)
    let K' := F.mapDerivedCategory.obj K
    let e : (DerivedCategory.homologyFunctor _ b).obj K' ≅
        (constantSheaf (J.toGrothendieck.over (V i)) (ModuleCat.{u} B)).obj M :=
      (F.mapDerivedCategoryHomologyFunctorIso b).symm.app K ≪≫
        (by simpa only [Functor.comp_obj, F, Category.comp_id] using eM)
    let R := DerivedCategory.Q.objPreimage K'
    let eR : DerivedCategory.Q.obj R ≅ K' := DerivedCategory.Q.objObjPreimageIso K'
    let := hM
    obtain ⟨r, p, hp⟩ := Module.Finite.exists_fin' B M
    let p' : ModuleCat.of B (Fin r → B) ⟶ M := ModuleCat.ofHom p
    have : Epi p' := (ModuleCat.epi_iff_surjective _).2 hp
    let φ := (constantSheaf (J.toGrothendieck.over (V i)) (ModuleCat.{u} B)).map p' ≫
      e.inv ≫ (DerivedCategory.homologyFunctor _ b).map eR.inv ≫
        (DerivedCategory.homologyFunctorFactors _ b).hom.app R
    have : Epi φ := inferInstance
    obtain ⟨T, W, g, hcoverW, hψ⟩ :=
      local_free_lift J B (V i) r (R.cycles b) (R.homology b) (R.homologyπ b) φ
    refine ⟨T, W, g, hcoverW, fun t ↦ ?_⟩
    obtain ⟨ψ, hψ⟩ := hψ t
    let G := J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (g t)
    have hφG : Epi (G.map φ) := G.map_epi φ
    have hψepi : Epi (ψ ≫ G.map (R.homologyπ b)) := by
      rw [hψ]
      exact epi_comp _ _
    obtain ⟨γ, hγ⟩ := single_map_of_cycles G R b _ ψ hψepi
    have := epi_homology_Q_map γ b hγ
    let α := DerivedCategory.Q.map γ ≫ G.mapDerivedCategoryFactors.inv.app R ≫
      G.mapDerivedCategory.map eR.hom
    have : Epi ((DerivedCategory.homologyFunctor _ b).map α) := by
      dsimp only [α]
      rw [Functor.map_comp, Functor.map_comp]
      infer_instance
    let ecomp := (Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso
        (J.toGrothendieck.overMapPullbackComp (ModuleCat.{u} B) (g t) (f i))).app K
    refine ⟨r, α ≫ ecomp.hom, ?_⟩
    rw [Functor.map_comp]
    infer_instance
  choose T W g hcoverW hstep using hlocal
  exact ⟨Σ i, T i, fun p ↦ W p.1 p.2, fun p ↦ g p.1 p.2 ≫ f p.1,
    Precoverage.comp_mem_coverings f hcover g hcoverW, fun p ↦ hstep p.1 p.2⟩

end Helpers

attribute [local instance] map_colimits map_additive

-- Preserve the original named forall binders, which are used by the proof but
-- do not occur in the theorem's conclusion.
set_option linter.unusedVariables false in
/-- Killing top cohomology locally leaves an object with one fewer possible
cohomological degree and finite locally constant cohomology. The triangle is
recorded after rotation; no extension tower is part of this assertion.

Source: Stacks Project, Tag 094G, proof of `lemma-locally-constant`, from the
choice of top-cohomology generators through the short exact sequence for the
cohomology of the cone.
(auxiliary; not a blueprint node)

Proof: Work on C/U. Trivialize the finite top cohomology on a covering, choose
finitely many module generators, and take the corresponding finite free module
F surjecting onto it. Choose any cochain representative of K. The map from
its cycles in degree b to its cohomology is epic. Intersect the image sieves of
the finitely many generators and extract a J-cover. The constant-sheaf
adjunction on each flat slice gives the required lift through this epimorphism.
Inclusion of the cycles gives a chain map from the constant
F in degree b. Complete its localization to a distinguished triangle and rotate.
The long exact homology sequence makes the cone vanish outside [a,b-1],
identifies its homology below b-1 with that of K, and gives in degree b-1 an
extension of H^(b-1)(K) by the kernel of F onto H^b(K). The finite locally
constant Serre theorem, using Noetherianity, shows this extension is finite
locally constant. Exact restriction, the constant-sheaf comparison and the
canonical equivalence of an iterated slice with C/V identify all these
properties with the displayed restrictions along maps in C. Compose the two
covering refinements. The construction also allows rank zero, a zero ring and
empty covers. -/
theorem exists_site_finite_constant_cone_step
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [∀ U : C, HasDerivedCategory.{w}
      (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))] :
    let ρ := fun {U V : C} (f : V ⟶ U) ↦
      @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
        (J.toGrothendieck.overMapPullback (ModuleCat.{u} B) f)
        (Functor.additive_of_preserves_binary_products _) _
        ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
          (self := Adjunction.leftAdjoint_preservesColimits
            (Functor.sheafAdjunctionCocontinuous (Over.map f) (ModuleCat.{u} B)
              (J.toGrothendieck.over V) (J.toGrothendieck.over U)))⟩
    ∀ (U : C) (K : DerivedCategory (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)))
      (a b : ℤ) (hab : a < b)
      (hvan : ∀ q : ℤ, q < a ∨ b < q → IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)) q).obj K))
      (hloc : ∀ (q : ℤ) (V : C) (g : V ⟶ U),
        ∃ (I : Type u) (W : I → C) (f : ∀ i : I, W i ⟶ V),
          Presieve.ofArrows W f ∈ J V ∧
          ∀ i : I, ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
            ((J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i ≫ g)).obj
              ((DerivedCategory.homologyFunctor
                (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)) q).obj K) ≅
              (constantSheaf (J.toGrothendieck.over (W i)) (ModuleCat.{u} B)).obj M)),
      ∃ (I : Type u) (V : I → C) (f : ∀ i : I, V i ⟶ U),
        Presieve.ofArrows V f ∈ J U ∧
        ∀ i : I, ∃ (M : ModuleCat.{u} B), Module.Finite B M ∧
          ∃ (L : DerivedCategory (Sheaf (J.toGrothendieck.over (V i)) (ModuleCat.{u} B))),
            (∀ q : ℤ, q < a ∨ b - 1 < q → IsZero
              ((DerivedCategory.homologyFunctor
                (Sheaf (J.toGrothendieck.over (V i)) (ModuleCat.{u} B)) q).obj L)) ∧
            (∀ (q : ℤ) (W : C) (g : W ⟶ V i),
              ∃ (T : Type u) (Z : T → C) (h : ∀ t : T, Z t ⟶ W),
                Presieve.ofArrows Z h ∈ J W ∧
                ∀ t : T, ∃ N : ModuleCat.{u} B, Module.Finite B N ∧ Nonempty
                  ((J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (h t ≫ g)).obj
                    ((DerivedCategory.homologyFunctor
                      (Sheaf (J.toGrothendieck.over (V i)) (ModuleCat.{u} B)) q).obj L) ≅
                    (constantSheaf (J.toGrothendieck.over (Z t)) (ModuleCat.{u} B)).obj N)) ∧
            ∃ (iK : (ρ (f i)).obj K ⟶ L)
              (δ : L ⟶ DerivedCategory.Q.obj
                ((CochainComplex.singleFunctor _ (b - 1)).obj
                  ((constantSheaf (J.toGrothendieck.over (V i)) (ModuleCat.{u} B)).obj M)))
              (j : DerivedCategory.Q.obj
                ((CochainComplex.singleFunctor _ (b - 1)).obj
                  ((constantSheaf (J.toGrothendieck.over (V i)) (ModuleCat.{u} B)).obj M)) ⟶
                    ((ρ (f i)).obj K)⟦(1 : ℤ)⟧),
              Triangle.mk iK δ j ∈ distTriang _ := by
  classical
  intro ρ U K a b hab hvan hloc
  obtain ⟨I, V, f, hcover, hα⟩ := local_top_epi J B U K b (hloc b)
  refine ⟨I, V, f, hcover, fun i ↦ ?_⟩
  obtain ⟨r, α, hα⟩ := hα i
  let M := ModuleCat.of B (Fin r → B)
  let F := J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i)
  let K' := F.mapDerivedCategory.obj K
  let A := (constantSheaf (J.toGrothendieck.over (V i)) (ModuleCat.{u} B)).obj M
  let S := (DerivedCategory.singleFunctor _ b).obj A
  obtain ⟨L, iK, δ, hT⟩ := distinguished_cocone_triangle α
  let T := Triangle.mk α iK δ
  have hK' : DerivedCategory.homologyProperty (locallyFinite J B (V i)) K' := by
    intro q
    exact (locallyFinite J B (V i)).prop_of_iso
      ((F.mapDerivedCategoryHomologyFunctorIso q).app K)
      (locallyFinite_restrict J B (f i) (hloc q))
  obtain ⟨hker, hcoker, hext⟩ := site_finiteLocallyConstant_weakSerre J B (V i)
  let : (locallyFinite J B (V i)).IsClosedUnderKernels := hker
  let : (locallyFinite J B (V i)).IsClosedUnderCokernels := hcoker
  let : (locallyFinite J B (V i)).IsClosedUnderExtensions := hext
  let e : S⟦(1 : ℤ)⟧ ≅ (DerivedCategory.singleFunctor _ (b - 1)).obj A :=
    ((DerivedCategory.singleFunctors _).shiftIso 1 (b - 1) b (by omega)).app A
  have hS : DerivedCategory.homologyProperty (locallyFinite J B (V i)) (S⟦(1 : ℤ)⟧) :=
    (DerivedCategory.homologyProperty (locallyFinite J B (V i))).prop_of_iso e.symm
      (locallyFinite_single J B (V i) M inferInstance (b - 1))
  have hL : DerivedCategory.homologyProperty (locallyFinite J B (V i)) L :=
    (DerivedCategory.homologyProperty (locallyFinite J B (V i))).ext_of_isTriangulatedClosed₂
      T.rotate (rot_of_distTriang T hT) hK' hS
  have hSz (q : ℤ) (hq : q ≠ b) : IsZero
      ((DerivedCategory.homologyFunctor _ q).obj S) := by
    rcases lt_or_gt_of_ne hq with hq | hq
    · exact DerivedCategory.isZero_of_isGE _ b q hq
    · exact DerivedCategory.isZero_of_isLE _ b q hq
  have hvanL (q : ℤ) (hq : q < a ∨ b - 1 < q) : IsZero
      ((DerivedCategory.homologyFunctor _ q).obj L) := by
    have hex := DerivedCategory.HomologySequence.exact₃ T hT q (q + 1) rfl
    by_cases hqb : q = b
    · subst q
      exact hex.isZero_of_both_zeros
        ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT b).mp hα)
        ((hSz (b + 1) (by omega)).eq_of_tgt _ _)
    · exact hex.isZero_of_both_isZero
        (F.isZero_homologyFunctor_mapDerivedCategory_obj (hvan q (by omega)))
        (hSz (q + 1) (by omega))
  refine ⟨M, inferInstance, L, hvanL, hL, iK, δ ≫ e.hom,
    e.inv ≫ T.rotate.mor₃, ?_⟩
  apply isomorphic_distinguished _ (rot_of_distTriang T hT)
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm ?_ ?_ ?_
  · simp [T]
  · simp [T]
  · simp [T]

end CategoryTheory
