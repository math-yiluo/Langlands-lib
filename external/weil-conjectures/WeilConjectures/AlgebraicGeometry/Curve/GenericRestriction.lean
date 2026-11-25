/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.GenericComparison
public import WeilConjectures.AlgebraicGeometry.Sites.FieldTrace
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-!
# The generic restriction of a pushforward from the generic point

Let `X` be an integral quasi-separated scheme with generic point `η : Spec k(X) ⟶ X`. For every
abelian étale sheaf `N` on `Spec k(X)` the counit `η^* η_* N ⟶ N` is an isomorphism: the generic
restriction of `η_* N` is `N`.

For a quasi-compact quasi-separated étale `X`-scheme `W`, continuity of sections at the limit
`Spec k(X) = lim_U Spec Γ(X, U)` (`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`)
shows that the unit `η_* N ⟶ η_* η^* η_* N` is bijective on sections over `W`, hence, by the
triangle identity, that the counit is bijective on sections over the generic fibre
`W ×_X Spec k(X)`. These generic fibres cover every étale `k(X)`-scheme: a finite separable
extension of `k(X)` has a standard étale presentation, which is defined over a nonempty affine
open of `X`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_hom_fromSpecFunctionField_etale_obj`: the generic fibres of
  the affine étale `X`-schemes cover the étale `k(X)`-schemes.
- `AlgebraicGeometry.Scheme.isIso_counit_app_fromSpecFunctionField`: `η^* η_* N ≅ N`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace Polynomial

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsIntegral X]

/-- The germ `Γ(X, U) ⟶ k(X)` of a nonempty affine open. -/
noncomputable abbrev NonemptyAffineOpens.germ (U : X.NonemptyAffineOpens) :
    Γ(X, U.1) ⟶ X.functionField :=
  X.affineOpensRingCocone.ι.app (op U)

lemma NonemptyAffineOpens.germ_injective (U : X.NonemptyAffineOpens) :
    Function.Injective U.germ.hom :=
  germ_injective_of_isIntegral X _ U.genericPoint_mem

lemma NonemptyAffineOpens.germ_map {U V : X.NonemptyAffineOpens} (h : U ≤ V) (y : Γ(X, V.1)) :
    U.germ.hom (X.presheaf.map (homOfLE h).op y) = V.germ.hom y :=
  ConcreteCategory.congr_hom (X.affineOpensRingCocone.w (homOfLE h).op) y

/-- Finitely many elements of the function field are defined on a common nonempty affine
open. -/
lemma exists_nonemptyAffineOpens_germ_eq (s : Finset X.functionField) :
    ∃ U : X.NonemptyAffineOpens, ∀ x ∈ s, x ∈ Set.range U.germ.hom := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary _, by simp⟩
  | insert x s _ ih =>
    obtain ⟨U₁, hU₁⟩ := ih
    obtain ⟨⟨U₂⟩, y, hy⟩ := Concrete.isColimit_exists_rep _ X.isColimitAffineOpensRingCocone x
    obtain ⟨U, hU1, hU2⟩ := directed_of (· ≥ ·) U₁ U₂
    refine ⟨U, fun z hz ↦ ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨_, (NonemptyAffineOpens.germ_map hU2 y).trans hy⟩
    · obtain ⟨y', rfl⟩ := hU₁ z hz
      exact ⟨_, NonemptyAffineOpens.germ_map hU1 y'⟩

/-- Finitely many polynomials over the function field are defined over a common nonempty
affine open. -/
lemma exists_nonemptyAffineOpens_lifts (s : Finset X.functionField[X]) :
    ∃ U : X.NonemptyAffineOpens, ∀ p ∈ s, p ∈ lifts U.germ.hom := by
  classical
  obtain ⟨U, hU⟩ := exists_nonemptyAffineOpens_germ_eq (s.biUnion fun p ↦ p.coeffs)
  refine ⟨U, fun p hp ↦ (lifts_iff_coeff_lifts p).2 fun n ↦ ?_⟩
  by_cases hn : p.coeff n = 0
  · rw [hn]
    exact ⟨0, map_zero _⟩
  · exact hU _ (Finset.mem_biUnion.2 ⟨p, hp, coeff_mem_coeffs hn⟩)

/-- **Spreading out a finite separable extension of the function field.** For a finite separable
extension `L` of `k(X)` with primitive element `α`, the minimal polynomial of `α` and a Bézout
relation with its derivative are defined over some nonempty affine open `U`, where they form a
standard étale pair. -/
lemma exists_standardEtalePair (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] [Algebra.IsSeparable X.functionField L] :
    ∃ (U : X.NonemptyAffineOpens) (P : StandardEtalePair Γ(X, U.1)), P.g = 1 ∧
      P.f.map U.germ.hom =
        minpoly X.functionField (Field.powerBasisOfFiniteOfSeparable X.functionField L).gen := by
  classical
  set f := minpoly X.functionField (Field.powerBasisOfFiniteOfSeparable X.functionField L).gen
  obtain ⟨a, b, hab⟩ : IsCoprime f (derivative f) := Algebra.IsSeparable.isSeparable _ _
  obtain ⟨U, hU⟩ := exists_nonemptyAffineOpens_lifts {f, a, b}
  obtain ⟨fU, hf⟩ := hU f (by simp)
  obtain ⟨aU, ha⟩ := hU a (by simp)
  obtain ⟨bU, hb⟩ := hU b (by simp)
  rw [coe_mapRingHom] at hf ha hb
  have hinj := map_injective _ U.germ_injective
  have hmonic : fU.Monic := by
    apply U.germ_injective
    rw [← leadingCoeff_map_of_injective U.germ_injective, hf, map_one]
    exact minpoly.monic (Algebra.IsSeparable.isIntegral _ _)
  refine ⟨U, ⟨fU, hmonic, 1, bU, aU, 0, hinj ?_⟩, rfl, hf⟩
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, pow_zero, ha, hb,
    ← derivative_map, hf]
  rw [← hab]
  ring

open GaloisCech in
/-- **The generic fibres of étale schemes over `X` dominate the étale `k(X)`-schemes of finite
separable field extensions.** For a finite separable extension `L` of the function field there
is an affine étale `X`-scheme `W` with a nonempty generic fibre `W ×_X Spec k(X)` mapping to
`Spec L` over `k(X)`: spread out a standard étale presentation of `L`
(`AlgebraicGeometry.Scheme.exists_standardEtalePair`) over a nonempty affine open. -/
lemma exists_hom_etaleSpec (L : Type u) [Field L] [Algebra X.functionField L]
    [Algebra.Etale X.functionField L] :
    ∃ (W : X.Etale) (_ : IsAffine W.left)
      (_ : Nonempty (X.fromSpecFunctionField.Etale.obj W).left),
      Nonempty (X.fromSpecFunctionField.Etale.obj W ⟶ etaleSpec X.functionField L) := by
  have : Module.Finite X.functionField L :=
    Algebra.FormallyUnramified.finite_of_free X.functionField L
  have : Algebra.IsSeparable X.functionField L :=
    Algebra.FormallyUnramified.isSeparable X.functionField L
  set pb := Field.powerBasisOfFiniteOfSeparable X.functionField L
  obtain ⟨U, P, hg1, hP⟩ := exists_standardEtalePair (X := X) L
  set η := X.fromSpecFunctionField
  let j := X.affineOpensDiagramι.app U
  let a : Spec (.of P.Ring) ⟶ Spec Γ(X, U.1) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) P.Ring))
  have ha : AlgebraicGeometry.Etale a :=
    HasRingHomProperty.Spec_iff.mpr
      (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale Γ(X, U.1) P.Ring)))
  let W : X.Etale := MorphismProperty.Over.mk ⊤ (a ≫ j) inferInstance
  let Z := (η.Etale.obj W).left
  let p₁ : Z ⟶ Spec (.of P.Ring) := pullback.fst (a ≫ j) η
  let p₂ : Z ⟶ Spec X.functionField := pullback.snd (a ≫ j) η
  have hcomp : p₁ ≫ a = p₂ ≫ Spec.map U.germ := by
    rw [← cancel_mono j, Category.assoc, Category.assoc]
    exact pullback.condition.trans
      (congrArg (p₂ ≫ ·) (fromSpecFunctionField_eq_functionFieldCone_comp X U))
  have key : (toRing p₂).comp U.germ.hom = (toRing p₁).comp (algebraMap Γ(X, U.1) P.Ring) := by
    rw [← toRing_comp_specMap, ← hcomp, toRing_comp_specMap]
    rfl
  let : Algebra X.functionField Γ(Z, ⊤) := (toRing p₂).toAlgebra
  let θ : Γ(Z, ⊤) := toRing p₁ P.X
  have hθ : aeval θ (minpoly X.functionField pb.gen) = 0 := by
    rw [← hP, aeval_def, eval₂_map]
    change eval₂ ((toRing p₂).comp U.germ.hom) θ P.f = 0
    rw [key, ← hom_eval₂, ← aeval_def, P.hasMap_X.1, map_zero]
  let φ := pb.lift θ hθ
  let g : Z ⟶ Spec (.of L) := Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)
  have hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) = p₂ := by
    refine eq_of_toRing_eq ?_
    rw [Category.assoc, ← Spec.map_comp, toRing_comp_specMap]
    have : toRing Z.toSpecΓ = RingHom.id _ := by
      rw [toRing, toSpecΓ_appTop, Iso.inv_hom_id]
      rfl
    rw [this]
    ext x
    exact φ.commutes x
  -- the generic fibre is nonempty
  let : Algebra Γ(X, U.1) L := ((algebraMap X.functionField L).comp U.germ.hom).toAlgebra
  have hL : P.HasMap pb.gen := by
    refine ⟨?_, by simp [hg1]⟩
    rw [aeval_def, show algebraMap Γ(X, U.1) L =
      (algebraMap X.functionField L).comp U.germ.hom from rfl, ← eval₂_map, hP, ← aeval_def,
      minpoly.aeval]
  have : Nontrivial P.Ring := (P.lift pb.gen hL).toRingHom.domain_nontrivial
  obtain ⟨w⟩ : Nonempty (Spec (.of P.Ring)) := inferInstance
  have hopen : IsOpenMap (a ≫ j) := (a ≫ j).isOpenMap
  have hξ : genericPoint X ∈ Set.range (a ≫ j) :=
    ((genericPoint_spec X).mem_open_set_iff (hopen.isOpen_range)).2
      ⟨_, trivial, w, rfl⟩
  obtain ⟨w', hw'⟩ := hξ
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := a ≫ j) (g := η) w'
    (IsLocalRing.closedPoint X.functionField) (hw'.trans fromSpecStalk_closedPoint.symm)
  exact ⟨W, inferInstanceAs (IsAffine (Spec (.of P.Ring))), ⟨z⟩,
    ⟨MorphismProperty.Over.homMk g hg trivial⟩⟩

/-- The generic fibres of affine étale `X`-schemes cover every étale `k(X)`-scheme. -/
lemma exists_hom_fromSpecFunctionField_etale_obj (Y : (Spec X.functionField).Etale)
    (y : Y.left) : ∃ (W : X.Etale) (_ : IsAffine W.left)
      (g : X.fromSpecFunctionField.Etale.obj W ⟶ Y), y ∈ Set.range g.left := by
  obtain ⟨L, _, _, _, g₀, y₀, hy₀⟩ := exists_etaleSpec_field_left_apply_eq Y y
  obtain ⟨W, hW, ⟨z⟩, ⟨h⟩⟩ := exists_hom_etaleSpec (X := X) L
  refine ⟨W, hW, h ≫ g₀, z, ?_⟩
  rw [← hy₀]
  change g₀.left (h.left z) = _
  congr 1
  exact Subsingleton.elim (α := Spec (.of L)) _ _

open _root_.AlgebraicGeometry.Etale

/-- The unit of `j^* ⊣ j_*` at the pushforward `η_* N` of a sheaf on the generic point is an
isomorphism, for the open immersion `j` of a nonempty affine open: `η` factors through `j`, and
`j_*` is fully faithful. -/
instance isIso_affineOpenUnit_lowerStar (U : X.NonemptyAffineOpens)
    (N : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (X.affineOpenUnit U ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N)) := by
  let π : Spec X.functionField ⟶ X.affineOpensDiagram.obj U := X.functionFieldCone.π.app U
  exact (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    (X.affineOpensDiagramι.app U)).isIso_unit_app_of_iso
      ((lowerStarComp AddCommGrpCat.{u + 1} π (X.affineOpensDiagramι.app U)
        X.fromSpecFunctionField (fromSpecFunctionField_eq_functionFieldCone_comp X U)).app N).symm

variable [QuasiSeparatedSpace X]

/-- **Sections of `η_* η^* η_* N` over quasi-compact objects.** For a sheaf `N` on the generic
point `η : Spec k(X) ⟶ X` and a quasi-compact quasi-separated étale `X`-scheme `W`, the unit
`η_* N ⟶ η_* η^* η_* N` is bijective on sections over `W`: by continuity of sections at
`Spec k(X) = lim_U Spec Γ(X, U)`, the target is the colimit of the sections of the
`j_{U*} j_U^* η_* N`, and the units `η_* N ⟶ j_{U*} j_U^* η_* N` are isomorphisms. -/
theorem bijective_unit_app_lowerStar_app
    (N : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) (W : X.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    Function.Bijective (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      X.fromSpecFunctionField).unit.app
        ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N)).hom.app (op W)) := by
  set G := (X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N
  have hP := fromSpecFunctionField_eq_functionFieldCone_comp X
  have hc := X.isLimitFunctionFieldCone
  have hτ (U : X.NonemptyAffineOpens) := Etale.unit_app_comp_unitComparison
    (X.functionFieldCone.π.app U) (X.affineOpensDiagramι.app U) X.fromSpecFunctionField (hP U) G
  have hbij (U : X.NonemptyAffineOpens) :
      Function.Bijective ((X.affineOpenUnit U G).hom.app (op W)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 (inferInstanceAs (IsIso
      (((sheafToPresheaf _ _).map (X.affineOpenUnit U G)).app (op W))))
  refine ⟨(injective_iff_map_eq_zero _).2 fun r hr ↦ ?_, fun t ↦ ?_⟩
  · let U₀ : X.NonemptyAffineOpens := Classical.arbitrary _
    have h₀ : (Etale.unitComparison (X.functionFieldCone.π.app U₀) (X.affineOpensDiagramι.app U₀)
        X.fromSpecFunctionField (hP U₀) G).hom.app (op W)
          ((X.affineOpenUnit U₀ G).hom.app (op W) r) = 0 := by
      rw [← hτ U₀] at hr
      exact hr
    obtain ⟨U, f', hU⟩ := Etale.exists_unitComparison_app_eq_zero_of_isLimit X.affineOpensDiagram
      X.affineOpensDiagramι X.functionFieldCone X.fromSpecFunctionField hP hc G W U₀ _ h₀
    refine (hbij U).1 ?_
    rw [map_zero, ← X.affineOpenUnit_comp_transition f' G]
    exact hU
  · obtain ⟨U, s, hs⟩ := Etale.unitComparison_app_surjective_of_isLimit X.affineOpensDiagram
      X.affineOpensDiagramι X.functionFieldCone X.fromSpecFunctionField hP hc G W t
    obtain ⟨r, rfl⟩ := (hbij U).2 s
    refine ⟨r, ?_⟩
    rw [← hs, ← hτ U]
    rfl

/-- **The counit at a generic fibre.** For a quasi-compact quasi-separated étale `X`-scheme `W`,
the counit `η^* η_* N ⟶ N` is bijective on sections over `W ×_X Spec k(X)`: by the triangle
identity it is inverse to the unit of `AlgebraicGeometry.Scheme.bijective_unit_app_lowerStar_app`.
-/
theorem bijective_counit_app_app
    (N : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) (W : X.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    Function.Bijective (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      X.fromSpecFunctionField).counit.app N).hom.app
        (op (X.fromSpecFunctionField.Etale.obj W))) := by
  set adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} X.fromSpecFunctionField
  have hu := bijective_unit_app_lowerStar_app N W
  have h (x) : (adj.counit.app N).hom.app (op (X.fromSpecFunctionField.Etale.obj W))
      ((adj.unit.app ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N)).hom.app
        (op W) x) = x :=
    ConcreteCategory.congr_hom (congrArg (fun φ ↦ φ.hom.app (op W))
      (adj.right_triangle_components N)) x
  refine ⟨fun y y' hyy' ↦ ?_, fun x ↦ ⟨_, h x⟩⟩
  obtain ⟨x, rfl⟩ := hu.2 y
  obtain ⟨x', rfl⟩ := hu.2 y'
  rw [h, h] at hyy'
  rw [hyy']

/-- **The generic restriction of `η_* N` is `N`.** Let `X` be an integral quasi-separated scheme
with generic point `η : Spec k(X) ⟶ X`. For every abelian étale sheaf `N` on `Spec k(X)` the
counit `η^* η_* N ⟶ N` is an isomorphism: it is bijective on the sections over the generic fibres
of the affine étale `X`-schemes (`AlgebraicGeometry.Scheme.bijective_counit_app_app`), and these
cover every étale `k(X)`-scheme. -/
theorem isIso_counit_app_fromSpecFunctionField
    (N : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      X.fromSpecFunctionField).counit.app N) := by
  set ε := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    X.fromSpecFunctionField).counit.app N
  let F := (X.fromSpecFunctionField)^*[AddCommGrpCat.{u + 1}].obj
    ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N)
  choose W hW g hg using exists_hom_fromSpecFunctionField_etale_obj (X := X)
  have hcov (Y : (Spec X.functionField).Etale) : ⋃ y, Set.range (g Y y).left = Set.univ :=
    Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨y, hg Y y⟩
  have hbij (Y : (Spec X.functionField).Etale) (y : Y.left) :=
    have := hW Y y
    bijective_counit_app_app N (W Y y)
  have : Mono ε := by
    have (Y : (Spec X.functionField).Etaleᵒᵖ) : Mono (ε.hom.app Y) := by
      refine (AddCommGrpCat.mono_iff_injective _).2 ?_
      refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
      have key (y : Y.unop.left) : F.obj.map (g Y.unop y).op x = 0 := by
        have h := NatTrans.naturality_apply ε.hom (g Y.unop y).op x
        rw [hx, map_zero] at h
        exact (hbij Y.unop y).1 (h.trans (map_zero _).symm)
      refine (isSheafFor_ofArrows _ (g Y.unop) (hcov Y.unop)).isSeparatedFor.ext
        fun Z f ⟨y⟩ ↦ show F.obj.map (g Y.unop y).op x = F.obj.map (g Y.unop y).op 0 from
          (key y).trans (map_zero _).symm
    have : Mono ε.hom := NatTrans.mono_of_mono_app _
    exact Sheaf.Hom.mono_of_presheaf_mono _ _ ε
  have : Epi ε := by
    have : Sheaf.IsLocallySurjective ε := by
      constructor
      intro Y t
      refine (Scheme.smallEtaleTopology _).superset_covering ?_
        ((ofArrows_mem_smallEtaleTopology_iff (g Y)).2 (hcov Y))
      refine (Sieve.generate_le_iff _ _).2 (Presieve.ofArrows_le_iff.2 fun y ↦ ?_)
      obtain ⟨s, hs⟩ := (hbij Y y).2 (N.obj.map (g Y y).op t)
      exact ⟨s, hs⟩
    exact Sheaf.epi_of_isLocallySurjective _
  exact isIso_of_mono_of_epi ε

end AlgebraicGeometry.Scheme
