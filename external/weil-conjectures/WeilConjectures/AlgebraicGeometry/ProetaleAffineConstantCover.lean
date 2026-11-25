/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.CategoryTheory.Sites.DisjointGluing
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # An affine cover with a fixed constant sheaf description

Source: blueprint `lemma-lattices-lisse-e-sheaves`, proof (2)
(blueprint: lem-sfb-proetale-affine-constant-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- A fixed constant description on a covering family can be realized on a single
surjective quasi-compact weakly etale affine cover.

Source: blueprint `lemma-lattices-lisse-e-sheaves`, proof (2), its finite affine
refinement of the trivializing covering
(blueprint: lem-sfb-proetale-affine-constant-cover).

Proof: apply the definition of the pro-etale topology to the covering sieve of
factorizations through the given family, at the terminal object. Refine the resulting
quasi-compact covering by finitely many affine opens. Each member factors through
one of the original covering objects, so restriction supplies its constant description.
Their finite disjoint union is affine; its structure map is weakly etale and surjective,
and is quasi-compact because the base is quasi-separated. The component inclusions
form a disjoint covering family: an object mapping compatibly to two distinct
components is empty. Glue the local isomorphisms to the restriction of the global
constant sheaf using the sheaf of morphisms, then use the constant-sheaf restriction
isomorphism. The same argument includes the empty base and empty refinement. -/
theorem exists_affine_constant_cover (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2))) (S : Type (u + 2))
    (I : Type (u + 1)) (U : I → X.ProEt)
    (hU : (Scheme.ProEt.topology X).CoversTop U)
    (e : ∀ i, F.over (U i) ≅
      ((constantSheaf (Scheme.ProEt.topology X) (Type (u + 2))).obj S).over (U i)) :
    ∃ (V : Scheme.{u}) (p : V ⟶ X) (_hw : WeaklyEtale p) (_ha : IsAffine V)
      (_hs : Surjective p) (_hq : QuasiCompact p),
      Nonempty (F.over (Scheme.ProEt.mk p) ≅
        (constantSheaf ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk p))
          (Type (u + 2))).obj S) := by
  classical
  let J := Scheme.ProEt.topology X
  let C := (constantSheaf J (Type (u + 2))).obj S
  let T := Scheme.ProEt.mk (𝟙 X)
  obtain ⟨P, hP, hPS⟩ := Scheme.ProEt.mem_topology_iff.mp (hU T)
  obtain ⟨𝒰, _, h𝒰⟩ := (Scheme.mem_propQCPrecoverage_iff_exists_quasiCompactCover
    (P := @WeaklyEtale)).mp (Scheme.ProEt.mem_precoverage_iff.mp hP)
  have : CompactSpace T.left := inferInstanceAs (CompactSpace X)
  obtain ⟨𝒱, g, hfin, _⟩ := QuasiCompactCover.exists_hom.{u + 1, u} 𝒰
  let := hfin
  have hmem (i : 𝒰.I₀) :
      P.map (Scheme.ProEt.forget X ⋙ Over.forget X) (𝒰.f i) := by
    rw [h𝒰]
    exact ⟨i⟩
  choose Z hZ a ha hZa using fun i ↦ Presieve.map_iff.mp (hmem i)
  have hweak (i : 𝒱.I₀) : WeaklyEtale (𝒱.f i) := 𝒱.map_prop i
  let V (i : 𝒱.I₀) := Scheme.ProEt.mk (𝒱.f i)
  have factor (i : 𝒱.I₀) : ∃ j : I, Nonempty (V i ⟶ U j) := by
    obtain ⟨j, ⟨v⟩⟩ := hPS _ _ (ha (g.s₀ i))
    refine ⟨j, ⟨?_ ≫ v⟩⟩
    refine MorphismProperty.Over.homMk
      (g.h₀ i ≫ eqToHom (hZ (g.s₀ i)).symm) ?_
    have hz := hZa (g.s₀ i)
    change (g.h₀ i ≫ eqToHom (hZ (g.s₀ i)).symm) ≫ (Z (g.s₀ i)).hom = 𝒱.f i
    have hz' : (a (g.s₀ i)).left =
        eqToHom (hZ (g.s₀ i)) ≫ 𝒰.f (g.s₀ i) := hz
    have ht : (Z (g.s₀ i)).hom = (a (g.s₀ i)).left := by
      have h := MorphismProperty.Over.w (a (g.s₀ i))
      change (a (g.s₀ i)).left ≫ 𝟙 X = (Z (g.s₀ i)).hom at h
      exact h.symm.trans (Category.comp_id (a (g.s₀ i)).left)
    rw [ht, hz', Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, g.w₀]
    rfl
  choose j v using factor
  let ev (i : 𝒱.I₀) : F.over (V i) ≅ C.over (V i) :=
    (F.pushforwardOverMapIso (v i).some).symm ≪≫
      (J.overMapPullback _ (v i).some).mapIso (e (j i)) ≪≫
        C.pushforwardOverMapIso (v i).some
  let p : (∐ fun i ↦ (V i).left) ⟶ X := Sigma.desc (fun i ↦ (V i).hom)
  have hpw : WeaklyEtale p := IsZariskiLocalAtSource.sigmaDesc fun i ↦ hweak i
  have hps : Surjective p := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨𝒱.cover.idx x, 𝒱.cover.covers x⟩
  have hpa : IsAffine (∐ fun i ↦ (V i).left) := by
    change IsAffine (∐ fun i ↦ Spec (𝒱.X i))
    infer_instance
  have hpq : QuasiCompact p := inferInstance
  let W := Scheme.ProEt.mk p
  let inc (i : 𝒱.I₀) : V i ⟶ W :=
    MorphismProperty.Over.homMk (Sigma.ι (fun i ↦ (V i).left) i) (Sigma.ι_comp_desc _ _)
  have hd : Presieve.IsDisjointFamily inc J := by
    constructor
    · intro i
      exact (Scheme.ProEt.forget X ⋙ Over.forget X).mono_of_mono_map
        (inferInstanceAs (Mono (Sigma.ι (fun i ↦ (V i).left) i)))
    · intro i k hik A a b hab
      have hempty : IsEmpty A.left := by
        constructor
        intro x
        have hh : a.left ≫ (inc i).left = b.left ≫ (inc k).left :=
          congrArg (fun f ↦ f.left) hab
        have hx := congrArg (fun f : A.left ⟶ W.left ↦ f x) hh
        exact hik (congrArg Sigma.fst
          ((AlgebraicGeometry.sigmaι_eq_iff (fun i ↦ (V i).left) i k (a.left x)
            (b.left x)).mp hx))
      exact Scheme.ProEt.bot_mem_topology A
  have hc : Sieve.ofArrows V inc ∈ J W := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    apply Scheme.zariskiPrecoverage_le_proetalePrecoverage
    apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
    refine ⟨?_, fun i ↦ inferInstanceAs (IsOpenImmersion
      (Sigma.ι (fun i ↦ (V i).left) i))⟩
    intro x
    obtain ⟨i, y, hy⟩ := (AlgebraicGeometry.sigmaOpenCover (fun i ↦ (V i).left)).exists_eq x
    exact ⟨i, y, hy⟩
  obtain ⟨ew, _⟩ := hd.exists_iso hc F C ev
  exact ⟨_, p, hpw, hpa, hps, hpq,
    ⟨ew ≪≫ (J.overPullbackConstantSheafIso (Type (u + 2)) W).app S⟩⟩

end AlgebraicGeometry.ProEtale
