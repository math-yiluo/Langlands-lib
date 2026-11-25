/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.SmoothLimitDerivedDirectImageExchange
import WeilConjectures.FieldTheory.SeparableSmoothColimit
import Mathlib.FieldTheory.SeparablyGenerated

/-! # Derived relative exchange for a torsion sheaf under field extension

Source: Stacks Project, Tag 0F1C, applied to a sheaf in degree zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Field extension commutes with the derived direct image of a sheaf annihilated by
an integer invertible in the base field. This statement concerns arbitrary sheaves,
and does not assert acyclicity of the pullback of an injective module sheaf.
Source: Stacks Project, Lemma 59.90.1, Tag 0F1C.
(blueprint: lem-sc-field-extension-derived-direct-image-exchange)

Proof: Because k is algebraically closed it is perfect. Every finitely generated
intermediate field is separably generated over k by the perfect-field transcendence
basis theorem. Thus K/k is a separable extension. Write K as the filtered colimit of
its finitely generated smooth k-subalgebras (Tag 07BV). Construct their spectra as a
cofiltered diagram over Spec k, and use the actual algebra inclusions for its
transition maps and cone. Spec sends the colimit cocone to a limit cone. Each stage
is smooth over k, and all transitions and structure maps are affine, hence qcqs.
Apply smooth-stage exchange and affine inverse-limit continuity to this diagram
and F in degree zero (Tag 0F09). Exact inverse image commutes with the degree-zero
single complex. This gives the displayed isomorphism. K need not be algebraically
closed. The zero sheaf and empty scheme give zero objects. If n = 1, F is zero;
n = 0 is excluded by hn. -/
theorem nonempty_fieldExtension_derivedDirectImage_single_iso
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (n : ℕ) (hn : (n : k) ≠ 0)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : n • 𝟙 F = 0) :
    Nonempty
      (((upperStar AddCommGrpCat.{u + 1}
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapDerivedCategory).obj
          ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
        (lowerStar AddCommGrpCat.{u + 1}
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1}
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj F))) := by
  have hsep : Algebra.IsSeparableExtension k K := by
    intro L hL
    let : Algebra.EssFiniteType k L := (IntermediateField.essFiniteType_iff).2 hL
    obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k L
    exact ⟨(s : Set L), hs, hsep⟩
  obtain ⟨hne, hdir, _, _, ⟨hc₀⟩, _, _⟩ :=
    FieldTheory.separable_extension_is_filtered_colimit_smooth hsep
  let A := {A : Subalgebra k K // Algebra.Smooth k A ∧ A.FG}
  let : Nonempty A := hne
  let : IsDirectedOrder A := ⟨hdir⟩
  let S := (FieldTheory.smoothSubalgebraDiagram k K).op ⋙ Scheme.Spec
  let a : S ⟶ (Functor.const Aᵒᵖ).obj (Spec (.of k)) :=
    { app i := Spec.map (CommRingCat.ofHom (algebraMap k i.unop.1))
      naturality := by
        intro i j h
        dsimp [S, FieldTheory.smoothSubalgebraDiagram]
        rw [← Spec.map_comp]
        rfl }
  let D := Over.lift S a
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let c₀ := Scheme.Spec.mapCone (FieldTheory.smoothSubalgebraCocone k K).op
  let c : Cone D := Over.liftCone S a c₀ g (by
    intro i
    dsimp [c₀, a, FieldTheory.smoothSubalgebraCocone]
    rw [← Spec.map_comp]
    rfl)
  have hc : IsLimit ((Over.forget _).mapCone c) := hc₀
  have (i : Aᵒᵖ) : Smooth (D.obj i).hom := by
    let : Algebra.Smooth k i.unop.1 := i.unop.2.1
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k i.unop.1)))
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
    change (algebraMap k i.unop.1).Smooth
    exact RingHom.smooth_algebraMap.mpr inferInstance
  have (i : Aᵒᵖ) : QuasiCompact (D.obj i).hom := by
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k i.unop.1)))
    infer_instance
  have (i : Aᵒᵖ) : QuasiSeparated (D.obj i).hom := by
    change QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap k i.unop.1)))
    infer_instance
  have {i j : Aᵒᵖ} (h : i ⟶ j) : IsAffineHom (D.map h).left := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (leOfHom h.unop)).toRingHom))
    infer_instance
  have : QuasiCompact c.pt.hom := by change QuasiCompact g; infer_instance
  have : QuasiSeparated c.pt.hom := by change QuasiSeparated g; infer_instance
  exact nonempty_smoothLimit_derivedDirectImage_single_iso D c hc f n hn F hF

end AlgebraicGeometry.Etale
