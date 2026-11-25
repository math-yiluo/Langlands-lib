/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.FinitePresentationAffineChartModels
import Mathlib.Data.Finset.Order
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Finite-stage local module models

Source: Stacks Project, Tags 01ZR and 05N7.
(blueprint: lem-pc-fp-local-object-models). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem transport_chart_model
    {Xi Xk Xj X : Scheme.{u}} (V : Xi.OpenCover.{u}) (a : V.I₀)
    (xk : Xk ⟶ Xi) (xj : Xj ⟶ Xi) (t : Xj ⟶ Xk) (ht : t ≫ xk = xj)
    (pk : X ⟶ Xk) (pj : X ⟶ Xj) (hp : pj ≫ t = pk)
    (M : X.Modules)
    (N : ((V.pullback₁ xk).X a).Modules)
    (hNfp : N.IsFinitePresentation) (hNqc : N.IsQuasicoherent)
    (e : (Scheme.Modules.pullback (Scheme.Cover.pullbackHom (V.pullback₁ xk) pk a)).obj N ≅
      (Scheme.Modules.pullback (((V.pullback₁ xk).pullback₁ pk).f a)).obj M) :
    ∃ Nj : ((V.pullback₁ xj).X a).Modules,
      Nj.IsFinitePresentation ∧ Nj.IsQuasicoherent ∧
      Nonempty ((Scheme.Modules.pullback (Scheme.Cover.pullbackHom (V.pullback₁ xj) pj a)).obj Nj ≅
        (Scheme.Modules.pullback (((V.pullback₁ xj).pullback₁ pj).f a)).obj M) := by
  let Uk : Xk.OpenCover.{u} := V.pullback₁ xk
  let Uj : Xj.OpenCover.{u} := V.pullback₁ xj
  let g : Uj.X a ⟶ Uk.X a :=
    pullback.map xj (V.f a) xk (V.f a) t (𝟙 _) (𝟙 _)
      (by simpa using ht.symm) (by simp)
  have hg : g ≫ Uk.f a = Uj.f a ≫ t := by
    change g ≫ pullback.fst xk (V.f a) = pullback.fst xj (V.f a) ≫ t
    exact pullback.lift_fst _ _ _
  let h : (Uj.pullback₁ pj).X a ⟶ (Uk.pullback₁ pk).X a :=
    pullback.lift ((Uj.pullback₁ pj).f a) (Uj.pullbackHom pj a ≫ g) (by
      rw [Category.assoc, hg, ← Category.assoc, Uj.pullbackHom_map,
        Category.assoc, hp])
  have h₁ : h ≫ (Uk.pullback₁ pk).f a = (Uj.pullback₁ pj).f a := by
    dsimp [h]
    exact pullback.lift_fst _ _ _
  have h₂ : h ≫ Uk.pullbackHom pk a = Uj.pullbackHom pj a ≫ g := by
    dsimp [h]
    exact pullback.lift_snd _ _ _
  let Nj := (Scheme.Modules.pullback g).obj N
  have : N.IsFinitePresentation := hNfp
  have : N.IsQuasicoherent := hNqc
  refine ⟨Nj, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp (Uj.pullbackHom pj a) g).app N ≪≫
    ((Scheme.Modules.pullbackCongr h₂.symm).app N) ≪≫
    ((Scheme.Modules.pullbackComp h (Uk.pullbackHom pk a)).app N).symm ≪≫
    (Scheme.Modules.pullback h).mapIso e ≪≫
    (Scheme.Modules.pullbackComp h ((Uk.pullback₁ pk).f a)).app M ≪≫
    (Scheme.Modules.pullbackCongr h₁).app M

/-- Local finitely presented modules lift on a finite affine cover, without any overlap maps.
Source: Stacks Project, Limits, Tag 01ZR, first proof; Algebra, Tag 05N7, object clause.
(blueprint: lem-pc-fp-local-object-models).

Proof: Quasi-compactness of f over the affine base makes Xi quasi-compact. Take a finite
subcover of its affine cover. On each chart the stage coordinate rings are base changes
of the chart ring, and the limit chart ring is their directed colimit: first identify
c.pt with Spec(colim R) by uniqueness of limits, then use the spectrum/tensor-product
pullback comparison. The restriction of M is quasi-coherent and finitely presented,
so its module of sections on this affine chart is finitely presented. Apply the object
clause of 05N7 to obtain a finitely presented stage module, realized geometrically by
its associated quasi-coherent sheaf. Lift its finite relation matrix, rather than
choosing arbitrary sheaf data. Finitely many charts give finitely many stages; choose
a common upper bound also above i, and extend scalars on all charts to that stage.
Finite presentation survives extension of scalars; the affine module equivalence and
pullback comparisons supply the displayed component isomorphisms. The pulled-back
charts form a finite affine cover of Xj. For a preorder take the partial-order quotient
of the upper tail; equivalent indices give canonically isomorphic rings. The fixed i
makes this tail nonempty. Empty Xi uses the empty family; zero modules and zero rings
use their zero presentations. No overlap identifications are claimed. -/
theorem exists_finitePresentation_local_object_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : (pullback f (c.π.app (op i))).Modules)
    (hM : M.IsFinitePresentation) (hMq : M.IsQuasicoherent) :
    ∃ (j : I) (hij : i ≤ j)
      (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u}),
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
      Finite U.I₀ ∧ (∀ a, IsAffine (U.X a)) ∧
      ∃ N : (a : U.I₀) → (U.X a).Modules,
        (∀ a, (N a).IsFinitePresentation) ∧ (∀ a, (N a).IsQuasicoherent) ∧
        (∀ a, Nonempty ((Scheme.Modules.pullback (U.pullbackHom p a)).obj (N a) ≅
          (Scheme.Modules.pullback ((U.pullback₁ p).f a)).obj M)) := by
  classical
  have : CompactSpace Xi := QuasiCompact.compactSpace_of_compactSpace f
  let V : Xi.OpenCover.{u} := Xi.affineCover.finiteSubcover
  have hV (a : V.I₀) : IsAffine (V.X a) := by
    dsimp [V]
    infer_instance
  have hchart (a : V.I₀) :=
    exists_finitePresentation_affine_chart_object_models R c hc i f M hM hMq V a (hV a)
  choose k hik N hNfp hNqc e using hchart
  have : Nonempty I := ⟨i⟩
  obtain ⟨j, hj⟩ := (insert i (Finset.univ.image k)).exists_le
  have hij : i ≤ j := hj i (Finset.mem_insert_self _ _)
  have hkj (a : V.I₀) : k a ≤ j :=
    hj (k a) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩))
  let U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u} :=
    V.pullback₁ (pullback.fst f (Spec.map (R.map (homOfLE hij))))
  refine ⟨j, hij, U, ?_, ?_, ?_⟩
  · change Finite V.I₀
    infer_instance
  · intro a
    have : IsAffine (V.X a) := hV a
    have hstage : IsAffineHom (Spec.map (R.map (homOfLE hij))) := inferInstance
    have hfst : IsAffineHom (pullback.fst f (Spec.map (R.map (homOfLE hij)))) :=
      MorphismProperty.pullback_fst _ _ hstage
    change IsAffine (pullback (pullback.fst f _) (V.f a))
    exact isAffine_of_isAffineHom (pullback.snd _ _)
  · have hmodels (a : V.I₀) :
        let p := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
        ∃ Nj : (U.X a).Modules,
          Nj.IsFinitePresentation ∧ Nj.IsQuasicoherent ∧
          Nonempty ((Scheme.Modules.pullback (U.pullbackHom p a)).obj Nj ≅
            (Scheme.Modules.pullback ((U.pullback₁ p).f a)).obj M) := by
      let Tk := Over.mk (Spec.map (R.map (homOfLE (hik a))))
      let Tj := Over.mk (Spec.map (R.map (homOfLE hij)))
      let T := Over.mk (c.π.app (op i))
      let q : Tj ⟶ Tk := Over.homMk (Spec.map (R.map (homOfLE (hkj a)))) (by
        dsimp [Tk, Tj]
        rw [← Spec.map_comp, ← R.map_comp]
        rfl)
      let ak : T ⟶ Tk := Over.homMk (c.π.app (op (k a))) (c.w (homOfLE (hik a)).op)
      let aj : T ⟶ Tj := Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)
      have ht : baseChangeMap f q ≫ pullback.fst f Tk.hom =
          pullback.fst f Tj.hom := by
        dsimp [baseChangeMap]
        simp
      have hp : baseChangeMap f aj ≫ baseChangeMap f q = baseChangeMap f ak := by
        rw [← baseChangeMap_comp]
        congr 1
        ext
        exact c.w (homOfLE (hkj a)).op
      exact transport_chart_model V a (pullback.fst f Tk.hom) (pullback.fst f Tj.hom)
        (baseChangeMap f q) ht (baseChangeMap f ak) (baseChangeMap f aj) hp
        M (N a) (hNfp a) (hNqc a) (e a).some
    choose Nj hNjfp hNjqc e' using hmodels
    exact ⟨Nj, hNjfp, hNjqc, e'⟩

end AlgebraicGeometry
