/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization

/-!
# Proper exchange over a geometric point

Source: Stacks Project, Tags 0A3T and 0A3U.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- On an algebraically closed field the identity neighbourhood computes the stalk.
Source: Stacks Project, Tag 03QO.
(auxiliary; not a blueprint node). -/
private theorem isIso_geometricPointGlobalGerm
    (Λ : Type (u + 1)) [CommRing Λ] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (G : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (geometricPointGlobalGerm Λ Ω G) := by
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (forget (ModuleCat.{u + 1} Λ)) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))
  let T := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))
  let t : Φ.fiber.obj T := Over.homMk (𝟙 _) (Category.comp_id _)
  have hsec (U : (Spec (.of Ω)).Etale) (x : Φ.fiber.obj U) :
      ∃ g : T ⟶ U, Φ.fiber.map g t = x := by
    refine ⟨MorphismProperty.Over.homMk x.left x.w, ?_⟩
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  have hg : IsIso (Φ.toPresheafFiber T t G.obj) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro a b hab
      obtain ⟨U, f, x, _, heq⟩ :=
        (Φ.toPresheafFiber_eq_iff' (P := G.obj) T t a b).mp hab
      obtain ⟨g, _⟩ := hsec U x
      have hgf : g ≫ f = 𝟙 T := by
        apply MorphismProperty.Over.Hom.ext
        have hf' : f.left ≫ T.hom = U.hom := f.w
        have hf : f.left = U.hom := by
          change f.left ≫ 𝟙 _ = U.hom at hf'
          simpa only [Category.comp_id] using hf'
        change g.left ≫ f.left = 𝟙 _
        rw [hf]
        exact g.w
      have h := congrArg (G.obj.map g.op) heq
      simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hgf] using h
    · intro z
      obtain ⟨U, x, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := G.obj) z
      obtain ⟨g, hg⟩ := hsec U x
      refine ⟨G.obj.map g.op a, ?_⟩
      rw [Φ.toPresheafFiber_w_apply, hg]
  unfold geometricPointGlobalGerm
  exact IsIso.comp_isIso

/-- Proper exchange for base change to an algebraically closed field.

Source: Stacks Project, Tags 0A3T and 0A3U, degree-zero stalk calculation.
(auxiliary; not a blueprint node).

Proof: forget the module structure and compute the stalk of the direct image as the
filtered colimit of sections on pointed affine etale neighbourhoods. Continuity of
sections identifies this colimit with sections on the strict-henselian base change.
Properness is preserved by base change. The henselian degree-zero comparison identifies
these sections with sections on the closed fibre. Its residue field is separably closed;
invariance of sections under extension of a separably closed field (Tag 0A3I) identifies
these with sections on the fibre over the given algebraically closed field. On the small
etale site of the spectrum of that field, sections at the terminal object compute the
unique geometric stalk. Expanding the unit-square-counit definition of exchange shows
that a section represented on a pointed neighbourhood is sent to its restriction on the
same fibre. Consequently the actual exchange map, rather than an unspecified comparison,
is bijective on that stalk. Conservativity gives the sheaf isomorphism; the forgetful
functor from modules reflects isomorphisms. This argument needs no torsion hypothesis.
It also applies to the empty fibre, whose section module is zero. -/
theorem isIso_baseChangeMap_app_of_isProper_geometricPoint
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsProper f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) := by
  let A := ModuleCat.{u + 1} Λ
  let φ := (baseChangeMap A sq.toCommSq).app F
  have hi : IsIso ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map φ) := by
    obtain ⟨hlocal, hstrict, t, q, ht, sqR, hq, e, he⟩ :=
      qcqs_geometricExchange_factorization Λ sq F
    let := hlocal
    let := hstrict
    have hrestrict := isIso_globalSectionsUpperStarMap_of_strictLocal_geometricClosedPoint
      Λ (Scheme.strictHenselizationRing s) t ht sqR
        ((upperStar A (CategoryTheory.Limits.pullback.fst f
          (Scheme.strictHenselizationStructuralMap s))).obj F)
    have hgerm := isIso_geometricPointGlobalGerm Λ Ω
      ((lowerStar A f').obj ((upperStar A g').obj F))
    change IsIso ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
      ((baseChangeMap A sq.toCommSq).app F))
    rw [he]
    infer_instance
  have hc := Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    (Spec (.of Ω)) (fun _ : PUnit.{u + 1} ↦ 𝟙 (Spec (.of Ω))) (by
      ext x
      exact ⟨fun _ ↦ Set.mem_univ x,
        fun _ ↦ Set.mem_iUnion.mpr ⟨PUnit.unit, ⟨x, rfl⟩⟩⟩)
  apply ((hc.jointlyReflectIsomorphisms A).isIso_iff φ).2
  rintro ⟨-, ⟨i⟩⟩
  rw [NatIso.isIso_map_iff ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).uliftSheafFiberIso A)]
  exact hi

end AlgebraicGeometry.Etale
