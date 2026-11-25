/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.AlgebraicGeometry.GradedRealizationLocalGeneratorsEpi
import WeilConjectures.AlgebraicGeometry.AffineModuleFiniteType
/-! # Homogeneous generators give finite type on the realization

Source: Stacks Project, Tag 0897, finite-type paragraph, with Tags 01SB and 01PB.
(blueprint: lem-weil-pbc-graded-module-realization-finite-type).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry

/-- Any quasi-coherent realization compatible with a locally finite family of
homogeneous generators is of finite type. No Noetherian or properness assumption is used.

Source: Stacks Project, Tag 0897, finite-type paragraph, with Tags 01SB and 01PB.
(blueprint: lem-weil-pbc-graded-module-realization-finite-type).

Proof: Near x choose U, degrees d_i and sections s_i from hfinite. Shrink U to an
affine neighbourhood; its inverse image under pi is affine since pi is a base change
of a morphism between affine schemes. The sections iota_(d_i)(s_i) are sections of F
on that inverse image. The coproduct condition means that every pushforward section
is locally a finite sum of images of homogeneous sections. The spanning condition
hfinite expresses each such section locally in terms of mu_(d_i)(b)(s_i), with
coefficients in O_X. The compatibility square turns these expressions into linear
combinations of the same finite family iota_(d_i)(s_i), now with coefficients in
pi_* O_Y: multiply the pulled-back O_X coefficients by fB^sharp(b). Thus they generate
pi_* F as a module over pi_* O_Y near x. Quasi-coherence and localization turn this
local generation on the affine base into finite generation on its affine inverse
image: the cokernel of the finite free map vanishes on the affine base cover, hence
vanishes on the inverse image under the affine module correspondence. The affine
finite-type correspondence gives F.IsFiniteType there. These inverse images cover Y,
so finite type is local and gives the result. If the generating family is empty the
same argument makes the module zero; if X is empty the covering assertion is vacuous. -/
theorem gradedModule_realization_isFiniteType
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (graded : ℕ → Submodule A B)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (G : ℕ → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)))
    (hfinite : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      ∃ (r : ℕ) (d : Fin r → ℕ) (s : ∀ i : Fin r, (G (d i)).val.obj (op U)),
        ∀ (m : ℕ) (V : X.Opens) (hVU : V ≤ U) (t : (G m).val.obj (op V))
          (y : X), y ∈ V → ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
            (G m).val.map (homOfLE hWV).op t ∈
              Submodule.span ((moduleRings X.toRingedSpace).obj.obj (op W))
                {z | ∃ (i : Fin r), d i ≤ m ∧
                  ∃ b : graded (m - d i),
                    HEq z ((mu (d i) (m - d i) b).val.app (op W)
                      ((G (d i)).val.map (homOfLE (hWV.trans hVU)).op (s i)))})
    :
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let Y := pullback f g
    let pi : Y ⟶ X := pullback.fst f g
    let fB : Y ⟶ Spec (.of B) := pullback.snd f g
    ∀ (F : Y.Modules), F.IsQuasicoherent →
      ∀ (iota : ∀ m : ℕ, G m ⟶ (Scheme.Modules.pushforward pi).obj F),
        Nonempty (IsColimit (Cofan.mk ((Scheme.Modules.pushforward pi).obj F) iota)) →
          (∀ (k m : ℕ) (b : graded k),
            mu m k b ≫ iota (m + k) = iota m ≫
              (Scheme.Modules.pushforward pi).map
                (F.smulHom (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b.val))) →
          F.IsFiniteType := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      classical
      dsimp only
      intro F hF iota hcoprod hcompat
      let pi := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      have : IsAffineHom pi := MorphismProperty.pullback_fst f
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) (inferInstance : IsAffineHom _)
      let fB := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      let AR := (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((TopCat.Sheaf.pushforward CommRingCat.{u} pi.base).obj (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).sheaf)
      let R := SheafOfModules.pushforward.{u} (F := TopologicalSpace.Opens.map pi.base)
        (S := AR) (R := (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).ringCatSheaf) (𝟙 AR)
      let M := R.obj F
      choose U hx r d s hs using hfinite
      let a (x : X) : ULift.{u} (Fin (r x)) → (M.over (U x)).sections := fun i ↦
        PresheafOfModules.sectionsMk
          (fun V ↦ M.val.presheaf.map V.unop.hom.op
            ((iota (d x i.down)).val.app (op (U x)) (s x i.down)))
          (fun V W v ↦ by
            change M.val.presheaf.map v.unop.left.op _ = _
            rw [← Functor.map_comp_apply]
            rfl)
      have hepi (x : X) : Epi ((M.over (U x)).freeHomEquiv.symm (a x)) :=
        gradedRealization_local_generators_epi graded pi fB G mu (U x) (r x) (d x)
          (s x) (hs x) F iota hcoprod hcompat
      let q : M.LocalGeneratorsData :=
        { I := X
          X := U
          coversTop := by
            rw [Opens.coversTop_iff]
            refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ ?_)
            exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
          generators x := { I := ULift.{u} (Fin (r x)), s := a x, epi := hepi x } }
      have hq : q.IsFiniteType := by
        refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := q) (fun x ↦ ?_)
        exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin (r x))))⟩
      have hM : M.IsFiniteType := by
        apply SheafOfModules.IsFiniteType.mk (M := M)
        exact ⟨q, hq⟩
      have hMq : M.IsQuasicoherent :=
        (Scheme.Modules.affine_module_correspondence pi).2.1 F hF
      exact (Scheme.Modules.affine_module_finite_type pi M hMq F hF (Iso.refl M)).mp hM

end AlgebraicGeometry
