/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyStageContinuity
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyClassDescent
import WeilConjectures.AlgebraicGeometry.EtaleLimitAffineStageEventualZero
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Continuity when one stage is affine

Source: Stacks Project, Tag 09YQ (theorem-colimit), cofinal-tail reduction.
(blueprint: lem-weil-pbc-etale-limit-cohomology-affine-stage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
/-- Affine-stage continuity applies when just one chosen stage is affine.

Source: Stacks Project, Tag 09YQ (theorem-colimit); cofinal-tail reduction in
step 1 of lem-weil-pbc-etale-limit-cohomology-qcqs-gluing.
(blueprint: lem-weil-pbc-etale-limit-cohomology-affine-stage).

Proof: the chosen stage is affine by its isomorphism to S. Class descent supplies
surjectivity of the canonical group-colimit comparison. For injectivity, represent
an element of its kernel at a stage and apply finite-stage detection of zero with
the chosen affine stage. The colimit transition equation then kills this
representative. A bijective group homomorphism is an isomorphism, so transport the
canonical colimit cocone along it; the comparison's leg equations identify the
transported cocone with B. The supplied affine-continuity hypothesis is retained
in the statement but is not needed by this elementwise reduction. The geometric
cofinal-tail argument remains in the finite-stage zero-detection theorem.
Empty affine schemes and degree zero use the same colimit argument. -/
theorem etale_limit_cohomology_affine_stage
    (haffine : ∀ {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (D : Jᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Jᵒᵖ, CompactSpace (D.obj i)] [∀ i : Jᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Jᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Jᵒᵖ, IsAffine (D.obj i)]
    (F : ∀ i : J, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : J} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : J, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : J) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : J ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : J, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : J) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (p : ℕ)
    (H : J ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : J, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p))
    (hH : ∀ (i j : J) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt p))
    (hB : ∀ i : J, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p)),
      Nonempty (IsColimit B))
    (S : Scheme.{u}) [IsAffine S] : EtaleCohomologyStageContinuity S  := by
  constructor
  intro I _ _ _ D c hc hcompact hqs hmaps F φ hid hcomp G eG hG L hL p H eH hH B eB hB
    i₀ hi
  obtain ⟨e⟩ := hi
  have : IsAffine (D.obj (op i₀)) := isAffine_of_isAffineHom e.hom
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have hlift := etale_limit_cohomology_class_descent D c hc F φ hid hcomp
    G eG hG L hL p H eH hH B eB hB
  have hzero := etale_limit_affine_stage_eventual_zero D c hc F φ hid hcomp
    G eG hG L hL p H eH hH B eB hB i₀
  have hbij : Function.Bijective (colimit.desc H B) := by
    constructor
    · apply (injective_iff_map_eq_zero (colimit.desc H B).hom).2
      intro z hz
      obtain ⟨i, x, rfl⟩ := Concrete.colimit_exists_rep H z
      have hx : (B.ι.app i).hom x = 0 := by
        change (colimit.ι H i ≫ colimit.desc H B) x = 0 at hz
        rwa [colimit.ι_desc] at hz
      obtain ⟨j, f, hf⟩ := hzero i x hx
      calc
        colimit.ι H i x = colimit.ι H j (H.map f x) :=
          (colimit.w_apply H f x).symm
        _ = 0 := by rw [hf]; exact map_zero (colimit.ι H j).hom
    · intro y
      obtain ⟨i, x, hx⟩ := hlift y
      refine ⟨colimit.ι H i x, ?_⟩
      change (colimit.ι H i ≫ colimit.desc H B) x = y
      rw [colimit.ι_desc]
      exact hx
  have : IsIso (colimit.desc H B) :=
    (ConcreteCategory.isIso_iff_bijective (colimit.desc H B)).2 hbij
  exact ⟨(colimit.isColimit H).ofIsoColimit
    (Cocone.ext (asIso (colimit.desc H B)) (by intro i; simp))⟩

end AlgebraicGeometry.Etale
