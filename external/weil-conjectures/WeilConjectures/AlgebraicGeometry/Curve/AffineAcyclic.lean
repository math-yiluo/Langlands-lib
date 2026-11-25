/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing

/-!
# Sheaves on a curve which are acyclic on affine étale schemes

Let `C` be a curve over an algebraically closed field and `F` an abelian étale sheaf on `C` whose
restriction to every affine étale `C`-scheme has no cohomology in positive degrees (for instance
the étale sheaf of a quasi-coherent module). Then `H²(C, F) = 0`.

Choose an affine open `j : U ⟶ C` whose complement is a finite set of closed points. The unit
`F ⟶ j_* j^* F` is an isomorphism over `U`, so it is bijective on `H²`. Since `j` is affine, the
base change of an affine étale `C`-scheme to `U` is affine, so `R¹ j_* (j^* F) = 0` and the edge
map `H²(C, j_* j^* F) ⟶ H²(U, j^* F) = 0` is injective.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_two_of_forall_isAffine`: the vanishing of
  `H²(C, F)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- **Sheaves acyclic on affine étale schemes have no `H²` on a curve.** Let `C` be a curve over
an algebraically closed field `k` and `F` an abelian étale sheaf on `C` such that
`Hᵠ(W, w^* F) = 0` for every étale morphism `w : W ⟶ C` from an affine scheme and every `q ≥ 1`.
Then `H²(C, F) = 0`. -/
theorem IsCurve.subsingleton_sheafH_two_of_forall_isAffine [IsAlgClosed k]
    (f : C ⟶ Spec (.of k)) [IsCurve f] (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ (W : Scheme.{u}) (w : W ⟶ C), AlgebraicGeometry.Etale w → IsAffine W → ∀ q : ℕ,
      Subsingleton (Sheaf.H ((w)^*[AddCommGrpCat.{u + 1}].obj F) (q + 1))) :
    Subsingleton (Sheaf.H F 2) := by
  obtain ⟨U, hUaff, hUfin, hUcl⟩ := IsCurve.exists_isAffineOpen_finite_compl f
  have : IsAffine U := hUaff
  have hsep (x : C) (hx : x ∉ U) : IsSepClosed (C.residueField x) :=
    have := Scheme.isAlgClosed_residueField_of_isClosed f x (hUcl x hx)
    inferInstance
  let j := U.ι
  have : IsAffineHom j :=
    MorphismProperty.HasOfPostcompProperty.of_postcomp (W := @IsAffineHom)
      (W' := @IsSeparated) j f inferInstance inferInstance
  let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j
  let G := (j)^*[AddCommGrpCat.{u + 1}].obj F
  -- `H²(C, F) ≅ H²(C, j_* G)`
  have hunit : IsIso ((U.ι)^*[AddCommGrpCat.{u + 1}].map (adj.unit.app F)) := by
    have : IsIso ((j)^*[AddCommGrpCat.{u + 1}].map (adj.unit.app F) ≫ adj.counit.app G) := by
      rw [adj.left_triangle_components F]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app G)
  have hb := Etale.bijective_H_map_of_isIso_upperStar_map U hUfin hUcl hsep (adj.unit.app F)
    hunit 0
  suffices hs : Subsingleton (Sheaf.H ((j)_*[AddCommGrpCat.{u + 1}].obj G) 2) by
    have : Subsingleton (Sheaf.H (((j)^*[AddCommGrpCat.{u + 1}] ⋙
      (j)_*[AddCommGrpCat.{u + 1}]).obj F) (0 + 2)) := hs
    exact hb.injective.subsingleton
  -- the edge map `H²(C, j_* G) ⟶ H²(U, G) = 0` is injective, as `R¹ j_* G = 0`
  let ι : G ⟶ Injective.under G := Injective.ι G
  let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have he : Epi ((j)_*[AddCommGrpCat.{u + 1}].map (cokernel.π ι)) := by
    have : Sheaf.IsLocallySurjective ((j)_*[AddCommGrpCat.{u + 1}].map S.g) := by
      refine ⟨fun {V} s ↦ (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_⟩
      obtain ⟨A, hA, hxA, -⟩ : ∃ A : V.left.Opens, A ∈ V.left.affineOpens ∧ x ∈ A ∧ A ≤ ⊤ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.1
        V.left.isBasis_affineOpens) (TopologicalSpace.Opens.mem_top x)
      have : IsAffine A := hA
      let VA : C.Etale := MorphismProperty.Over.mk ⊤ (A.ι ≫ V.hom)
        (MorphismProperty.comp_mem _ _ _ inferInstance V.prop)
      let g : VA ⟶ V := MorphismProperty.Over.homMk A.ι rfl trivial
      refine ⟨VA, g, ?_, ⟨x, hxA⟩, rfl⟩
      -- the base change of `VA` to `U` is affine and étale over `C`
      let W := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ j).obj VA
      have : IsAffine W.left := inferInstanceAs (IsAffine (pullback (A.ι ≫ V.hom) j))
      have : AlgebraicGeometry.Etale W.hom := W.prop
      have : Subsingleton (Sheaf.H ((W.hom)^*[AddCommGrpCat.{u + 1}].obj S.X₁) 1) := by
        have : Subsingleton (Sheaf.H ((W.hom ≫ j)^*[AddCommGrpCat.{u + 1}].obj F) (0 + 1)) :=
          hF W.left (W.hom ≫ j) inferInstance inferInstance 0
        exact Sheaf.H.subsingleton_of_iso
          ((Etale.upperStarComp AddCommGrpCat.{u + 1} W.hom j).app F).symm 1
      obtain ⟨t, ht⟩ := Etale.surjective_app_of_subsingleton_H_one hS W
        (((j)_*[AddCommGrpCat.{u + 1}].obj S.X₃).obj.map g.op s)
      exact ⟨t, ht⟩
    exact Sheaf.epi_of_isLocallySurjective _
  have : Subsingleton (Sheaf.H ((𝟭 (Sheaf (U : Scheme.{u}).smallEtaleTopology
      AddCommGrpCat.{u + 1})).obj G) 2) := hF U j inferInstance inferInstance 1
  exact (Etale.injective_edgeMap_two j ι he).subsingleton

end AlgebraicGeometry
