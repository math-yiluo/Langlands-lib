/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.FiniteConstantLabelSubgroupNeighborhood

/-! # Finite-operation abelian charts near a point

Source: Stacks Project, Tag 03RU (definitions); explicit finite-operation
refinement of steps 1--3 of `lem-weil-pbc-finite-constant-abelian-refinement`.
(blueprint: lem-weil-pbc-finite-constant-abelian-neighborhood).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- A finite constant set chart admits, near each underlying point, a locally bijective
map from an actual constant abelian presheaf into the restricted abelian sheaf.
Source: Stacks Project, Tag 03RU (definitions only); explicit argument,
steps 1--3 of the finite-operation refinement
(blueprint: lem-weil-pbc-finite-constant-abelian-neighborhood).

Proof: choose an algebraic closure of the residue field at the given point. Identify the
localized site at U with the small etale site of its domain. The constant set chart
identifies its labels with the underlying abelian stalk at this geometric point; transport
addition, zero and negation from that stalk to the labels. Constant labels give sections
of G. Equality of germs is equality on some pointed etale neighborhood. Apply this to
zero, every negative and every pairwise sum. There are finitely many comparisons, so
cofilteredness gives one pointed neighborhood where all hold. On every object above that
neighborhood, restriction of these sections is an additive map from the transported
abelian group; restriction compatibility makes these maps a natural transformation from
the constant abelian presheaf. Its underlying map is the set chart composed with the
constant-presheaf sheafification unit, after restriction. This is locally bijective:
restriction preserves local bijectivity and the chart is an isomorphism. The neighborhood
contains a point above the specified underlying point. The abelian group is finite since
its underlying labels are S. If S is empty, the geometric stalk, which contains zero,
cannot be identified with S, so this case is impossible. -/
theorem finite_constant_abelian_neighborhood {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : Y.Etale)
    (S : Type (u + 1)) [Finite S]
    (e : ((sheafCompose Y.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).over U ≅
        (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1))).obj S)
    (x : U.left) :
    ∃ (V : U.left.Etale) (v : V.left), V.hom v = x ∧
      ∃ (M : AddCommGrpCat.{u + 1}), Finite M ∧
        ∃ e' : (constantSheaf
          (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
          (Type (u + 1))).obj (M : Type (u + 1)) ≅
            (sheafCompose
              (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
                (G.over ((MorphismProperty.Over.map ⊤ U.prop).obj V)),
          ∃ α : (Functor.const
            (Over ((MorphismProperty.Over.map ⊤ U.prop).obj V))ᵒᵖ).obj M ⟶
              (G.over ((MorphismProperty.Over.map ⊤ U.prop).obj V)).obj,
            Functor.whiskerRight α (CategoryTheory.forget AddCommGrpCat.{u + 1}) =
              toSheafify
                (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
                ((Functor.const
                  (Over ((MorphismProperty.Over.map ⊤ U.prop).obj V))ᵒᵖ).obj
                    (M : Type (u + 1))) ≫ e'.hom.hom := by
  classical
  -- Use local closure of the finite label sections, then transport their subgroup structure.
  obtain ⟨V, v, hv, e', hinj, hzero, hadd, hneg⟩ :=
    finite_constant_label_subgroup_neighborhood G U S e x
  let A := (MorphismProperty.Over.map ⊤ U.prop).obj V
  let F := G.over A
  let T := F.obj.obj (op (Over.mk (𝟙 A)))
  let t : S → T := fun s ↦
    (toSheafify (Y.smallEtaleTopology.over A)
      ((Functor.const (Over A)ᵒᵖ).obj S) ≫ e'.hom.hom).app
        (op (Over.mk (𝟙 A))) s
  let H : AddSubgroup T :=
    { carrier := Set.range t
      zero_mem' := hzero
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact hadd a b
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        exact hneg a }
  let q : S ≃ H := Equiv.ofBijective (fun s ↦ ⟨t s, ⟨s, rfl⟩⟩)
    ⟨fun a b h ↦ hinj (congrArg Subtype.val h), by
      rintro ⟨z, a, rfl⟩
      exact ⟨a, rfl⟩⟩
  let : AddCommGroup S := q.addCommGroup
  let M : AddCommGrpCat.{u + 1} := AddCommGrpCat.of S
  let η : M →+ T := H.subtype.comp q.addEquiv.toAddMonoidHom
  have hM : Finite M := inferInstance
  let β := toSheafify
    (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
    ((Functor.const
      (Over ((MorphismProperty.Over.map ⊤ U.prop).obj V))ᵒᵖ).obj
        (M : Type (u + 1))) ≫ e'.hom.hom
  let α : (Functor.const
      (Over ((MorphismProperty.Over.map ⊤ U.prop).obj V))ᵒᵖ).obj M ⟶
        (G.over ((MorphismProperty.Over.map ⊤ U.prop).obj V)).obj :=
    { app := fun W ↦ AddCommGrpCat.ofHom
        { toFun := β.app W
          map_zero' := by
            have hnat := ConcreteCategory.congr_hom
              (β.naturality (Over.mkIdTerminal.from W.unop).op) (0 : M)
            change β.app W (0 : M) =
              (F.obj.map (Over.mkIdTerminal.from W.unop).op) (t 0) at hnat
            rw [hnat]
            change (F.obj.map (Over.mkIdTerminal.from W.unop).op) (η 0) = 0
            simp
          map_add' := by
            intro a b
            have hnat (m : M) := ConcreteCategory.congr_hom
              (β.naturality (Over.mkIdTerminal.from W.unop).op) m
            change ∀ m : M, β.app W m =
              (F.obj.map (Over.mkIdTerminal.from W.unop).op) (t m) at hnat
            rw [hnat, hnat, hnat]
            change (F.obj.map (Over.mkIdTerminal.from W.unop).op) (η (a + b)) =
              (F.obj.map (Over.mkIdTerminal.from W.unop).op) (η a) +
                (F.obj.map (Over.mkIdTerminal.from W.unop).op) (η b)
            simp }
      naturality := by
        intro W W' f
        apply AddCommGrpCat.ext
        intro m
        exact ConcreteCategory.congr_hom (β.naturality f) m }
  refine ⟨V, v, hv, M, hM, e', α, ?_⟩
  rfl

end AlgebraicGeometry.Scheme
