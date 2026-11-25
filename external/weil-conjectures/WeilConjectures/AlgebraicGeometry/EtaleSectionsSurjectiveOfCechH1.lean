/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

import WeilConjectures.CategoryTheory.Sites.CechCriterion

/-!
# Surjectivity of étale sections from vanishing Čech H¹

Source: Stacks Project, Cohomology on Sites, Lemma 03F8 (lemma-ses-cech-h1)
(blueprint: lem-weil-pbc-ses-cech-h1-surjective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

-- The product universal property identifies categorical cochains with families of sections.
private noncomputable def productSectionsIso {I : Type u}
    (G : I → AddCommGrpCat.{u}) :
    ∏ᶜ G ≅ AddCommGrpCat.of (∀ i, G i) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor G))
    (AddCommGrpCat.HasLimit.productLimitCone G).isLimit

private lemma productSectionsIso_hom_π {I : Type u}
    (G : I → AddCommGrpCat.{u}) (i : I) :
    (productSectionsIso G).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ i) =
      Pi.π G i :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk i)

private lemma productSectionsIso_hom_apply {I : Type u}
    (G : I → AddCommGrpCat.{u}) (c : (∏ᶜ G : AddCommGrpCat.{u})) (i : I) :
    (productSectionsIso G).hom c i = Pi.π G i c :=
  ConcreteCategory.congr_hom (productSectionsIso_hom_π G i) c

-- The product comparison commutes with every face and degeneracy, hence with the differential.
private noncomputable def cechSectionsIso.{v} {C : Type u} [Category.{v} C]
    {V : C} [HasFiniteProducts (Over V)] {I : Type (max u v)} (A : I → Over V)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ A).cech).obj
      ((Over.forget V).op ⋙ P) ≅ (Presheaf.cechCosimplicialObject A).obj P := by
  refine NatIso.ofComponents (fun n ↦ productSectionsIso
    (fun z : Fin (n.len + 1) → I ↦ P.obj (op (Presheaf.cechNerveObj A z).left))) ?_
  intro n m θ
  apply AddCommGrpCat.ext
  intro c
  funext z
  change (productSectionsIso
    (fun y : Fin (m.len + 1) → I ↦ P.obj (op (Presheaf.cechNerveObj A y).left))).hom _ z =
    P.map (Presheaf.cechNerveMap A z θ.toOrderHom).left.op
      ((productSectionsIso
        (fun y : Fin (n.len + 1) → I ↦ P.obj (op (Presheaf.cechNerveObj A y).left))).hom
          c (z ∘ θ.toOrderHom))
  rw [productSectionsIso_hom_apply, productSectionsIso_hom_apply]
  rw [← ConcreteCategory.comp_apply]
  change ((Pi.lift fun i : Fin (m.len + 1) → I ↦
    Pi.π (fun y : Fin (n.len + 1) → I ↦ P.obj (op (Presheaf.cechNerveObj A y).left))
      (i ∘ θ.toOrderHom) ≫ P.map (Presheaf.cechNerveMap A i θ.toOrderHom).left.op) ≫
        Pi.π (fun y : Fin (m.len + 1) → I ↦ P.obj (op (Presheaf.cechNerveObj A y).left))
          z) c = _
  rw [Pi.lift_comp_π]

/-- A short exact sequence of abelian étale sheaves is surjective on sections over `U`
if the kernel has vanishing Čech H¹ on a cofinal system of coverings of `U`.
`Cov` is the membership predicate of that system of indexed families. Its members are
coverings by `hcover`; `hcofinal` expresses refinement of every covering by a member.
The Čech complex is computed in `Over U`, so products are fibre products over `U`.
Source: Stacks Project, Lemma 03F8 (lemma-ses-cech-h1).
(blueprint: lem-weil-pbc-ses-cech-h1-surjective)

Proof (the node's six steps). (1) Short exactness makes `S.g` an epimorphism and `S.f`
its kernel inclusion. By situation-conventions, kernels are computed
sectionwise, so the section map of `S.f` is injective with image the kernel of `S.g`.
(2) Fix a section `h` of `S.X₃` over `U`. The epimorphism is locally surjective by
lem-weil-pbc-abelian-sheaf-epi-locally-surjective, so `h` has local lifts on a covering.
(3) Refine this covering to one in `Cov` using `hcofinal`, and restrict the lifts along
the refinement maps. Naturality shows that they remain lifts of `h`.
(4) On pairwise fibre products, the difference of the two restricted lifts maps to zero,
so it has a unique preimage in `S.X₁`. These differences form a Čech 1-cocycle: on triple
fibre products their alternating sum maps under the injective kernel inclusion to
`(g₂ - g₁) - (g₂ - g₀) + (g₁ - g₀) = 0`.
(5) By `hcech`, this cocycle is a coboundary of a 0-cochain of `S.X₁`. Subtract its image
under `S.f` from each local lift. The corrected lifts agree on pairwise fibre products
and still map to the restrictions of `h`.
(6) The sheaf condition of `S.X₂` glues these lifts to a section over `U`. Its image is `h`
by the separatedness of `S.X₃`. This proves surjectivity. -/
theorem surjective_sections_of_cech_h1_vanishing
    (X : Scheme.{u}) (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact) (U : X.Etale)
    (Cov : ∀ (I : Type (u + 1)) (V : I → X.Etale), (∀ i : I, V i ⟶ U) → Prop)
    (hcover : ∀ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U),
      Cov I V f → Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
    (hcofinal : ∀ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U),
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U →
      ∃ (K : Type (u + 1)) (W : K → X.Etale) (g : ∀ k : K, W k ⟶ U),
        Cov K W g ∧ ∀ k : K, ∃ (i : I) (t : W k ⟶ V i), t ≫ f i = g k)
    (hcech : ∀ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U),
      Cov I V f → IsZero (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
        ((Over.forget U).op ⋙ S.X₁.obj)).homology 1)) :
    Function.Surjective (S.g.hom.app (op U)) := by
  classical
  intro s
  have := hS.epi_g
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology S.g.hom :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} S.g).2 this
  -- Index all arrows in the image sieve, then use the given cofinality.
  let R := Presheaf.imageSieve S.g.hom s
  have hR : R ∈ X.smallEtaleTopology U := Presheaf.imageSieve_mem _ S.g.hom s
  let I := Σ V : X.Etale, { f : V ⟶ U // R f }
  let V : I → X.Etale := fun i ↦ i.1
  let f : ∀ i : I, V i ⟶ U := fun i ↦ i.2.1
  have hcov : Sieve.ofArrows V f ∈ X.smallEtaleTopology U := by
    apply X.smallEtaleTopology.superset_covering _ hR
    intro Y g hg
    exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨Y, g, hg⟩, 𝟙 Y, by simp [f]⟩
  obtain ⟨K, W, g, hCov, href⟩ := hcofinal I V f hcov
  have hlift : ∀ k : K, ∃ t : S.X₂.obj.obj (op (W k)),
      S.g.hom.app _ t = S.X₃.obj.map (g k).op s := by
    intro k
    obtain ⟨i, a, ha⟩ := href k
    obtain ⟨t, ht⟩ := i.2.2
    refine ⟨S.X₂.obj.map a.op t, ?_⟩
    rw [NatTrans.naturality_apply, ht, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, ha]
  choose t ht using hlift
  let A : K → Over U := fun k ↦ Over.mk (g k)
  -- Transfer vanishing of Mathlib Čech H¹ to exactness of the explicit cochain complex.
  have hA : ((Presheaf.cechComplex A).obj S.X₁.obj).ExactAt 1 := by
    have h := (HomologicalComplex.exactAt_iff_isZero_homology _ 1).2 (hcech K W g hCov)
    exact h.of_iso ((AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
      (cechSectionsIso A S.X₁.obj))
  let a : ((Presheaf.cechComplex A).obj S.X₂.obj).X 0 := fun z ↦
    S.X₂.obj.map (Pi.π (fun l ↦ A (z l)) 0).left.op (t (z 0))
  have ha (z : Fin 1 → K) : ((Presheaf.cechComplex A).map S.g.hom).f 0 a z =
      S.X₃.obj.map (Presheaf.cechNerveObj A z).hom.op s := by
    rw [Presheaf.cechComplex_map_f_apply, NatTrans.naturality_apply]
    erw [ht]
    change S.X₃.obj.map (Pi.π (fun l ↦ A (z l)) 0).left.op
      (S.X₃.obj.map (A (z 0)).hom.op s) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w]
  -- The differential of the local lifts comes from a kernel-valued cocycle.
  obtain ⟨e, he⟩ := Presheaf.exists_cechComplex_map_f_eq A S.f.hom S.g.hom
    (Sheaf.exists_app_f_eq hS) _ (((Presheaf.cechComplex A).obj S.X₂.obj).d 0 1 a) (by
      rw [Presheaf.cechComplex_map_f_d_apply]
      exact Presheaf.cechComplex_d_zero_restrict A _ s _ ha)
  obtain ⟨b, hb⟩ := (Presheaf.exactAt_cechComplex_iff A _ 0).1 hA e
    (Presheaf.cechComplex_map_f_injective A _ (Sheaf.injective_app_f hS) _ (by
      rw [Presheaf.cechComplex_map_f_d_apply, he, map_zero,
        Presheaf.cechComplex_d_d_apply]))
  -- Subtract the coboundary correction to obtain compatible local lifts.
  have hda : ((Presheaf.cechComplex A).obj S.X₂.obj).d 0 1
      (a - ((Presheaf.cechComplex A).map S.f.hom).f 0 b) = 0 := by
    rw [map_sub, ← Presheaf.cechComplex_map_f_d_apply, hb, he, sub_self]
  have hcov' : Sieve.ofArrows
      (fun z : Fin 1 → K ↦ (Presheaf.cechNerveObj A z).left)
      (fun z ↦ (Presheaf.cechNerveObj A z).hom) ∈ X.smallEtaleTopology U := by
    refine X.smallEtaleTopology.superset_covering (fun Y g hg ↦ ?_) (hcover K W g hCov)
    obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    refine (Sieve.mem_ofArrows_iff _ _ _).2
      ⟨fun _ ↦ i, h ≫ (Pi.lift fun _ ↦ 𝟙 (A i)).left, ?_⟩
    rw [Category.assoc, Over.w]
    rfl
  obtain ⟨σ, hσ, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (Sheaf.isSheafFor_ofArrows S.X₂ _ hcov')
    (fun z ↦ (a - ((Presheaf.cechComplex A).map S.f.hom).f 0 b) z)
    fun z z' Z g₁ g₂ hg ↦
      Presheaf.map_eq_of_cechComplex_d_zero A _ _ hda z z' g₁ g₂ hg
  refine ⟨σ, (Sheaf.isSheafFor_ofArrows S.X₃ _ hcov').isSeparatedFor.ext
    fun Y f ⟨z⟩ ↦ ?_⟩
  change S.X₃.obj.map _ (S.g.hom.app _ σ) = S.X₃.obj.map _ s
  rw [← NatTrans.naturality_apply]
  erw [hσ z]
  rw [Presheaf.cechComplex_sub_apply, map_sub, Presheaf.cechComplex_map_f_apply,
    Sheaf.app_g_app_f, sub_zero, ← ha]
  rfl

end AlgebraicGeometry.Scheme
