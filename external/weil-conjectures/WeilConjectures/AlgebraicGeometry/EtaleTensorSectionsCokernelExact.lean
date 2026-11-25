/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality

/-! # Local kernel-image comparison for tensor sections

Source: Stacks Project, Tags 070S(2) and 03FH(1).
(blueprint: lem-sc-etale-tensor-sections-cokernel-exact)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj

private theorem sheafify_exact_of_local_lifts {X : Scheme.{u}}
    {P Q R : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (a : P ⟶ Q) (b : Q ⟶ R) (hab : a ≫ b = 0)
    (hl : ∀ (U : X.Etale) (s : Q.obj (op U)), b.app (op U) s = 0 →
      Presheaf.imageSieve a s ∈ X.smallEtaleTopology U) :
    ((ShortComplex.mk a b hab).map
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})).Exact := by
  let l := kernel.lift b a hab
  have hlocal : Presheaf.IsLocallySurjective X.smallEtaleTopology l := by
    constructor
    intro U s
    have hs : b.app (op U) ((kernel.ι b).app (op U) s) = 0 := by
      exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.app (op U))
        (kernel.condition b)) s
    apply X.smallEtaleTopology.superset_covering _ (hl U _ hs)
    intro V f hf
    obtain ⟨t, ht⟩ := hf
    refine ⟨t, ?_⟩
    have hinj : Function.Injective ((kernel.ι b).app (op V)) :=
      (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    apply hinj
    have hfac := congrArg (fun f ↦ f.app (op V)) (kernel.lift_ι b a hab)
    exact (ConcreteCategory.congr_hom hfac t).trans
      (ht.trans (NatTrans.naturality_apply (kernel.ι b) f.op s).symm)
  let A := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : Sheaf.IsLocallySurjective (A.map l) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff X.smallEtaleTopology l).2 hlocal
  have : Epi (A.map l) := Sheaf.epi_of_isLocallySurjective _
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  have he : A.map l ≫ kernelComparison b A =
      kernel.lift (A.map b) (A.map a) ((ShortComplex.mk a b hab).map A).zero :=
    map_lift_kernelComparison b A hab
  change Epi (kernel.lift (A.map b) (A.map a) _)
  rw [← he]
  infer_instance

private theorem openSection_naturality {A : Scheme.{u}} (W : A.Opens)
    {M N : A.Modules} (f : M ⟶ N) :
    ((tensorPullback W.ι).map f).app ⊤ ≫ (tensorOpenSectionIso A N W).hom =
      (tensorOpenSectionIso A M W).hom ≫ f.app W := by
  let e := (Classical.choose (exists_tensorPullbackAdjunction W.ι)).leftAdjointUniq
    (restrictAdjunction W.ι)
  have hn := congrArg (fun k ↦ k.app ⊤) (e.hom.naturality f)
  change ((tensorPullback W.ι).map f).app ⊤ ≫ (e.hom.app N).app ⊤ =
    (e.hom.app M).app ⊤ ≫ f.app (W.ι ''ᵁ ⊤) at hn
  have hr := f.mapPresheaf.naturality (eqToHom W.ι_image_top.symm).op
  change M.presheaf.map (eqToHom W.ι_image_top.symm).op ≫ f.app W =
    f.app (W.ι ''ᵁ ⊤) ≫ N.presheaf.map (eqToHom W.ι_image_top.symm).op at hr
  change ((tensorPullback W.ι).map f).app ⊤ ≫
      ((e.hom.app N).app ⊤ ≫ N.presheaf.map (eqToHom W.ι_image_top.symm).op) =
    ((e.hom.app M).app ⊤ ≫ M.presheaf.map (eqToHom W.ι_image_top.symm).op) ≫ f.app W
  rw [← Category.assoc, hn, Category.assoc, ← hr, ← Category.assoc]

private theorem openSection_unit {A : Scheme.{u}} (W : A.Opens) (M : A.Modules) :
    tensorSectionsUnit W.ι M ≫ (tensorOpenSectionIso A M W).hom =
      M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op := by
  let e := (Classical.choose (exists_tensorPullbackAdjunction W.ι)).leftAdjointUniq
    (restrictAdjunction W.ι)
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Classical.choose (exists_tensorPullbackAdjunction W.ι)) (restrictAdjunction W.ι) M
  have hs := congrArg (fun k ↦ k.app ⊤) hu
  change ((Classical.choose (exists_tensorPullbackAdjunction W.ι)).unit.app M).app ⊤ ≫
    (e.hom.app M).app ⊤ = ((restrictAdjunction W.ι).unit.app M).app ⊤ at hs
  have hi : (homOfLE W.ι.preimage_top.ge).op =
      𝟙 (op (⊤ : Opens W.toScheme)) := rfl
  unfold tensorSectionsUnit
  erw [hi, ((tensorPullback W.ι).obj M).presheaf.map_id, Category.comp_id]
  change ((Classical.choose (exists_tensorPullbackAdjunction W.ι)).unit.app M).app ⊤ ≫
    ((e.hom.app M).app ⊤ ≫ M.presheaf.map (eqToHom W.ι_image_top.symm).op) = _
  rw [← Category.assoc, hs, restrictAdjunction_unit_app_app, ← M.presheaf.map_comp]
  congr 1

private def openEtaleObj {X : Scheme.{u}} (U : X.Etale) (W : U.left.Opens) :
    X.Etale := .mk (W.ι ≫ U.hom)

private def openEtaleArrow {X : Scheme.{u}} (U : X.Etale) (W : U.left.Opens) :
    openEtaleObj U W ⟶ U := MorphismProperty.Over.homMk W.ι

private def overOpenIso {X : Scheme.{u}} (U : X.Etale) (W : U.left.Opens)
    (F : X.Modules) :
    (etaleTensorSectionsPresheaf F).obj (op (openEtaleObj U W)) ≅
      Γ((tensorPullback U.hom).obj F, W) :=
  ((CategoryTheory.evaluation _ AddCommGrpCat).obj (op ⊤)).mapIso
    ((toPresheaf W.toScheme).mapIso ((tensorSectionsComp W.ι U.hom).symm.app F)) ≪≫
      tensorOpenSectionIso U.left ((tensorPullback U.hom).obj F) W

private theorem overOpenIso_naturality {X : Scheme.{u}} (U : X.Etale)
    (W : U.left.Opens) {F G : X.Modules} (φ : F ⟶ G) :
    ((tensorPullback (openEtaleObj U W).hom).map φ).app ⊤ ≫
        (overOpenIso U W G).hom =
      (overOpenIso U W F).hom ≫ ((tensorPullback U.hom).map φ).app W := by
  have hc := congrArg (fun ψ ↦ ψ.app ⊤)
    ((tensorSectionsComp W.ι U.hom).inv.naturality φ)
  change ((tensorPullback (W.ι ≫ U.hom)).map φ).app ⊤ ≫
      ((tensorSectionsComp W.ι U.hom).inv.app G).app ⊤ =
    ((tensorSectionsComp W.ι U.hom).inv.app F).app ⊤ ≫
      ((tensorPullback W.ι).map ((tensorPullback U.hom).map φ)).app ⊤ at hc
  change ((tensorPullback (W.ι ≫ U.hom)).map φ).app ⊤ ≫
      (((tensorSectionsComp W.ι U.hom).inv.app G).app ⊤ ≫
        (tensorOpenSectionIso U.left ((tensorPullback U.hom).obj G) W).hom) =
    (((tensorSectionsComp W.ι U.hom).inv.app F).app ⊤ ≫
      (tensorOpenSectionIso U.left ((tensorPullback U.hom).obj F) W).hom) ≫ _
  rw [← Category.assoc, hc, Category.assoc, openSection_naturality, ← Category.assoc]

private theorem overOpenIso_restriction {X : Scheme.{u}} (U : X.Etale)
    (W : U.left.Opens) (F : X.Modules) :
    (etaleTensorSectionsPresheaf F).map (openEtaleArrow U W).op ≫
        (overOpenIso U W F).hom =
      ((tensorPullback U.hom).obj F).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op := by
  change (tensorSectionsUnit W.ι ((tensorPullback U.hom).obj F) ≫
      ((tensorSectionsComp W.ι U.hom).hom.app F).app ⊤ ≫
        (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) (show W.ι ≫ U.hom =
          W.ι ≫ U.hom from rfl))).app ⊤) ≫
    (((tensorSectionsComp W.ι U.hom).inv.app F).app ⊤ ≫
      (tensorOpenSectionIso U.left ((tensorPullback U.hom).obj F) W).hom) = _
  simp only [eqToHom_refl, Hom.id_app, Category.comp_id, Category.assoc]
  have hc := congrArg (fun k ↦ k.app ⊤)
    ((tensorSectionsComp W.ι U.hom).hom_inv_id_app F)
  change ((tensorSectionsComp W.ι U.hom).hom.app F).app ⊤ ≫
    ((tensorSectionsComp W.ι U.hom).inv.app F).app ⊤ = 𝟙 _ at hc
  rw [← Category.assoc (((tensorSectionsComp W.ι U.hom).hom.app F).app ⊤)
    (((tensorSectionsComp W.ι U.hom).inv.app F).app ⊤), hc, Category.id_comp]
  exact openSection_unit W ((tensorPullback U.hom).obj F)

private theorem tensorSections_local_image {X : Scheme.{u}} {F G : X.Modules}
    (φ : F ⟶ G)
    (α : etaleTensorSectionsPresheaf F ⟶ etaleTensorSectionsPresheaf G)
    (β : etaleTensorSectionsPresheaf G ⟶ etaleTensorSectionsPresheaf (cokernel φ))
    (hα : ∀ U : X.Etaleᵒᵖ, α.app U = ((tensorPullback U.unop.hom).map φ).app ⊤)
    (hβ : ∀ U : X.Etaleᵒᵖ,
      β.app U = ((tensorPullback U.unop.hom).map (cokernel.π φ)).app ⊤)
    (U : X.Etale) (s : (etaleTensorSectionsPresheaf G).obj (op U))
    (hs : β.app (op U) s = 0) :
    Presheaf.imageSieve α s ∈ X.smallEtaleTopology U := by
  classical
  let T := tensorPullback U.hom
  have : T.IsLeftAdjoint :=
    (Classical.choose (exists_tensorPullbackAdjunction U.hom)).isLeftAdjoint
  have : T.Additive :=
    (Classical.choose (exists_tensorPullbackAdjunction U.hom)).left_adjoint_additive
  let S := ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)
  have he : (S.map T).Exact :=
    (ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel φ)).map_of_epi_of_preservesCokernel
      T inferInstance inferInstance
  have hs' : (T.map (cokernel.π φ)).val.app (op ⊤) s = 0 := by
    change ((tensorPullback U.hom).map (cokernel.π φ)).app ⊤ s = 0
    rw [← hβ (op U)]
    exact hs
  obtain ⟨I, V, hV, t, hcover, ht⟩ :=
    ((RingedSpace.module_exactness_local_lifting U.left.toRingedSpace).2.2
      (T.obj F) (T.obj G) (T.obj (cokernel φ)) (T.map φ)
        (T.map (cokernel.π φ)) (S.map T).zero).mp he ⊤ s hs'
  apply X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows
    (fun i ↦ openEtaleObj U (V i)) (fun i ↦ openEtaleArrow U (V i)))
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    intro A f hf
    obtain ⟨i⟩ := hf
    refine ⟨(overOpenIso U (V i) F).inv (t i), ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (overOpenIso U (V i) G).hom).injective
    have hn := ConcreteCategory.congr_hom (overOpenIso_naturality U (V i) φ)
      ((overOpenIso U (V i) F).inv (t i))
    have hr := ConcreteCategory.congr_hom (overOpenIso_restriction U (V i) G) s
    rw [hα]
    change (overOpenIso U (V i) G).hom
        (((tensorPullback (openEtaleObj U (V i)).hom).map φ).app ⊤
          ((overOpenIso U (V i) F).inv (t i))) =
      (overOpenIso U (V i) G).hom
        ((etaleTensorSectionsPresheaf G).map (openEtaleArrow U (V i)).op s)
    simp only [ConcreteCategory.comp_apply] at hn hr
    have hi := ConcreteCategory.congr_hom (overOpenIso U (V i) F).inv_hom_id (t i)
    change (overOpenIso U (V i) F).hom ((overOpenIso U (V i) F).inv (t i)) = t i at hi
    exact hn.trans ((congrArg (((tensorPullback U.hom).map φ).app (V i)) hi).trans
      ((ht i).trans hr.symm))
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).2
    change (⋃ i, Set.range (Scheme.Opens.ι (X := U.left) (V i))) = Set.univ
    simp only [Scheme.Opens.range_ι]
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    apply Opens.mem_iSup.mp
    rw [hcover]
    trivial

private theorem imageSieve_ulift {X : Scheme.{u}}
    {P Q : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} (a : P ⟶ Q) {U : X.Etale}
    (s : (Q ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (op U)) :
    Presheaf.imageSieve (Functor.whiskerRight a AddCommGrpCat.uliftFunctor.{u + 1, u}) s =
      Presheaf.imageSieve a s.down := by
  ext V f
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.down, congrArg ULift.down ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨ULift.up t, congrArg ULift.up ht⟩

/-- The sheafified tensor-section sequence of a module cokernel is exact in the middle.
Source: Stacks Project, Descent, Tag 070S(2), and Tag 03FH(1).
(blueprint: lem-sc-etale-tensor-sections-cokernel-exact)

Proof: For an etale object U, tensor pullback carries the module cokernel of phi
to the cokernel of its pullback because it is a left adjoint. The module cokernel
is the sheafification of the sectionwise quotient. Therefore a section of the
pullback of G whose image vanishes in the pullback cokernel locally comes from
the pullback of F, on a Zariski covering of U. Open immersions in this covering
are etale over X; their tensor-section restrictions are the usual restrictions
under the unit-normalized open pullback comparison. Hence the kernel presheaf
of beta is locally the image of alpha. Conversely every image section is in
the kernel since phi composed with its cokernel projection is zero. After
universe lift this local kernel-image equality persists. Sheafification is
exact for abelian presheaves: the image sheaf is the sheafification of the
sectionwise image, and the kernel is the sheafification of the sectionwise
kernel. Local equality gives equality of these sheaves, which is the asserted
exactness. This asserts only middle exactness, not surjectivity onto the last
term; local lifting of arbitrary cokernel sections is a separate assertion.
For the empty scheme or zero morphism the same argument applies. -/
theorem etaleTensorSections_cokernel_exact {X : Scheme.{u}} {F G : X.Modules}
    (φ : F ⟶ G)
    (α : etaleTensorSectionsPresheaf F ⟶ etaleTensorSectionsPresheaf G)
    (β : etaleTensorSectionsPresheaf G ⟶ etaleTensorSectionsPresheaf (cokernel φ))
    (hα : ∀ U : X.Etaleᵒᵖ, α.app U = ((tensorPullback U.unop.hom).map φ).app ⊤)
    (hβ : ∀ U : X.Etaleᵒᵖ,
      β.app U = ((tensorPullback U.unop.hom).map (cokernel.π φ)).app ⊤)
    (w : ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (Functor.whiskerRight α AddCommGrpCat.uliftFunctor.{u + 1, u})) ≫
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (Functor.whiskerRight β AddCommGrpCat.uliftFunctor.{u + 1, u})) = 0) :
    (ShortComplex.mk
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (Functor.whiskerRight α AddCommGrpCat.uliftFunctor.{u + 1, u}))
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (Functor.whiskerRight β AddCommGrpCat.uliftFunctor.{u + 1, u})) w).Exact := by
  classical
  have hzero : α ≫ β = 0 := by
    apply NatTrans.ext
    funext U
    have : (tensorPullback U.unop.hom).Additive :=
      (Classical.choose (exists_tensorPullbackAdjunction U.unop.hom)).left_adjoint_additive
    change α.app U ≫ β.app U = 0
    rw [hα, hβ, ← Hom.comp_app, ← Functor.map_comp, cokernel.condition,
      Functor.map_zero, Hom.zero_app]
  let a := Functor.whiskerRight α AddCommGrpCat.uliftFunctor.{u + 1, u}
  let b := Functor.whiskerRight β AddCommGrpCat.uliftFunctor.{u + 1, u}
  have hab : a ≫ b = 0 := by
    apply NatTrans.ext
    funext U
    change AddCommGrpCat.uliftFunctor.map (α.app U) ≫
      AddCommGrpCat.uliftFunctor.map (β.app U) = 0
    rw [← Functor.map_comp]
    have hz : α.app U ≫ β.app U = 0 := congrArg (fun f ↦ f.app U) hzero
    rw [hz, Functor.map_zero]
  apply sheafify_exact_of_local_lifts a b hab
  intro U s hs
  have hs' : β.app (op U) s.down = 0 := congrArg ULift.down hs
  have hi : Presheaf.imageSieve a s = Presheaf.imageSieve α s.down := imageSieve_ulift α s
  rw [hi]
  exact tensorSections_local_image φ α β hα hβ U s.down hs'

end
end AlgebraicGeometry.Scheme.Modules
