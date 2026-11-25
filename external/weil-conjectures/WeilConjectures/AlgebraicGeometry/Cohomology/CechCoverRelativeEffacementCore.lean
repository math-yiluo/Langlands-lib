/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.Topology.Sheaves.CechCohomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products

/-! # Cover effacement before inverse image

Source: `lem-pc-cech-cover-relative-effacement`, product and contraction paragraphs.
The construction is an expansion of that node's argument, given here;
Stacks Project, Tags 01EQ and 01FD, supply its comparison context.
(blueprint: lem-pc-cech-cover-relative-effacement-core)
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The restriction adjunction for an open inclusion, transported to naive restriction.
Source: Mathlib `sheafPullbackIso` and `pullbackPushforwardAdjunction`.
(blueprint: lem-pc-cech-cover-relative-effacement-core) -/
private noncomputable def coverRestrictionAdjunction {X : Scheme.{u}} (W : X.Opens) :
    W.sheafRestrict ⊣ TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' W) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (Opens.inclusion' W)).ofNatIsoLeft (W.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u})

/-- The product of the direct images of the restrictions of a sheaf to cover members.
Source: the product paragraph of `lem-pc-cech-cover-relative-effacement`.
(blueprint: lem-pc-cech-cover-relative-effacement-core) -/
private noncomputable def cechCoverProduct {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ∏ᶜ fun i ↦ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' (U i))).obj
    ((U i).sheafRestrict.obj F)

/-- The map whose components are the restriction-adjunction units.
Source: the product paragraph of `lem-pc-cech-cover-relative-effacement`.
(blueprint: lem-pc-cech-cover-relative-effacement-core) -/
private noncomputable def cechCoverProductMap {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : F ⟶ cechCoverProduct U F :=
  Pi.lift fun i ↦ (coverRestrictionAdjunction (U i)).unit.app F

/-- Projection and the restriction counit retract the cover-product map on each member.
Source: the triangle identity for the restriction adjunction.
(blueprint: lem-pc-cech-cover-relative-effacement-core) -/
private theorem cechCoverProductMap_localSplit {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (i : ι) : IsSplitMono ((U i).sheafRestrict.map (cechCoverProductMap U F)) := by
  let A := coverRestrictionAdjunction (U i)
  refine IsSplitMono.mk' ⟨(U i).sheafRestrict.map (Pi.π _ i) ≫
    A.counit.app ((U i).sheafRestrict.obj F), ?_⟩
  rw [← Functor.map_comp_assoc]
  change (U i).sheafRestrict.map (Pi.lift _ ≫ Pi.π _ i) ≫ _ = _
  rw [Pi.lift_comp_π]
  exact A.left_triangle_components F

/-- Inserting the factor index contracts its Čech complex. -/
private theorem factor_exact {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (i : ι) (q : ℕ) :
    ((TopCat.Sheaf.cechComplexFunctor U).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' (U i))).obj
        ((U i).sheafRestrict.obj F))).ExactAt (q + 1) := by
  apply TopCat.Presheaf.exactAt_cechComplex_of_bijective U _ (j := i)
  intro k y
  let W := ⨅ l, U (y l)
  have heq : (Opens.map (Opens.inclusion' (U i))).obj (W ⊓ U i) =
      (Opens.map (Opens.inclusion' (U i))).obj W := by
    ext x
    change (x.val ∈ W ∧ x.val ∈ U i) ↔ x.val ∈ W
    exact ⟨And.left, fun hx ↦ ⟨hx, x.property⟩⟩
  have hi : IsIso ((Opens.map (Opens.inclusion' (U i))).map
      (homOfLE (inf_le_left : W ⊓ U i ≤ W))) := by
    rw [Subsingleton.elim
      ((Opens.map (Opens.inclusion' (U i))).map
        (homOfLE (inf_le_left : W ⊓ U i ≤ W))) (eqToHom heq)]
    infer_instance
  change Function.Bijective (((U i).sheafRestrict.obj F).obj.map
    (((Opens.map (Opens.inclusion' (U i))).map
      (homOfLE (inf_le_left : W ⊓ U i ≤ W))).op))
  exact ConcreteCategory.bijective_of_isIso _

/-- Evaluation identifies the sheaf product with the product of its section types. -/
private noncomputable def productSectionsIso {X : Scheme.{u}} {ι : Type u}
    (E : ι → Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (W : X.Opens) :
    ((∏ᶜ E).obj.obj (op W) : Type u) ≅ (∀ i, (E i).obj.obj (op W)) :=
  let K := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation _ _).obj (op W) ⋙
    CategoryTheory.forget AddCommGrpCat.{u}
  PreservesProduct.iso K E ≪≫ Types.productIso (fun i ↦ K.obj (E i))

private theorem productSectionsIso_apply {X : Scheme.{u}} {ι : Type u}
    (E : ι → Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (W : X.Opens)
    (x : (∏ᶜ E).obj.obj (op W)) (i : ι) :
    (productSectionsIso E W).hom x i = (Pi.π E i).hom.app (op W) x := by
  let K := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation _ _).obj (op W) ⋙
    CategoryTheory.forget AddCommGrpCat.{u}
  change (Types.productIso (fun i ↦ K.obj (E i))).hom
    ((PreservesProduct.iso K E).hom x) i = _
  have ht := ConcreteCategory.congr_hom
    (Types.productIso_hom_comp_eval (fun i ↦ K.obj (E i)) i)
    ((PreservesProduct.iso K E).hom x)
  change (Types.productIso (fun i ↦ K.obj (E i))).hom
    ((PreservesProduct.iso K E).hom x) i =
    (Pi.π (fun i ↦ K.obj (E i)) i) ((PreservesProduct.iso K E).hom x) at ht
  rw [ht]
  exact ConcreteCategory.congr_hom (piComparison_comp_π K E i) x

/-- Lift factorwise coboundaries through the sectionwise product isomorphism. -/
private theorem cechCoverProduct_exact {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    ((TopCat.Sheaf.cechComplexFunctor U).obj (cechCoverProduct U F)).ExactAt (q + 1) := by
  classical
  let E (i : ι) : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' (U i))).obj
      ((U i).sheafRestrict.obj F)
  change ((TopCat.Presheaf.cechComplex U).obj (cechCoverProduct U F).obj).ExactAt (q + 1)
  rw [TopCat.Presheaf.exactAt_cechComplex_iff]
  intro c hc
  let p (i : ι) := (TopCat.Presheaf.cechComplex U).map (Pi.π E i).hom
  let ci (i : ι) := (p i).f (q + 1) c
  have hci (i : ι) : ((TopCat.Presheaf.cechComplex U).obj (E i).obj).d
      (q + 1) (q + 2) (ci i) = 0 := by
    have h := ConcreteCategory.congr_hom ((p i).comm (q + 1) (q + 2)) c
    change _ = (p i).f (q + 2)
      (((TopCat.Presheaf.cechComplex U).obj (cechCoverProduct U F).obj).d
        (q + 1) (q + 2) c) at h
    rw [hc, map_zero] at h
    exact h
  choose b hb using fun i ↦
    (TopCat.Presheaf.exactAt_cechComplex_iff U (E i).obj q).mp (factor_exact U F i q)
      (ci i) (hci i)
  let b' : TopCat.Presheaf.CechCochain U (cechCoverProduct U F).obj q :=
    fun y ↦ (productSectionsIso E (⨅ l, U (y l))).inv (fun i ↦ b i y)
  have hbi (i : ι) : (p i).f q b' = b i := by
    funext y
    change (Pi.π E i).hom.app (op (⨅ l, U (y l))) (b' y) = b i y
    rw [← productSectionsIso_apply]
    exact congrFun ((productSectionsIso E (⨅ l, U (y l))).inv_hom_id_apply
      (fun i ↦ b i y)) i
  refine ⟨b', funext fun y ↦ ?_⟩
  apply (productSectionsIso E (⨅ l, U (y l))).toEquiv.injective
  funext i
  simp only [Iso.toEquiv_fun, productSectionsIso_apply]
  have h := ConcreteCategory.congr_hom ((p i).comm q (q + 1)) b'
  change ((TopCat.Presheaf.cechComplex U).obj (E i).obj).d q (q + 1)
    ((p i).f q b') = (p i).f (q + 1)
    (((TopCat.Presheaf.cechComplex U).obj (cechCoverProduct U F).obj).d q (q + 1) b') at h
  rw [hbi, hb] at h
  exact (congrFun h y).symm

/-- Sheaf uniqueness detects a morphism vanishing on every cover member. -/
private theorem hom_eq_zero_of_coverRestriction {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hcover : iSup U = ⊤)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G)
    (h : ∀ i, (U i).sheafRestrict.map f = 0) : f = 0 := by
  have h' (i : ι) (W : X.Opens) (hW : W ≤ U i) : f.hom.app (op W) = 0 := by
    have key : ∀ W' : X.Opens, W' = W → f.hom.app (op W') = 0 →
        f.hom.app (op W) = 0 := by
      rintro _ rfl hw
      exact hw
    refine key _ ?_ (by
      have he := congrArg (fun g ↦ g.hom.app
        (op ((Opens.map (Opens.inclusion' (U i))).obj W))) (h i)
      exact he)
    rw [Opens.functor_map_eq_inf]
    exact inf_eq_left.mpr hW
  ext V x
  change f.hom.app V x = 0
  refine TopCat.Sheaf.eq_of_locally_eq' G (fun i ↦ V.unop ⊓ U i) V.unop
    (fun _ ↦ homOfLE inf_le_left) (fun z hz ↦ ?_) _ 0 fun i ↦ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.ge (Set.mem_univ z))
    exact Opens.mem_iSup.mpr ⟨i, hz, hi⟩
  · rw [map_zero]
    have hn := ConcreteCategory.congr_hom
      (f.hom.naturality (homOfLE (inf_le_left : V.unop ⊓ U i ≤ V.unop)).op) x
    refine hn.symm.trans ?_
    rw [h' i _ inf_le_right]
    rfl

private theorem cechCoverProductMap_mono {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Mono (cechCoverProductMap U F) := by
  refine Preadditive.mono_of_cancel_zero _ fun {Z} g hg ↦ ?_
  refine hom_eq_zero_of_coverRestriction U hcover g fun i ↦ ?_
  have := cechCoverProductMap_localSplit U F i
  rw [← cancel_mono ((U i).sheafRestrict.map (cechCoverProductMap U F)),
    ← Functor.map_comp, hg, Functor.map_zero, zero_comp]

/-- An exact sequence split on an open is surjective on sections of its subopens. -/
private theorem surjective_sections_of_splitRestriction {X : Scheme.{u}}
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact) (W B : X.Opens) (hB : B ≤ W)
    (hsplit : IsSplitMono (W.sheafRestrict.map T.f)) :
    Function.Surjective (T.g.hom.app (op B)) := by
  let A := coverRestrictionAdjunction W
  have : (W.sheafRestrict (C := AddCommGrpCat.{u})).IsLeftAdjoint := A.isLeftAdjoint
  have : PreservesFiniteColimits (W.sheafRestrict (C := AddCommGrpCat.{u})) := inferInstance
  have := hsplit
  let TW := T.map W.sheafRestrict
  have hTW : TW.ShortExact := hT.map_of_exact W.sheafRestrict
  let sp := ShortComplex.Splitting.ofExactOfRetraction TW hTW.exact
    (retraction (W.sheafRestrict.map T.f)) (IsSplitMono.id (W.sheafRestrict.map T.f))
    hTW.epi_g
  have : IsSplitEpi (W.sheafRestrict.map T.g) := sp.isSplitEpi_g
  let V := (Opens.map (Opens.inclusion' W)).obj B
  have : IsSplitEpi ((W.sheafRestrict.map T.g).hom.app (op V)) :=
    inferInstanceAs (IsSplitEpi ((sheafToPresheaf _ _ ⋙
      (CategoryTheory.evaluation _ _).obj (op V)).map (W.sheafRestrict.map T.g)))
  have he := (AddCommGrpCat.epi_iff_surjective
    ((W.sheafRestrict.map T.g).hom.app (op V))).mp inferInstance
  change Function.Surjective (T.g.hom.app (op (W.isOpenEmbedding.functor.obj V))) at he
  dsimp [V] at he
  rw [Opens.functor_map_eq_inf, inf_eq_left.mpr hB] at he
  exact he

/-- Core cover effacement: the quotient is sectionwise surjective and locally split,
with surjective Čech connecting maps. The inverse-image clause is derived separately.
Source: `lem-pc-cech-cover-relative-effacement`, product and contraction paragraphs
(explicit expansion in the context of Stacks Project, Tags 01EQ and 01FD).
(blueprint: lem-pc-cech-cover-relative-effacement-core)

Proof: For j_i : U_i → X put E_i = (j_i)_*(F|U_i), E = ∏_i E_i, and let
f : F → E have components the restriction-adjunction units. On each U_i,
projection to E_i followed by the restriction-adjunction counit retracts f,
by the triangle identity. A section killed by f vanishes on every U_i;
the sheaf uniqueness axiom and the covering hypothesis make f monic. Take
Q = cokernel f and the cokernel short exact sequence T, with T.X₁ = F.
Restriction is exact, so its monic first arrow with the displayed retraction
splits the restricted sequence. Restricting its quotient section further to
any tuple intersection gives hg, since that intersection lies in its first member.
On an intersection W, E_i(W) = F(W ∩ U_i). In the Čech complex of E_i,
define h in positive degree by inserting i at the front of the tuple. The
intersection is unchanged by that insertion because U_i is already present
in the coefficient restriction. In dh + hd, the face deleting the inserted i
is the identity; all other faces cancel in pairs with opposite signs. Thus
positive-degree cocycles are boundaries. Products of these contractions give
the same identity for E, since products of sheaves are computed sectionwise.
Hence the positive Čech cohomology of E vanishes. The tuplewise exact sequence
of cochain groups is short exact (hg makes the product quotient map surjective).
Its long exact homology sequence says the image of each connecting map is the
kernel of the map into the zero positive cohomology group of E, giving hδ.
If the index type is empty, the covering hypothesis makes X empty, all sheaves
are zero, the same cokernel construction is exact, and all Čech groups vanish. -/
theorem exists_cechCoverRelativeEffacement_core
    {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ∃ (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})),
      T.X₁ = F ∧ ∃ (hT : T.ShortExact)
        (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
          Function.Surjective (T.g.hom.app (op (⨅ l, U (y l))))),
        (∀ i, IsSplitMono ((U i).sheafRestrict.map T.f)) ∧
        ∀ q, Function.Surjective (TopCat.Sheaf.cechδ U hT hg q) := by
  classical
  have : Mono (cechCoverProductMap U F) := cechCoverProductMap_mono U hcover F
  let T := ShortComplex.cokernelSequence (cechCoverProductMap U F)
  have : Mono T.f := inferInstanceAs (Mono (cechCoverProductMap U F))
  have hT : T.ShortExact := ⟨ShortComplex.cokernelSequence_exact _⟩
  have hs : ∀ i, IsSplitMono ((U i).sheafRestrict.map T.f) :=
    cechCoverProductMap_localSplit U F
  have hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (T.g.hom.app (op (⨅ l, U (y l)))) := fun k y ↦
    surjective_sections_of_splitRestriction T hT (U (y 0)) (⨅ l, U (y l))
      (iInf_le _ 0) (hs (y 0))
  refine ⟨T, rfl, hT, hg, hs, fun q ↦ ?_⟩
  have h := (TopCat.Sheaf.shortExact_cechComplex hT hg).homology_exact₁ q (q + 1) rfl
  have hz : IsZero ((T.map (TopCat.Sheaf.cechComplexFunctor U)).X₂.homology (q + 1)) :=
    (cechCoverProduct_exact U F q).isZero_homology
  have := h.epi_f (hz.eq_of_tgt _ _)
  exact (AddCommGrpCat.epi_iff_surjective _).mp this

end AlgebraicGeometry.Scheme.Modules
